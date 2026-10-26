import V185TrunkScan22Chunk171

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1535509 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 6]
def baseStart_1535509 : Nat := 118140960795 + 1535509 * 2 ^ 59
def prefixEnd_1535509 : Nat := 4983230072969 + 3 ^ 40 * 1535509 * 2
def baseEnd_1535509 : Nat := 175212036956608455039073

theorem tailTrace_1535509 : CollatzResearch.WordTrace tailWord_1535509 prefixEnd_1535509 175212036956608455039073 := by
  unfold tailWord_1535509
  simp only [CollatzResearch.WordTrace]
  refine ⟨56004614194120611903993581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37336409462747074602662387 56004614194120611903993581)
  ·
    refine ⟨21001730322795229463997593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56004614194120611903993581 21001730322795229463997593)
    ·
      refine ⟨15751297742096422097998195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21001730322795229463997593 15751297742096422097998195)
      ·
        refine ⟨23626946613144633146997293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15751297742096422097998195 23626946613144633146997293)
        ·
          refine ⟨8860104979929237430123985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23626946613144633146997293 8860104979929237430123985)
          ·
            refine ⟨6645078734946928072592989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8860104979929237430123985 6645078734946928072592989)
            ·
              refine ⟨2491904525605098027222371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6645078734946928072592989 2491904525605098027222371)
              ·
                refine ⟨3737856788407647040833557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2491904525605098027222371 3737856788407647040833557)
                ·
                  refine ⟨175212036956608455039073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3737856788407647040833557 175212036956608455039073)
                  ·
                    rfl

theorem cell22_1535509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 6].length) (baseStart_1535509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535509 prefixEnd_1535509 := by exact prefixLift 1535509
  have htrace : WordTrace (prefixWord ++ tailWord_1535509) baseStart_1535509 baseEnd_1535509 := by
    simpa [prefixWord, tailWord_1535509, baseEnd_1535509] using wordTrace_append hprefix tailTrace_1535509
  have hstable : (prefixWord ++ tailWord_1535509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535509).length < 2 ^ (prefixWord ++ tailWord_1535509).sum := by decide
  have hdescent : baseEnd_1535509 < baseStart_1535509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535539 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 2, 4]
def baseStart_1535539 : Nat := 118140960795 + 1535539 * 2 ^ 59
def prefixEnd_1535539 : Nat := 4983230072969 + 3 ^ 40 * 1535539 * 2
def baseEnd_1535539 : Nat := 525646380482915286867127

theorem tailTrace_1535539 : CollatzResearch.WordTrace tailWord_1535539 prefixEnd_1535539 525646380482915286867127 := by
  unfold tailWord_1535539
  simp only [CollatzResearch.WordTrace]
  refine ⟨56005708384011927027585671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37337138922674618018390447 56005708384011927027585671)
  ·
    refine ⟨84008562576017890541378507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56005708384011927027585671 84008562576017890541378507)
    ·
      refine ⟨126012843864026835812067761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84008562576017890541378507 126012843864026835812067761)
      ·
        refine ⟨94509632898020126859050821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126012843864026835812067761 94509632898020126859050821)
        ·
          refine ⟨17720556168378773786072029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94509632898020126859050821 17720556168378773786072029)
          ·
            refine ⟨6645208563142040169777011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17720556168378773786072029 6645208563142040169777011)
            ·
              refine ⟨9967812844713060254665517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6645208563142040169777011 9967812844713060254665517)
              ·
                refine ⟨3737929816767397595499569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9967812844713060254665517 3737929816767397595499569)
                ·
                  refine ⟨2803447362575548196624677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3737929816767397595499569 2803447362575548196624677)
                  ·
                    refine ⟨525646380482915286867127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2803447362575548196624677 525646380482915286867127)
                    ·
                      rfl

theorem cell22_1535539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 2, 4].length) (baseStart_1535539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535539 prefixEnd_1535539 := by exact prefixLift 1535539
  have htrace : WordTrace (prefixWord ++ tailWord_1535539) baseStart_1535539 baseEnd_1535539 := by
    simpa [prefixWord, tailWord_1535539, baseEnd_1535539] using wordTrace_append hprefix tailTrace_1535539
  have hstable : (prefixWord ++ tailWord_1535539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535539).length < 2 ^ (prefixWord ++ tailWord_1535539).sum := by decide
  have hdescent : baseEnd_1535539 < baseStart_1535539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535678 : List Nat := [4, 2, 1, 1, 2, 4, 1, 1, 6]
def baseStart_1535678 : Nat := 118140960795 + 1535678 * 2 ^ 59
def prefixEnd_1535678 : Nat := 4983230072969 + 3 ^ 40 * 1535678 * 2
def baseEnd_1535678 : Nat := 175231321007855085880567

theorem tailTrace_1535678 : CollatzResearch.WordTrace tailWord_1535678 prefixEnd_1535678 175231321007855085880567 := by
  unfold tailWord_1535678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7001347266313544220861961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37340518753672235844597125 7001347266313544220861961)
  ·
    refine ⟨5251010449735158165646471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7001347266313544220861961 5251010449735158165646471)
    ·
      refine ⟨7876515674602737248469707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5251010449735158165646471 7876515674602737248469707)
      ·
        refine ⟨11814773511904105872704561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7876515674602737248469707 11814773511904105872704561)
        ·
          refine ⟨8861080133928079404528421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11814773511904105872704561 8861080133928079404528421)
          ·
            refine ⟨1661452525111514888349079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8861080133928079404528421 1661452525111514888349079)
            ·
              refine ⟨2492178787667272332523619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1661452525111514888349079 2492178787667272332523619)
              ·
                refine ⟨3738268181500908498785429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2492178787667272332523619 3738268181500908498785429)
                ·
                  refine ⟨175231321007855085880567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3738268181500908498785429 175231321007855085880567)
                  ·
                    rfl

theorem cell22_1535678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_1535678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535678 prefixEnd_1535678 := by exact prefixLift 1535678
  have htrace : WordTrace (prefixWord ++ tailWord_1535678) baseStart_1535678 baseEnd_1535678 := by
    simpa [prefixWord, tailWord_1535678, baseEnd_1535678] using wordTrace_append hprefix tailTrace_1535678
  have hstable : (prefixWord ++ tailWord_1535678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535678).length < 2 ^ (prefixWord ++ tailWord_1535678).sum := by decide
  have hdescent : baseEnd_1535678 < baseStart_1535678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535916 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 1, 10]
def baseStart_1535916 : Nat := 118140960795 + 1535916 * 2 ^ 59
def prefixEnd_1535916 : Nat := 4983230072969 + 3 ^ 40 * 1535916 * 2
def baseEnd_1535916 : Nat := 525775435287411970190971

theorem tailTrace_1535916 : CollatzResearch.WordTrace tailWord_1535916 prefixEnd_1535916 525775435287411970190971 := by
  unfold tailWord_1535916
  simp only [CollatzResearch.WordTrace]
  refine ⟨28009729351823060207029801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37346305802430746942706401 28009729351823060207029801)
  ·
    refine ⟨21007297013867295155272351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28009729351823060207029801 21007297013867295155272351)
    ·
      refine ⟨31510945520800942732908527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21007297013867295155272351 31510945520800942732908527)
      ·
        refine ⟨47266418281201414099362791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31510945520800942732908527 47266418281201414099362791)
        ·
          refine ⟨70899627421802121149044187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47266418281201414099362791 70899627421802121149044187)
          ·
            refine ⟨106349441132703181723566281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 70899627421802121149044187 106349441132703181723566281)
            ·
              refine ⟨79762080849527386292674711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106349441132703181723566281 79762080849527386292674711)
              ·
                refine ⟨119643121274291079439012067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 79762080849527386292674711 119643121274291079439012067)
                ·
                  refine ⟨179464681911436619158518101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 119643121274291079439012067 179464681911436619158518101)
                  ·
                    refine ⟨525775435287411970190971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 179464681911436619158518101 525775435287411970190971)
                    ·
                      rfl

theorem cell22_1535916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_1535916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535916 prefixEnd_1535916 := by exact prefixLift 1535916
  have htrace : WordTrace (prefixWord ++ tailWord_1535916) baseStart_1535916 baseEnd_1535916 := by
    simpa [prefixWord, tailWord_1535916, baseEnd_1535916] using wordTrace_append hprefix tailTrace_1535916
  have hstable : (prefixWord ++ tailWord_1535916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535916).length < 2 ^ (prefixWord ++ tailWord_1535916).sum := by decide
  have hdescent : baseEnd_1535916 < baseStart_1535916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535924 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1535924 : Nat := 118140960795 + 1535924 * 2 ^ 59
def prefixEnd_1535924 : Nat := 4983230072969 + 3 ^ 40 * 1535924 * 2
def baseEnd_1535924 : Nat := 525778173850902615990947

theorem tailTrace_1535924 : CollatzResearch.WordTrace tailWord_1535924 prefixEnd_1535924 525778173850902615990947 := by
  unfold tailWord_1535924
  simp only [CollatzResearch.WordTrace]
  refine ⟨28009875243808568890175413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37346500325078091853567217 28009875243808568890175413)
  ·
    refine ⟨2625925804107053333453945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28009875243808568890175413 2625925804107053333453945)
    ·
      refine ⟨1969444353080290000090459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2625925804107053333453945 1969444353080290000090459)
      ·
        refine ⟨2954166529620435000135689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1969444353080290000090459 2954166529620435000135689)
        ·
          refine ⟨2215624897215326250101767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2954166529620435000135689 2215624897215326250101767)
          ·
            refine ⟨3323437345822989375152651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2215624897215326250101767 3323437345822989375152651)
            ·
              refine ⟨4985156018734484062728977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3323437345822989375152651 4985156018734484062728977)
              ·
                refine ⟨3738867014050863047046733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4985156018734484062728977 3738867014050863047046733)
                ·
                  refine ⟨1402075130269073642642525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3738867014050863047046733 1402075130269073642642525)
                  ·
                    refine ⟨525778173850902615990947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1402075130269073642642525 525778173850902615990947)
                    ·
                      rfl

theorem cell22_1535924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1535924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535924 prefixEnd_1535924 := by exact prefixLift 1535924
  have htrace : WordTrace (prefixWord ++ tailWord_1535924) baseStart_1535924 baseEnd_1535924 := by
    simpa [prefixWord, tailWord_1535924, baseEnd_1535924] using wordTrace_append hprefix tailTrace_1535924
  have hstable : (prefixWord ++ tailWord_1535924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535924).length < 2 ^ (prefixWord ++ tailWord_1535924).sum := by decide
  have hdescent : baseEnd_1535924 < baseStart_1535924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535931 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 8]
def baseStart_1535931 : Nat := 118140960795 + 1535931 * 2 ^ 59
def prefixEnd_1535931 : Nat := 4983230072969 + 3 ^ 40 * 1535931 * 2
def baseEnd_1535931 : Nat := 175260190031318977021975

theorem tailTrace_1535931 : CollatzResearch.WordTrace tailWord_1535931 prefixEnd_1535931 175260190031318977021975 := by
  unfold tailWord_1535931
  simp only [CollatzResearch.WordTrace]
  refine ⟨56020005798591777975855647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37346670532394518650570431 56020005798591777975855647)
  ·
    refine ⟨84030008697887666963783471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56020005798591777975855647 84030008697887666963783471)
    ·
      refine ⟨126045013046831500445675207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84030008697887666963783471 126045013046831500445675207)
      ·
        refine ⟨189067519570247250668512811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126045013046831500445675207 189067519570247250668512811)
        ·
          refine ⟨283601279355370876002769217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189067519570247250668512811 283601279355370876002769217)
          ·
            refine ⟨212700959516528157002076913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 283601279355370876002769217 212700959516528157002076913)
            ·
              refine ⟨159525719637396117751557685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 212700959516528157002076913 159525719637396117751557685)
              ·
                refine ⟨14955536216005886039208533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 159525719637396117751557685 14955536216005886039208533)
                ·
                  refine ⟨175260190031318977021975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14955536216005886039208533 175260190031318977021975)
                  ·
                    rfl

theorem cell22_1535931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 8].length) (baseStart_1535931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535931 prefixEnd_1535931 := by exact prefixLift 1535931
  have htrace : WordTrace (prefixWord ++ tailWord_1535931) baseStart_1535931 baseEnd_1535931 := by
    simpa [prefixWord, tailWord_1535931, baseEnd_1535931] using wordTrace_append hprefix tailTrace_1535931
  have hstable : (prefixWord ++ tailWord_1535931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535931).length < 2 ^ (prefixWord ++ tailWord_1535931).sum := by decide
  have hdescent : baseEnd_1535931 < baseStart_1535931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535950 : List Nat := [4, 1, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_1535950 : Nat := 118140960795 + 1535950 * 2 ^ 59
def prefixEnd_1535950 : Nat := 4983230072969 + 3 ^ 40 * 1535950 * 2
def baseEnd_1535950 : Nat := 525787074182247214840867

theorem tailTrace_1535950 : CollatzResearch.WordTrace tailWord_1535950 prefixEnd_1535950 525787074182247214840867 := by
  unfold tailWord_1535950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7002587348190368027599663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37347132523681962813864869 7002587348190368027599663)
  ·
    refine ⟨10503881022285552041399495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7002587348190368027599663 10503881022285552041399495)
    ·
      refine ⟨15755821533428328062099243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10503881022285552041399495 15755821533428328062099243)
      ·
        refine ⟨23633732300142492093148865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15755821533428328062099243 23633732300142492093148865)
        ·
          refine ⟨17725299225106869069861649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23633732300142492093148865 17725299225106869069861649)
          ·
            refine ⟨13293974418830151802396237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17725299225106869069861649 13293974418830151802396237)
            ·
              refine ⟨4985240407061306925898589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13293974418830151802396237 4985240407061306925898589)
              ·
                refine ⟨1869465152647990097211971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4985240407061306925898589 1869465152647990097211971)
                ·
                  refine ⟨2804197728971985145817957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869465152647990097211971 2804197728971985145817957)
                  ·
                    refine ⟨525787074182247214840867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2804197728971985145817957 525787074182247214840867)
                    ·
                      rfl

theorem cell22_1535950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_1535950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535950 prefixEnd_1535950 := by exact prefixLift 1535950
  have htrace : WordTrace (prefixWord ++ tailWord_1535950) baseStart_1535950 baseEnd_1535950 := by
    simpa [prefixWord, tailWord_1535950, baseEnd_1535950] using wordTrace_append hprefix tailTrace_1535950
  have hstable : (prefixWord ++ tailWord_1535950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535950).length < 2 ^ (prefixWord ++ tailWord_1535950).sum := by decide
  have hdescent : baseEnd_1535950 < baseStart_1535950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535954 : List Nat := [3, 2, 2, 3, 3, 1, 1, 2, 5]
def baseStart_1535954 : Nat := 118140960795 + 1535954 * 2 ^ 59
def prefixEnd_1535954 : Nat := 4983230072969 + 3 ^ 40 * 1535954 * 2
def baseEnd_1535954 : Nat := 175262814487997512580285

theorem tailTrace_1535954 : CollatzResearch.WordTrace tailWord_1535954 prefixEnd_1535954 175262814487997512580285 := by
  unfold tailWord_1535954
  simp only [CollatzResearch.WordTrace]
  refine ⟨14005211169377113225985729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37347229785005635269295277 14005211169377113225985729)
  ·
    refine ⟨10503908377032834919489297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14005211169377113225985729 10503908377032834919489297)
    ·
      refine ⟨7877931282774626189616973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10503908377032834919489297 7877931282774626189616973)
      ·
        refine ⟨2954224231040484821106365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7877931282774626189616973 2954224231040484821106365)
        ·
          refine ⟨1107834086640181807914887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2954224231040484821106365 1107834086640181807914887)
          ·
            refine ⟨1661751129960272711872331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1107834086640181807914887 1661751129960272711872331)
            ·
              refine ⟨2492626694940409067808497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1661751129960272711872331 2492626694940409067808497)
              ·
                refine ⟨1869470021205306800856373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2492626694940409067808497 1869470021205306800856373)
                ·
                  refine ⟨175262814487997512580285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1869470021205306800856373 175262814487997512580285)
                  ·
                    rfl

theorem cell22_1535954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_1535954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535954 prefixEnd_1535954 := by exact prefixLift 1535954
  have htrace : WordTrace (prefixWord ++ tailWord_1535954) baseStart_1535954 baseEnd_1535954 := by
    simpa [prefixWord, tailWord_1535954, baseEnd_1535954] using wordTrace_append hprefix tailTrace_1535954
  have hstable : (prefixWord ++ tailWord_1535954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535954).length < 2 ^ (prefixWord ++ tailWord_1535954).sum := by decide
  have hdescent : baseEnd_1535954 < baseStart_1535954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535978 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 3, 6]
def baseStart_1535978 : Nat := 118140960795 + 1535978 * 2 ^ 59
def prefixEnd_1535978 : Nat := 4983230072969 + 3 ^ 40 * 1535978 * 2
def baseEnd_1535978 : Nat := 525796659154464475140781

theorem tailTrace_1535978 : CollatzResearch.WordTrace tailWord_1535978 prefixEnd_1535978 525796659154464475140781 := by
  unfold tailWord_1535978
  simp only [CollatzResearch.WordTrace]
  refine ⟨14005430007355376250704147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37347813352947670001877725 14005430007355376250704147)
  ·
    refine ⟨21008145011033064376056221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14005430007355376250704147 21008145011033064376056221)
    ·
      refine ⟨7878054379137399141021083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21008145011033064376056221 7878054379137399141021083)
      ·
        refine ⟨11817081568706098711531625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7878054379137399141021083 11817081568706098711531625)
        ·
          refine ⟨8862811176529574033648719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11817081568706098711531625 8862811176529574033648719)
          ·
            refine ⟨13294216764794361050473079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8862811176529574033648719 13294216764794361050473079)
            ·
              refine ⟨19941325147191541575709619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13294216764794361050473079 19941325147191541575709619)
              ·
                refine ⟨29911987720787312363564429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19941325147191541575709619 29911987720787312363564429)
                ·
                  refine ⟨11216995395295242136336661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29911987720787312363564429 11216995395295242136336661)
                  ·
                    refine ⟨525796659154464475140781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11216995395295242136336661 525796659154464475140781)
                    ·
                      rfl

theorem cell22_1535978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_1535978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535978 prefixEnd_1535978 := by exact prefixLift 1535978
  have htrace : WordTrace (prefixWord ++ tailWord_1535978) baseStart_1535978 baseEnd_1535978 := by
    simpa [prefixWord, tailWord_1535978, baseEnd_1535978] using wordTrace_append hprefix tailTrace_1535978
  have hstable : (prefixWord ++ tailWord_1535978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535978).length < 2 ^ (prefixWord ++ tailWord_1535978).sum := by decide
  have hdescent : baseEnd_1535978 < baseStart_1535978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535980 : List Nat := [2, 2, 1, 1, 2, 1, 1, 7, 2, 3]
def baseStart_1535980 : Nat := 118140960795 + 1535980 * 2 ^ 59
def prefixEnd_1535980 : Nat := 4983230072969 + 3 ^ 40 * 1535980 * 2
def baseEnd_1535980 : Nat := 525797343795337136590775

theorem tailTrace_1535980 : CollatzResearch.WordTrace tailWord_1535980 prefixEnd_1535980 525797343795337136590775 := by
  unfold tailWord_1535980
  simp only [CollatzResearch.WordTrace]
  refine ⟨28010896487707129672194697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37347861983609506229592929 28010896487707129672194697)
  ·
    refine ⟨21008172365780347254146023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28010896487707129672194697 21008172365780347254146023)
    ·
      refine ⟨31512258548670520881219035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21008172365780347254146023 31512258548670520881219035)
      ·
        refine ⟨47268387823005781321828553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31512258548670520881219035 47268387823005781321828553)
        ·
          refine ⟨35451290867254335991371415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47268387823005781321828553 35451290867254335991371415)
          ·
            refine ⟨53176936300881503987057123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35451290867254335991371415 53176936300881503987057123)
            ·
              refine ⟨79765404451322255980585685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53176936300881503987057123 79765404451322255980585685)
              ·
                refine ⟨1869501666827865374544977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 79765404451322255980585685 1869501666827865374544977)
                ·
                  refine ⟨1402126250120899030908733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1869501666827865374544977 1402126250120899030908733)
                  ·
                    refine ⟨525797343795337136590775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1402126250120899030908733 525797343795337136590775)
                    ·
                      rfl

theorem cell22_1535980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 3].length) (baseStart_1535980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535980 prefixEnd_1535980 := by exact prefixLift 1535980
  have htrace : WordTrace (prefixWord ++ tailWord_1535980) baseStart_1535980 baseEnd_1535980 := by
    simpa [prefixWord, tailWord_1535980, baseEnd_1535980] using wordTrace_append hprefix tailTrace_1535980
  have hstable : (prefixWord ++ tailWord_1535980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535980).length < 2 ^ (prefixWord ++ tailWord_1535980).sum := by decide
  have hdescent : baseEnd_1535980 < baseStart_1535980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1535993 : List Nat := [1, 2, 1, 3, 1, 5, 1, 8]
def baseStart_1535993 : Nat := 118140960795 + 1535993 * 2 ^ 59
def prefixEnd_1535993 : Nat := 4983230072969 + 3 ^ 40 * 1535993 * 2
def baseEnd_1535993 : Nat := 58422421551223270668415

theorem tailTrace_1535993 : CollatzResearch.WordTrace tailWord_1535993 prefixEnd_1535993 58422421551223270668415 := by
  unfold tailWord_1535993
  simp only [CollatzResearch.WordTrace]
  refine ⟨56022267124367162564612633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37348178082911441709741755 56022267124367162564612633)
  ·
    refine ⟨42016700343275371923459475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56022267124367162564612633 42016700343275371923459475)
    ·
      refine ⟨63025050514913057885189213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42016700343275371923459475 63025050514913057885189213)
      ·
        refine ⟨23634393943092396706945955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63025050514913057885189213 23634393943092396706945955)
        ·
          refine ⟨35451590914638595060418933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23634393943092396706945955 35451590914638595060418933)
          ·
            refine ⟨3323586648247368286914275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35451590914638595060418933 3323586648247368286914275)
            ·
              refine ⟨4985379972371052430371413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3323586648247368286914275 4985379972371052430371413)
              ·
                refine ⟨58422421551223270668415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4985379972371052430371413 58422421551223270668415)
                ·
                  rfl

theorem cell22_1535993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 8].length) (baseStart_1535993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1535993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1535993 prefixEnd_1535993 := by exact prefixLift 1535993
  have htrace : WordTrace (prefixWord ++ tailWord_1535993) baseStart_1535993 baseEnd_1535993 := by
    simpa [prefixWord, tailWord_1535993, baseEnd_1535993] using wordTrace_append hprefix tailTrace_1535993
  have hstable : (prefixWord ++ tailWord_1535993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1535993).length < 2 ^ (prefixWord ++ tailWord_1535993).sum := by decide
  have hdescent : baseEnd_1535993 < baseStart_1535993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1535993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536010 : List Nat := [3, 1, 2, 2, 4, 2, 8]
def baseStart_1536010 : Nat := 118140960795 + 1536010 * 2 ^ 59
def prefixEnd_1536010 : Nat := 4983230072969 + 3 ^ 40 * 1536010 * 2
def baseEnd_1536010 : Nat := 19474356052163965123729

theorem tailTrace_1536010 : CollatzResearch.WordTrace tailWord_1536010 prefixEnd_1536010 19474356052163965123729 := by
  unfold tailWord_1536010
  simp only [CollatzResearch.WordTrace]
  refine ⟨14005721791326393616995371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37348591443537049645320989 14005721791326393616995371)
  ·
    refine ⟨21008582686989590425493057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14005721791326393616995371 21008582686989590425493057)
    ·
      refine ⟨15756437015242192819119793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21008582686989590425493057 15756437015242192819119793)
      ·
        refine ⟨11817327761431644614339845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15756437015242192819119793 11817327761431644614339845)
        ·
          refine ⟨2215748955268433365188721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11817327761431644614339845 2215748955268433365188721)
          ·
            refine ⟨1661811716451325023891541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2215748955268433365188721 1661811716451325023891541)
            ·
              refine ⟨19474356052163965123729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1661811716451325023891541 19474356052163965123729)
              ·
                rfl

theorem cell22_1536010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 8].length) (baseStart_1536010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536010 prefixEnd_1536010 := by exact prefixLift 1536010
  have htrace : WordTrace (prefixWord ++ tailWord_1536010) baseStart_1536010 baseEnd_1536010 := by
    simpa [prefixWord, tailWord_1536010, baseEnd_1536010] using wordTrace_append hprefix tailTrace_1536010
  have hstable : (prefixWord ++ tailWord_1536010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536010).length < 2 ^ (prefixWord ++ tailWord_1536010).sum := by decide
  have hdescent : baseEnd_1536010 < baseStart_1536010 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536085 : List Nat := [1, 3, 2, 2, 1, 3, 1, 2, 3, 4]
def baseStart_1536085 : Nat := 118140960795 + 1536085 * 2 ^ 59
def prefixEnd_1536085 : Nat := 4983230072969 + 3 ^ 40 * 1536085 * 2
def baseEnd_1536085 : Nat := 525833287441151862715453

theorem tailTrace_1536085 : CollatzResearch.WordTrace tailWord_1536085 prefixEnd_1536085 525833287441151862715453 := by
  unfold tailWord_1536085
  simp only [CollatzResearch.WordTrace]
  refine ⟨56025622640033862276961709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37350415093355908184641139 56025622640033862276961709)
  ·
    refine ⟨21009608490012698353860641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56025622640033862276961709 21009608490012698353860641)
    ·
      refine ⟨15757206367509523765395481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21009608490012698353860641 15757206367509523765395481)
      ·
        refine ⟨11817904775632142824046611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15757206367509523765395481 11817904775632142824046611)
        ·
          refine ⟨17726857163448214236069917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11817904775632142824046611 17726857163448214236069917)
          ·
            refine ⟨6647571436293080338526219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17726857163448214236069917 6647571436293080338526219)
            ·
              refine ⟨9971357154439620507789329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6647571436293080338526219 9971357154439620507789329)
              ·
                refine ⟨7478517865829715380841997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9971357154439620507789329 7478517865829715380841997)
                ·
                  refine ⟨2804444199686143267815749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7478517865829715380841997 2804444199686143267815749)
                  ·
                    refine ⟨525833287441151862715453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2804444199686143267815749 525833287441151862715453)
                    ·
                      rfl

theorem cell22_1536085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_1536085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536085 prefixEnd_1536085 := by exact prefixLift 1536085
  have htrace : WordTrace (prefixWord ++ tailWord_1536085) baseStart_1536085 baseEnd_1536085 := by
    simpa [prefixWord, tailWord_1536085, baseEnd_1536085] using wordTrace_append hprefix tailTrace_1536085
  have hstable : (prefixWord ++ tailWord_1536085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536085).length < 2 ^ (prefixWord ++ tailWord_1536085).sum := by decide
  have hdescent : baseEnd_1536085 < baseStart_1536085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536119 : List Nat := [1, 1, 3, 1, 1, 7, 2, 1, 1, 4]
def baseStart_1536119 : Nat := 118140960795 + 1536119 * 2 ^ 59
def prefixEnd_1536119 : Nat := 4983230072969 + 3 ^ 40 * 1536119 * 2
def baseEnd_1536119 : Nat := 525844926335987107365349

theorem tailTrace_1536119 : CollatzResearch.WordTrace tailWord_1536119 prefixEnd_1536119 525844926335987107365349 := by
  unfold tailWord_1536119
  simp only [CollatzResearch.WordTrace]
  refine ⟨56026862721910686083699411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37351241814607124055799607 56026862721910686083699411)
  ·
    refine ⟨84040294082866029125549117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56026862721910686083699411 84040294082866029125549117)
    ·
      refine ⟨31515110281074760922080919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84040294082866029125549117 31515110281074760922080919)
      ·
        refine ⟨47272665421612141383121379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31515110281074760922080919 47272665421612141383121379)
        ·
          refine ⟨70908998132418212074682069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47272665421612141383121379 70908998132418212074682069)
          ·
            refine ⟨1661929643728551845500361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 70908998132418212074682069 1661929643728551845500361)
            ·
              refine ⟨1246447232796413884125271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1661929643728551845500361 1246447232796413884125271)
              ·
                refine ⟨1869670849194620826187907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246447232796413884125271 1869670849194620826187907)
                ·
                  refine ⟨2804506273791931239281861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1869670849194620826187907 2804506273791931239281861)
                  ·
                    refine ⟨525844926335987107365349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2804506273791931239281861 525844926335987107365349)
                    ·
                      rfl

theorem cell22_1536119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_1536119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536119 prefixEnd_1536119 := by exact prefixLift 1536119
  have htrace : WordTrace (prefixWord ++ tailWord_1536119) baseStart_1536119 baseEnd_1536119 := by
    simpa [prefixWord, tailWord_1536119, baseEnd_1536119] using wordTrace_append hprefix tailTrace_1536119
  have hstable : (prefixWord ++ tailWord_1536119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536119).length < 2 ^ (prefixWord ++ tailWord_1536119).sum := by decide
  have hdescent : baseEnd_1536119 < baseStart_1536119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536132 : List Nat := [2, 3, 2, 1, 2, 1, 3, 1, 4, 3]
def baseStart_1536132 : Nat := 118140960795 + 1536132 * 2 ^ 59
def prefixEnd_1536132 : Nat := 4983230072969 + 3 ^ 40 * 1536132 * 2
def baseEnd_1536132 : Nat := 525849376501659406790309

theorem tailTrace_1536132 : CollatzResearch.WordTrace tailWord_1536132 prefixEnd_1536132 525849376501659406790309 := by
  unfold tailWord_1536132
  simp only [CollatzResearch.WordTrace]
  refine ⟨28013668435431794651961325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37351557913909059535948433 28013668435431794651961325)
  ·
    refine ⟨10505125663286922994485497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28013668435431794651961325 10505125663286922994485497)
    ·
      refine ⟨7878844247465192245864123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10505125663286922994485497 7878844247465192245864123)
      ·
        refine ⟨11818266371197788368796185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7878844247465192245864123 11818266371197788368796185)
        ·
          refine ⟨8863699778398341276597139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11818266371197788368796185 8863699778398341276597139)
          ·
            refine ⟨13295549667597511914895709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8863699778398341276597139 13295549667597511914895709)
            ·
              refine ⟨4985831125349066968085891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13295549667597511914895709 4985831125349066968085891)
              ·
                refine ⟨7478746688023600452128837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4985831125349066968085891 7478746688023600452128837)
                ·
                  refine ⟨1402265004004425084774157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7478746688023600452128837 1402265004004425084774157)
                  ·
                    refine ⟨525849376501659406790309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1402265004004425084774157 525849376501659406790309)
                    ·
                      rfl

theorem cell22_1536132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_1536132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536132 prefixEnd_1536132 := by exact prefixLift 1536132
  have htrace : WordTrace (prefixWord ++ tailWord_1536132) baseStart_1536132 baseEnd_1536132 := by
    simpa [prefixWord, tailWord_1536132, baseEnd_1536132] using wordTrace_append hprefix tailTrace_1536132
  have hstable : (prefixWord ++ tailWord_1536132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536132).length < 2 ^ (prefixWord ++ tailWord_1536132).sum := by decide
  have hdescent : baseEnd_1536132 < baseStart_1536132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536149 : List Nat := [1, 3, 2, 1, 1, 1, 7, 1, 2, 3]
def baseStart_1536149 : Nat := 118140960795 + 1536149 * 2 ^ 59
def prefixEnd_1536149 : Nat := 4983230072969 + 3 ^ 40 * 1536149 * 2
def baseEnd_1536149 : Nat := 525855195949077029115257

theorem tailTrace_1536149 : CollatzResearch.WordTrace tailWord_1536149 prefixEnd_1536149 525855195949077029115257 := by
  unfold tailWord_1536149
  simp only [CollatzResearch.WordTrace]
  refine ⟨56027956911802001207291501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37351971274534667471527667 56027956911802001207291501)
  ·
    refine ⟨21010483841925750452734313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56027956911802001207291501 21010483841925750452734313)
    ·
      refine ⟨15757862881444312839550735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21010483841925750452734313 15757862881444312839550735)
      ·
        refine ⟨23636794322166469259326103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15757862881444312839550735 23636794322166469259326103)
        ·
          refine ⟨35455191483249703888989155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23636794322166469259326103 35455191483249703888989155)
          ·
            refine ⟨53182787224874555833483733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35455191483249703888989155 53182787224874555833483733)
            ·
              refine ⟨1246471575582997402347275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 53182787224874555833483733 1246471575582997402347275)
              ·
                refine ⟨1869707363374496103520913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246471575582997402347275 1869707363374496103520913)
                ·
                  refine ⟨1402280522530872077640685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1869707363374496103520913 1402280522530872077640685)
                  ·
                    refine ⟨525855195949077029115257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1402280522530872077640685 525855195949077029115257)
                    ·
                      rfl

theorem cell22_1536149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_1536149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536149 prefixEnd_1536149 := by exact prefixLift 1536149
  have htrace : WordTrace (prefixWord ++ tailWord_1536149) baseStart_1536149 baseEnd_1536149 := by
    simpa [prefixWord, tailWord_1536149, baseEnd_1536149] using wordTrace_append hprefix tailTrace_1536149
  have hstable : (prefixWord ++ tailWord_1536149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536149).length < 2 ^ (prefixWord ++ tailWord_1536149).sum := by decide
  have hdescent : baseEnd_1536149 < baseStart_1536149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536162 : List Nat := [3, 3, 1, 3, 1, 2, 1, 8]
def baseStart_1536162 : Nat := 118140960795 + 1536162 * 2 ^ 59
def prefixEnd_1536162 : Nat := 4983230072969 + 3 ^ 40 * 1536162 * 2
def baseEnd_1536162 : Nat := 58428849568305480948913

theorem tailTrace_1536162 : CollatzResearch.WordTrace tailWord_1536162 prefixEnd_1536162 58428849568305480948913 := by
  unfold tailWord_1536162
  simp only [CollatzResearch.WordTrace]
  refine ⟨14007107765188726106878685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37352287373836602951676493 14007107765188726106878685)
  ·
    refine ⟨5252665411945772290079507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14007107765188726106878685 5252665411945772290079507)
    ·
      refine ⟨7878998117918658435119261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5252665411945772290079507 7878998117918658435119261)
      ·
        refine ⟨2954624294219496913169723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7878998117918658435119261 2954624294219496913169723)
        ·
          refine ⟨4431936441329245369754585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2954624294219496913169723 4431936441329245369754585)
          ·
            refine ⟨3323952330996934027315939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4431936441329245369754585 3323952330996934027315939)
            ·
              refine ⟨4985928496495401040973909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3323952330996934027315939 4985928496495401040973909)
              ·
                refine ⟨58428849568305480948913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4985928496495401040973909 58428849568305480948913)
                ·
                  rfl

theorem cell22_1536162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 8].length) (baseStart_1536162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536162 prefixEnd_1536162 := by exact prefixLift 1536162
  have htrace : WordTrace (prefixWord ++ tailWord_1536162) baseStart_1536162 baseEnd_1536162 := by
    simpa [prefixWord, tailWord_1536162, baseEnd_1536162] using wordTrace_append hprefix tailTrace_1536162
  have hstable : (prefixWord ++ tailWord_1536162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536162).length < 2 ^ (prefixWord ++ tailWord_1536162).sum := by decide
  have hdescent : baseEnd_1536162 < baseStart_1536162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536267 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 1, 5]
def baseStart_1536267 : Nat := 118140960795 + 1536267 * 2 ^ 59
def prefixEnd_1536267 : Nat := 4983230072969 + 3 ^ 40 * 1536267 * 2
def baseEnd_1536267 : Nat := 525895589760564054664895

theorem tailTrace_1536267 : CollatzResearch.WordTrace tailWord_1536267 prefixEnd_1536267 525895589760564054664895 := by
  unfold tailWord_1536267
  simp only [CollatzResearch.WordTrace]
  refine ⟨56032260725374507360087055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37354840483583004906724703 56032260725374507360087055)
  ·
    refine ⟨84048391088061761040130583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56032260725374507360087055 84048391088061761040130583)
    ·
      refine ⟨126072586632092641560195875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84048391088061761040130583 126072586632092641560195875)
      ·
        refine ⟨189108879948138962340293813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126072586632092641560195875 189108879948138962340293813)
        ·
          refine ⟨17728957495138027719402545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189108879948138962340293813 17728957495138027719402545)
          ·
            refine ⟨13296718121353520789551909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17728957495138027719402545 13296718121353520789551909)
            ·
              refine ⟨2493134647753785148040983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13296718121353520789551909 2493134647753785148040983)
              ·
                refine ⟨3739701971630677722061475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2493134647753785148040983 3739701971630677722061475)
                ·
                  refine ⟨5609552957446016583092213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3739701971630677722061475 5609552957446016583092213)
                  ·
                    refine ⟨525895589760564054664895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5609552957446016583092213 525895589760564054664895)
                    ·
                      rfl

theorem cell22_1536267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 1, 5].length) (baseStart_1536267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536267 prefixEnd_1536267 := by exact prefixLift 1536267
  have htrace : WordTrace (prefixWord ++ tailWord_1536267) baseStart_1536267 baseEnd_1536267 := by
    simpa [prefixWord, tailWord_1536267, baseEnd_1536267] using wordTrace_append hprefix tailTrace_1536267
  have hstable : (prefixWord ++ tailWord_1536267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536267).length < 2 ^ (prefixWord ++ tailWord_1536267).sum := by decide
  have hdescent : baseEnd_1536267 < baseStart_1536267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536318 : List Nat := [4, 2, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_1536318 : Nat := 118140960795 + 1536318 * 2 ^ 59
def prefixEnd_1536318 : Nat := 4983230072969 + 3 ^ 40 * 1536318 * 2
def baseEnd_1536318 : Nat := 525913048102816921639739

theorem tailTrace_1536318 : CollatzResearch.WordTrace tailWord_1536318 prefixEnd_1536318 525913048102816921639739 := by
  unfold tailWord_1536318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7004265106023717883774201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37356080565459828713462405 7004265106023717883774201)
  ·
    refine ⟨5253198829517788412830651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7004265106023717883774201 5253198829517788412830651)
    ·
      refine ⟨7879798244276682619245977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5253198829517788412830651 7879798244276682619245977)
      ·
        refine ⟨5909848683207511964434483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7879798244276682619245977 5909848683207511964434483)
        ·
          refine ⟨8864773024811267946651725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5909848683207511964434483 8864773024811267946651725)
          ·
            refine ⟨3324289884304225479994397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8864773024811267946651725 3324289884304225479994397)
            ·
              refine ⟨1246608706614084554997899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3324289884304225479994397 1246608706614084554997899)
              ·
                refine ⟨1869913059921126832496849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246608706614084554997899 1869913059921126832496849)
                ·
                  refine ⟨1402434794940845124372637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1869913059921126832496849 1402434794940845124372637)
                  ·
                    refine ⟨525913048102816921639739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1402434794940845124372637 525913048102816921639739)
                    ·
                      rfl

theorem cell22_1536318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_1536318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536318 prefixEnd_1536318 := by exact prefixLift 1536318
  have htrace : WordTrace (prefixWord ++ tailWord_1536318) baseStart_1536318 baseEnd_1536318 := by
    simpa [prefixWord, tailWord_1536318, baseEnd_1536318] using wordTrace_append hprefix tailTrace_1536318
  have hstable : (prefixWord ++ tailWord_1536318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536318).length < 2 ^ (prefixWord ++ tailWord_1536318).sum := by decide
  have hdescent : baseEnd_1536318 < baseStart_1536318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536466 : List Nat := [3, 2, 2, 4, 1, 1, 9]
def baseStart_1536466 : Nat := 118140960795 + 1536466 * 2 ^ 59
def prefixEnd_1536466 : Nat := 4983230072969 + 3 ^ 40 * 1536466 * 2
def baseEnd_1536466 : Nat := 19480137463977550701455

theorem tailTrace_1536466 : CollatzResearch.WordTrace tailWord_1536466 prefixEnd_1536466 19480137463977550701455 := by
  unfold tailWord_1536466
  simp only [CollatzResearch.WordTrace]
  refine ⟨14009879712913391086645313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37359679234435709564387501 14009879712913391086645313)
  ·
    refine ⟨10507409784685043314983985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14009879712913391086645313 10507409784685043314983985)
    ·
      refine ⟨7880557338513782486237989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10507409784685043314983985 7880557338513782486237989)
      ·
        refine ⟨1477604500971334216169623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7880557338513782486237989 1477604500971334216169623)
        ·
          refine ⟨2216406751457001324254435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1477604500971334216169623 2216406751457001324254435)
          ·
            refine ⟨3324610127185501986381653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2216406751457001324254435 3324610127185501986381653)
            ·
              refine ⟨19480137463977550701455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3324610127185501986381653 19480137463977550701455)
              ·
                rfl

theorem cell22_1536466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 9].length) (baseStart_1536466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536466 prefixEnd_1536466 := by exact prefixLift 1536466
  have htrace : WordTrace (prefixWord ++ tailWord_1536466) baseStart_1536466 baseEnd_1536466 := by
    simpa [prefixWord, tailWord_1536466, baseEnd_1536466] using wordTrace_append hprefix tailTrace_1536466
  have hstable : (prefixWord ++ tailWord_1536466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536466).length < 2 ^ (prefixWord ++ tailWord_1536466).sum := by decide
  have hdescent : baseEnd_1536466 < baseStart_1536466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536481 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 3, 3]
def baseStart_1536481 : Nat := 118140960795 + 1536481 * 2 ^ 59
def prefixEnd_1536481 : Nat := 4983230072969 + 3 ^ 40 * 1536481 * 2
def baseEnd_1536481 : Nat := 525968846333938829814239

theorem tailTrace_1536481 : CollatzResearch.WordTrace tailWord_1536481 prefixEnd_1536481 525968846333938829814239 := by
  unfold tailWord_1536481
  simp only [CollatzResearch.WordTrace]
  refine ⟨56040065946599221908377297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37360043964399481272251531 56040065946599221908377297)
  ·
    refine ⟨42030049459949416431282973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56040065946599221908377297 42030049459949416431282973)
    ·
      refine ⟨15761268547481031161731115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42030049459949416431282973 15761268547481031161731115)
      ·
        refine ⟨23641902821221546742596673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15761268547481031161731115 23641902821221546742596673)
        ·
          refine ⟨17731427115916160056947505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23641902821221546742596673 17731427115916160056947505)
          ·
            refine ⟨13298570336937120042710629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17731427115916160056947505 13298570336937120042710629)
            ·
              refine ⟨2493481938175710008008243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13298570336937120042710629 2493481938175710008008243)
              ·
                refine ⟨3740222907263565012012365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2493481938175710008008243 3740222907263565012012365)
                ·
                  refine ⟨1402583590223836879504637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3740222907263565012012365 1402583590223836879504637)
                  ·
                    refine ⟨525968846333938829814239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1402583590223836879504637 525968846333938829814239)
                    ·
                      rfl

theorem cell22_1536481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_1536481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536481 prefixEnd_1536481 := by exact prefixLift 1536481
  have htrace : WordTrace (prefixWord ++ tailWord_1536481) baseStart_1536481 baseEnd_1536481 := by
    simpa [prefixWord, tailWord_1536481, baseEnd_1536481] using wordTrace_append hprefix tailTrace_1536481
  have hstable : (prefixWord ++ tailWord_1536481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536481).length < 2 ^ (prefixWord ++ tailWord_1536481).sum := by decide
  have hdescent : baseEnd_1536481 < baseStart_1536481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536558 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1536558 : Nat := 118140960795 + 1536558 * 2 ^ 59
def prefixEnd_1536558 : Nat := 4983230072969 + 3 ^ 40 * 1536558 * 2
def baseEnd_1536558 : Nat := 525995205007536295639003

theorem tailTrace_1536558 : CollatzResearch.WordTrace tailWord_1536558 prefixEnd_1536558 525995205007536295639003 := by
  unfold tailWord_1536558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7005359295915033007366291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37361916244880176039286885 7005359295915033007366291)
  ·
    refine ⟨10508038943872549511049437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7005359295915033007366291 10508038943872549511049437)
    ·
      refine ⟨3940514603952206066643539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10508038943872549511049437 3940514603952206066643539)
      ·
        refine ⟨5910771905928309099965309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3940514603952206066643539 5910771905928309099965309)
        ·
          refine ⟨2216539464723115912486991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5910771905928309099965309 2216539464723115912486991)
          ·
            refine ⟨3324809197084673868730487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2216539464723115912486991 3324809197084673868730487)
            ·
              refine ⟨4987213795627010803095731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3324809197084673868730487 4987213795627010803095731)
              ·
                refine ⟨7480820693440516204643597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4987213795627010803095731 7480820693440516204643597)
                ·
                  refine ⟨2805307760040193576741349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7480820693440516204643597 2805307760040193576741349)
                  ·
                    refine ⟨525995205007536295639003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2805307760040193576741349 525995205007536295639003)
                    ·
                      rfl

theorem cell22_1536558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1536558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536558 prefixEnd_1536558 := by exact prefixLift 1536558
  have htrace : WordTrace (prefixWord ++ tailWord_1536558) baseStart_1536558 baseEnd_1536558 := by
    simpa [prefixWord, tailWord_1536558, baseEnd_1536558] using wordTrace_append hprefix tailTrace_1536558
  have hstable : (prefixWord ++ tailWord_1536558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536558).length < 2 ^ (prefixWord ++ tailWord_1536558).sum := by decide
  have hdescent : baseEnd_1536558 < baseStart_1536558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536586 : List Nat := [3, 1, 2, 1, 1, 4, 2, 2, 2, 4]
def baseStart_1536586 : Nat := 118140960795 + 1536586 * 2 ^ 59
def prefixEnd_1536586 : Nat := 4983230072969 + 3 ^ 40 * 1536586 * 2
def baseEnd_1536586 : Nat := 526004789979753555938917

theorem tailTrace_1536586 : CollatzResearch.WordTrace tailWord_1536586 prefixEnd_1536586 526004789979753555938917 := by
  unfold tailWord_1536586
  simp only [CollatzResearch.WordTrace]
  refine ⟨14010973902804706210237403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37362597074145883227299741 14010973902804706210237403)
  ·
    refine ⟨21016460854207059315356105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14010973902804706210237403 21016460854207059315356105)
    ·
      refine ⟨15762345640655294486517079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21016460854207059315356105 15762345640655294486517079)
      ·
        refine ⟨23643518460982941729775619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15762345640655294486517079 23643518460982941729775619)
        ·
          refine ⟨35465277691474412594663429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23643518460982941729775619 35465277691474412594663429)
          ·
            refine ⟨6649739567151452361499393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35465277691474412594663429 6649739567151452361499393)
            ·
              refine ⟨4987304675363589271124545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6649739567151452361499393 4987304675363589271124545)
              ·
                refine ⟨3740478506522691953343409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4987304675363589271124545 3740478506522691953343409)
                ·
                  refine ⟨2805358879892018965007557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3740478506522691953343409 2805358879892018965007557)
                  ·
                    refine ⟨526004789979753555938917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2805358879892018965007557 526004789979753555938917)
                    ·
                      rfl

theorem cell22_1536586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_1536586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536586 prefixEnd_1536586 := by exact prefixLift 1536586
  have htrace : WordTrace (prefixWord ++ tailWord_1536586) baseStart_1536586 baseEnd_1536586 := by
    simpa [prefixWord, tailWord_1536586, baseEnd_1536586] using wordTrace_append hprefix tailTrace_1536586
  have hstable : (prefixWord ++ tailWord_1536586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536586).length < 2 ^ (prefixWord ++ tailWord_1536586).sum := by decide
  have hdescent : baseEnd_1536586 < baseStart_1536586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536588 : List Nat := [2, 2, 1, 3, 1, 2, 4, 2, 2, 3]
def baseStart_1536588 : Nat := 118140960795 + 1536588 * 2 ^ 59
def prefixEnd_1536588 : Nat := 4983230072969 + 3 ^ 40 * 1536588 * 2
def baseEnd_1536588 : Nat := 526005474620626217388911

theorem tailTrace_1536588 : CollatzResearch.WordTrace tailWord_1536588 prefixEnd_1536588 526005474620626217388911 := by
  unfold tailWord_1536588
  simp only [CollatzResearch.WordTrace]
  refine ⟨28021984278605789591261209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37362645704807719455014945 28021984278605789591261209)
  ·
    refine ⟨21016488208954342193445907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28021984278605789591261209 21016488208954342193445907)
    ·
      refine ⟨31524732313431513290168861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21016488208954342193445907 31524732313431513290168861)
      ·
        refine ⟨11821774617536817483813323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31524732313431513290168861 11821774617536817483813323)
        ·
          refine ⟨17732661926305226225719985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11821774617536817483813323 17732661926305226225719985)
          ·
            refine ⟨13299496444728919669289989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17732661926305226225719985 13299496444728919669289989)
            ·
              refine ⟨2493655583386672437991873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13299496444728919669289989 2493655583386672437991873)
              ·
                refine ⟨1870241687540004328493905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2493655583386672437991873 1870241687540004328493905)
                ·
                  refine ⟨1402681265655003246370429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1870241687540004328493905 1402681265655003246370429)
                  ·
                    refine ⟨526005474620626217388911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1402681265655003246370429 526005474620626217388911)
                    ·
                      rfl

theorem cell22_1536588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_1536588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536588 prefixEnd_1536588 := by exact prefixLift 1536588
  have htrace : WordTrace (prefixWord ++ tailWord_1536588) baseStart_1536588 baseEnd_1536588 := by
    simpa [prefixWord, tailWord_1536588, baseEnd_1536588] using wordTrace_append hprefix tailTrace_1536588
  have hstable : (prefixWord ++ tailWord_1536588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536588).length < 2 ^ (prefixWord ++ tailWord_1536588).sum := by decide
  have hdescent : baseEnd_1536588 < baseStart_1536588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536650 : List Nat := [3, 1, 2, 3, 3, 1, 2, 1, 3, 3]
def baseStart_1536650 : Nat := 118140960795 + 1536650 * 2 ^ 59
def prefixEnd_1536650 : Nat := 4983230072969 + 3 ^ 40 * 1536650 * 2
def baseEnd_1536650 : Nat := 526026698487678722338721

theorem tailTrace_1536650 : CollatzResearch.WordTrace tailWord_1536650 prefixEnd_1536650 526026698487678722338721 := by
  unfold tailWord_1536650
  simp only [CollatzResearch.WordTrace]
  refine ⟨14011557470746740942819851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37364153255324642514186269 14011557470746740942819851)
  ·
    refine ⟨21017336206120111414229777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14011557470746740942819851 21017336206120111414229777)
    ·
      refine ⟨15763002154590083560672333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21017336206120111414229777 15763002154590083560672333)
      ·
        refine ⟨5911125807971281335252125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15763002154590083560672333 5911125807971281335252125)
        ·
          refine ⟨2216672177989230500719547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5911125807971281335252125 2216672177989230500719547)
          ·
            refine ⟨3325008266983845751079321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2216672177989230500719547 3325008266983845751079321)
            ·
              refine ⟨2493756200237884313309491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3325008266983845751079321 2493756200237884313309491)
              ·
                refine ⟨3740634300356826469964237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2493756200237884313309491 3740634300356826469964237)
                ·
                  refine ⟨1402737862633809926236589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3740634300356826469964237 1402737862633809926236589)
                  ·
                    refine ⟨526026698487678722338721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1402737862633809926236589 526026698487678722338721)
                    ·
                      rfl

theorem cell22_1536650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_1536650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536650 prefixEnd_1536650 := by exact prefixLift 1536650
  have htrace : WordTrace (prefixWord ++ tailWord_1536650) baseStart_1536650 baseEnd_1536650 := by
    simpa [prefixWord, tailWord_1536650, baseEnd_1536650] using wordTrace_append hprefix tailTrace_1536650
  have hstable : (prefixWord ++ tailWord_1536650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536650).length < 2 ^ (prefixWord ++ tailWord_1536650).sum := by decide
  have hdescent : baseEnd_1536650 < baseStart_1536650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536663 : List Nat := [1, 1, 3, 3, 2, 1, 5, 1, 5]
def baseStart_1536663 : Nat := 118140960795 + 1536663 * 2 ^ 59
def prefixEnd_1536663 : Nat := 4983230072969 + 3 ^ 40 * 1536663 * 2
def baseEnd_1536663 : Nat := 175343716217783673921227

theorem tailTrace_1536663 : CollatzResearch.WordTrace tailWord_1536663 prefixEnd_1536663 175343716217783673921227 := by
  unfold tailWord_1536663
  simp only [CollatzResearch.WordTrace]
  refine ⟨56046704031939866991502643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37364469354626577994335095 56046704031939866991502643)
  ·
    refine ⟨84070056047909800487253965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56046704031939866991502643 84070056047909800487253965)
    ·
      refine ⟨31526271017966175182720237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84070056047909800487253965 31526271017966175182720237)
      ·
        refine ⟨11822351631737315693520089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31526271017966175182720237 11822351631737315693520089)
        ·
          refine ⟨8866763723802986770140067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11822351631737315693520089 8866763723802986770140067)
          ·
            refine ⟨13300145585704480155210101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8866763723802986770140067 13300145585704480155210101)
            ·
              refine ⟨1246888648659795014550947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13300145585704480155210101 1246888648659795014550947)
              ·
                refine ⟨1870332972989692521826421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1246888648659795014550947 1870332972989692521826421)
                ·
                  refine ⟨175343716217783673921227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1870332972989692521826421 175343716217783673921227)
                  ·
                    rfl

theorem cell22_1536663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 5].length) (baseStart_1536663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536663 prefixEnd_1536663 := by exact prefixLift 1536663
  have htrace : WordTrace (prefixWord ++ tailWord_1536663) baseStart_1536663 baseEnd_1536663 := by
    simpa [prefixWord, tailWord_1536663, baseEnd_1536663] using wordTrace_append hprefix tailTrace_1536663
  have hstable : (prefixWord ++ tailWord_1536663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536663).length < 2 ^ (prefixWord ++ tailWord_1536663).sum := by decide
  have hdescent : baseEnd_1536663 < baseStart_1536663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536708 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 6]
def baseStart_1536708 : Nat := 118140960795 + 1536708 * 2 ^ 59
def prefixEnd_1536708 : Nat := 4983230072969 + 3 ^ 40 * 1536708 * 2
def baseEnd_1536708 : Nat := 175348851024328634796181

theorem tailTrace_1536708 : CollatzResearch.WordTrace tailWord_1536708 prefixEnd_1536708 175348851024328634796181 := by
  unfold tailWord_1536708
  simp only [CollatzResearch.WordTrace]
  refine ⟨28024172658388419838445389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37365563544517893117927185 28024172658388419838445389)
  ·
    refine ⟨10509064746895657439417021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28024172658388419838445389 10509064746895657439417021)
    ·
      refine ⟨3940899280085871539781383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10509064746895657439417021 3940899280085871539781383)
      ·
        refine ⟨5911348920128807309672075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3940899280085871539781383 5911348920128807309672075)
        ·
          refine ⟨8867023380193210964508113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5911348920128807309672075 8867023380193210964508113)
          ·
            refine ⟨6650267535144908223381085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8867023380193210964508113 6650267535144908223381085)
            ·
              refine ⟨2493850325679340583767907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6650267535144908223381085 2493850325679340583767907)
              ·
                refine ⟨3740775488519010875651861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2493850325679340583767907 3740775488519010875651861)
                ·
                  refine ⟨175348851024328634796181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3740775488519010875651861 175348851024328634796181)
                  ·
                    rfl

theorem cell22_1536708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_1536708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536708 prefixEnd_1536708 := by exact prefixLift 1536708
  have htrace : WordTrace (prefixWord ++ tailWord_1536708) baseStart_1536708 baseEnd_1536708 := by
    simpa [prefixWord, tailWord_1536708, baseEnd_1536708] using wordTrace_append hprefix tailTrace_1536708
  have hstable : (prefixWord ++ tailWord_1536708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536708).length < 2 ^ (prefixWord ++ tailWord_1536708).sum := by decide
  have hdescent : baseEnd_1536708 < baseStart_1536708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536721 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 4, 4]
def baseStart_1536721 : Nat := 118140960795 + 1536721 * 2 ^ 59
def prefixEnd_1536721 : Nat := 4983230072969 + 3 ^ 40 * 1536721 * 2
def baseEnd_1536721 : Nat := 526051003238658203813503

theorem tailTrace_1536721 : CollatzResearch.WordTrace tailWord_1536721 prefixEnd_1536721 526051003238658203813503 := by
  unfold tailWord_1536721
  simp only [CollatzResearch.WordTrace]
  refine ⟨56048819465729742897114017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37365879643819828598076011 56048819465729742897114017)
  ·
    refine ⟨42036614599297307172835513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56048819465729742897114017 42036614599297307172835513)
    ·
      refine ⟨31527460949472980379626635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42036614599297307172835513 31527460949472980379626635)
      ·
        refine ⟨47291191424209470569439953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31527460949472980379626635 47291191424209470569439953)
        ·
          refine ⟨35468393568157102927079965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47291191424209470569439953 35468393568157102927079965)
          ·
            refine ⟨13300647588058913597654987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35468393568157102927079965 13300647588058913597654987)
            ·
              refine ⟨19950971382088370396482481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13300647588058913597654987 19950971382088370396482481)
              ·
                refine ⟨14963228536566277797361861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19950971382088370396482481 14963228536566277797361861)
                ·
                  refine ⟨2805605350606177087005349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14963228536566277797361861 2805605350606177087005349)
                  ·
                    refine ⟨526051003238658203813503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2805605350606177087005349 526051003238658203813503)
                    ·
                      rfl

theorem cell22_1536721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 4, 4].length) (baseStart_1536721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536721 prefixEnd_1536721 := by exact prefixLift 1536721
  have htrace : WordTrace (prefixWord ++ tailWord_1536721) baseStart_1536721 baseEnd_1536721 := by
    simpa [prefixWord, tailWord_1536721, baseEnd_1536721] using wordTrace_append hprefix tailTrace_1536721
  have hstable : (prefixWord ++ tailWord_1536721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536721).length < 2 ^ (prefixWord ++ tailWord_1536721).sum := by decide
  have hdescent : baseEnd_1536721 < baseStart_1536721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536770 : List Nat := [3, 4, 1, 1, 1, 4, 1, 7]
def baseStart_1536770 : Nat := 118140960795 + 1536770 * 2 ^ 59
def prefixEnd_1536770 : Nat := 4983230072969 + 3 ^ 40 * 1536770 * 2
def baseEnd_1536770 : Nat := 58451975215559823259817

theorem tailTrace_1536770 : CollatzResearch.WordTrace tailWord_1536770 prefixEnd_1536770 58451975215559823259817 := by
  unfold tailWord_1536770
  simp only [CollatzResearch.WordTrace]
  refine ⟨14012651660638056066411941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37367071095034816177098509 14012651660638056066411941)
  ·
    refine ⟨2627372186369635512452239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14012651660638056066411941 2627372186369635512452239)
    ·
      refine ⟨3941058279554453268678359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2627372186369635512452239 3941058279554453268678359)
      ·
        refine ⟨5911587419331679903017539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3941058279554453268678359 5911587419331679903017539)
        ·
          refine ⟨8867381128997519854526309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5911587419331679903017539 8867381128997519854526309)
          ·
            refine ⟨1662633961687034972723683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8867381128997519854526309 1662633961687034972723683)
            ·
              refine ⟨2493950942530552459085525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1662633961687034972723683 2493950942530552459085525)
              ·
                refine ⟨58451975215559823259817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2493950942530552459085525 58451975215559823259817)
                ·
                  rfl

theorem cell22_1536770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 7].length) (baseStart_1536770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536770 prefixEnd_1536770 := by exact prefixLift 1536770
  have htrace : WordTrace (prefixWord ++ tailWord_1536770) baseStart_1536770 baseEnd_1536770 := by
    simpa [prefixWord, tailWord_1536770, baseEnd_1536770] using wordTrace_append hprefix tailTrace_1536770
  have hstable : (prefixWord ++ tailWord_1536770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536770).length < 2 ^ (prefixWord ++ tailWord_1536770).sum := by decide
  have hdescent : baseEnd_1536770 < baseStart_1536770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536802 : List Nat := [3, 3, 1, 1, 2, 2, 1, 5, 1, 3]
def baseStart_1536802 : Nat := 118140960795 + 1536802 * 2 ^ 59
def prefixEnd_1536802 : Nat := 4983230072969 + 3 ^ 40 * 1536802 * 2
def baseEnd_1536802 : Nat := 526078731194000992538255

theorem tailTrace_1536802 : CollatzResearch.WordTrace tailWord_1536802 prefixEnd_1536802 526078731194000992538255 := by
  unfold tailWord_1536802
  simp only [CollatzResearch.WordTrace]
  refine ⟨14012943444609073432703165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37367849185624195820541773 14012943444609073432703165)
  ·
    refine ⟨5254853791728402537263687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14012943444609073432703165 5254853791728402537263687)
    ·
      refine ⟨7882280687592603805895531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5254853791728402537263687 7882280687592603805895531)
      ·
        refine ⟨11823421031388905708843297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7882280687592603805895531 11823421031388905708843297)
        ·
          refine ⟨8867565773541679281632473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11823421031388905708843297 8867565773541679281632473)
          ·
            refine ⟨6650674330156259461224355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8867565773541679281632473 6650674330156259461224355)
            ·
              refine ⟨9976011495234389191836533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6650674330156259461224355 9976011495234389191836533)
              ·
                refine ⟨935251077678223986734675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9976011495234389191836533 935251077678223986734675)
                ·
                  refine ⟨1402876616517335980102013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935251077678223986734675 1402876616517335980102013)
                  ·
                    refine ⟨526078731194000992538255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1402876616517335980102013 526078731194000992538255)
                    ·
                      rfl

theorem cell22_1536802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_1536802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536802 prefixEnd_1536802 := by exact prefixLift 1536802
  have htrace : WordTrace (prefixWord ++ tailWord_1536802) baseStart_1536802 baseEnd_1536802 := by
    simpa [prefixWord, tailWord_1536802, baseEnd_1536802] using wordTrace_append hprefix tailTrace_1536802
  have hstable : (prefixWord ++ tailWord_1536802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536802).length < 2 ^ (prefixWord ++ tailWord_1536802).sum := by decide
  have hdescent : baseEnd_1536802 < baseStart_1536802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536937 : List Nat := [1, 2, 1, 1, 1, 1, 7, 4, 1, 3]
def baseStart_1536937 : Nat := 118140960795 + 1536937 * 2 ^ 59
def prefixEnd_1536937 : Nat := 4983230072969 + 3 ^ 40 * 1536937 * 2
def baseEnd_1536937 : Nat := 526124944452905640412841

theorem tailTrace_1536937 : CollatzResearch.WordTrace tailWord_1536937 prefixEnd_1536937 526124944452905640412841 := by
  unfold tailWord_1536937
  simp only [CollatzResearch.WordTrace]
  refine ⟨56056697632947211786977065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37371131755298141191318043 56056697632947211786977065)
  ·
    refine ⟨42042523224710408840232799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56056697632947211786977065 42042523224710408840232799)
    ·
      refine ⟨63063784837065613260349199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42042523224710408840232799 63063784837065613260349199)
      ·
        refine ⟨94595677255598419890523799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63063784837065613260349199 94595677255598419890523799)
        ·
          refine ⟨141893515883397629835785699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94595677255598419890523799 141893515883397629835785699)
          ·
            refine ⟨212840273825096444753678549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 141893515883397629835785699 212840273825096444753678549)
            ·
              refine ⟨4988443917775697923914341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 212840273825096444753678549 4988443917775697923914341)
              ·
                refine ⟨935333234582943360733939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4988443917775697923914341 935333234582943360733939)
                ·
                  refine ⟨1402999851874415041100909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935333234582943360733939 1402999851874415041100909)
                  ·
                    refine ⟨526124944452905640412841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1402999851874415041100909 526124944452905640412841)
                    ·
                      rfl

theorem cell22_1536937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 1, 3].length) (baseStart_1536937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536937 prefixEnd_1536937 := by exact prefixLift 1536937
  have htrace : WordTrace (prefixWord ++ tailWord_1536937) baseStart_1536937 baseEnd_1536937 := by
    simpa [prefixWord, tailWord_1536937, baseEnd_1536937] using wordTrace_append hprefix tailTrace_1536937
  have hstable : (prefixWord ++ tailWord_1536937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536937).length < 2 ^ (prefixWord ++ tailWord_1536937).sum := by decide
  have hdescent : baseEnd_1536937 < baseStart_1536937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536982 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_1536982 : Nat := 118140960795 + 1536982 * 2 ^ 59
def prefixEnd_1536982 : Nat := 4983230072969 + 3 ^ 40 * 1536982 * 2
def baseEnd_1536982 : Nat := 526140348872540523037703

theorem tailTrace_1536982 : CollatzResearch.WordTrace tailWord_1536982 prefixEnd_1536982 526140348872540523037703 := by
  unfold tailWord_1536982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3503646182361511529522825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37372225945189456314910133 3503646182361511529522825)
  ·
    refine ⟨2627734636771133647142119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3503646182361511529522825 2627734636771133647142119)
    ·
      refine ⟨3941601955156700470713179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2627734636771133647142119 3941601955156700470713179)
      ·
        refine ⟨5912402932735050706069769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3941601955156700470713179 5912402932735050706069769)
        ·
          refine ⟨4434302199551288029552327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5912402932735050706069769 4434302199551288029552327)
          ·
            refine ⟨6651453299326932044328491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4434302199551288029552327 6651453299326932044328491)
            ·
              refine ⟨9977179948990398066492737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6651453299326932044328491 9977179948990398066492737)
              ·
                refine ⟨7482884961742798549869553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9977179948990398066492737 7482884961742798549869553)
                ·
                  refine ⟨5612163721307098912402165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7482884961742798549869553 5612163721307098912402165)
                  ·
                    refine ⟨526140348872540523037703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5612163721307098912402165 526140348872540523037703)
                    ·
                      rfl

theorem cell22_1536982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_1536982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536982 prefixEnd_1536982 := by exact prefixLift 1536982
  have htrace : WordTrace (prefixWord ++ tailWord_1536982) baseStart_1536982 baseEnd_1536982 := by
    simpa [prefixWord, tailWord_1536982, baseEnd_1536982] using wordTrace_append hprefix tailTrace_1536982
  have hstable : (prefixWord ++ tailWord_1536982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536982).length < 2 ^ (prefixWord ++ tailWord_1536982).sum := by decide
  have hdescent : baseEnd_1536982 < baseStart_1536982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1536995 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 6]
def baseStart_1536995 : Nat := 118140960795 + 1536995 * 2 ^ 59
def prefixEnd_1536995 : Nat := 4983230072969 + 3 ^ 40 * 1536995 * 2
def baseEnd_1536995 : Nat := 175381599679404274154221

theorem tailTrace_1536995 : CollatzResearch.WordTrace tailWord_1536995 prefixEnd_1536995 175381599679404274154221 := by
  unfold tailWord_1536995
  simp only [CollatzResearch.WordTrace]
  refine ⟨56058813066737087692588439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37372542044491391795058959 56058813066737087692588439)
  ·
    refine ⟨84088219600105631538882659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56058813066737087692588439 84088219600105631538882659)
    ·
      refine ⟨126132329400158447308323989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84088219600105631538882659 126132329400158447308323989)
      ·
        refine ⟨5912452940632427217577687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 126132329400158447308323989 5912452940632427217577687)
        ·
          refine ⟨8868679410948640826366531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5912452940632427217577687 8868679410948640826366531)
          ·
            refine ⟨13303019116422961239549797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8868679410948640826366531 13303019116422961239549797)
            ·
              refine ⟨2494316084329305232415587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13303019116422961239549797 2494316084329305232415587)
              ·
                refine ⟨3741474126493957848623381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2494316084329305232415587 3741474126493957848623381)
                ·
                  refine ⟨175381599679404274154221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3741474126493957848623381 175381599679404274154221)
                  ·
                    rfl

theorem cell22_1536995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 6].length) (baseStart_1536995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1536995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1536995 prefixEnd_1536995 := by exact prefixLift 1536995
  have htrace : WordTrace (prefixWord ++ tailWord_1536995) baseStart_1536995 baseEnd_1536995 := by
    simpa [prefixWord, tailWord_1536995, baseEnd_1536995] using wordTrace_append hprefix tailTrace_1536995
  have hstable : (prefixWord ++ tailWord_1536995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1536995).length < 2 ^ (prefixWord ++ tailWord_1536995).sum := by decide
  have hdescent : baseEnd_1536995 < baseStart_1536995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1536995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537014 : List Nat := [5, 1, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_1537014 : Nat := 118140960795 + 1537014 * 2 ^ 59
def prefixEnd_1537014 : Nat := 4983230072969 + 3 ^ 40 * 1537014 * 2
def baseEnd_1537014 : Nat := 526151303126503106237605

theorem tailTrace_1537014 : CollatzResearch.WordTrace tailWord_1537014 prefixEnd_1537014 526151303126503106237605 := by
  unfold tailWord_1537014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3503719128354265871095631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37373004035778835958353397 3503719128354265871095631)
  ·
    refine ⟨5255578692531398806643447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3503719128354265871095631 5255578692531398806643447)
    ·
      refine ⟨7883368038797098209965171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5255578692531398806643447 7883368038797098209965171)
      ·
        refine ⟨11825052058195647314947757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7883368038797098209965171 11825052058195647314947757)
        ·
          refine ⟨4434394521823367743105409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11825052058195647314947757 4434394521823367743105409)
          ·
            refine ⟨3325795891367525807329057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4434394521823367743105409 3325795891367525807329057)
            ·
              refine ⟨2494346918525644355496793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3325795891367525807329057 2494346918525644355496793)
              ·
                refine ⟨1870760188894233266622595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2494346918525644355496793 1870760188894233266622595)
                ·
                  refine ⟨2806140283341349899933893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1870760188894233266622595 2806140283341349899933893)
                  ·
                    refine ⟨526151303126503106237605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2806140283341349899933893 526151303126503106237605)
                    ·
                      rfl

theorem cell22_1537014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_1537014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537014 prefixEnd_1537014 := by exact prefixLift 1537014
  have htrace : WordTrace (prefixWord ++ tailWord_1537014) baseStart_1537014 baseEnd_1537014 := by
    simpa [prefixWord, tailWord_1537014, baseEnd_1537014] using wordTrace_append hprefix tailTrace_1537014
  have hstable : (prefixWord ++ tailWord_1537014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537014).length < 2 ^ (prefixWord ++ tailWord_1537014).sum := by decide
  have hdescent : baseEnd_1537014 < baseStart_1537014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537025 : List Nat := [1, 2, 4, 1, 2, 2, 2, 1, 1, 6]
def baseStart_1537025 : Nat := 118140960795 + 1537025 * 2 ^ 59
def prefixEnd_1537025 : Nat := 4983230072969 + 3 ^ 40 * 1537025 * 2
def baseEnd_1537025 : Nat := 526155068651302744212571

theorem tailTrace_1537025 : CollatzResearch.WordTrace tailWord_1537025 prefixEnd_1537025 526155068651302744212571 := by
  unfold tailWord_1537025
  simp only [CollatzResearch.WordTrace]
  refine ⟨56059907256628402816180529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37373271504418935210787019 56059907256628402816180529)
  ·
    refine ⟨42044930442471302112135397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56059907256628402816180529 42044930442471302112135397)
    ·
      refine ⟨7883424457963369146025387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42044930442471302112135397 7883424457963369146025387)
      ·
        refine ⟨11825136686945053719038081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7883424457963369146025387 11825136686945053719038081)
        ·
          refine ⟨8868852515208790289278561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11825136686945053719038081 8868852515208790289278561)
          ·
            refine ⟨6651639386406592716958921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8868852515208790289278561 6651639386406592716958921)
            ·
              refine ⟨4988729539804944537719191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6651639386406592716958921 4988729539804944537719191)
              ·
                refine ⟨7483094309707416806578787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4988729539804944537719191 7483094309707416806578787)
                ·
                  refine ⟨11224641464561125209868181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7483094309707416806578787 11224641464561125209868181)
                  ·
                    refine ⟨526155068651302744212571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11224641464561125209868181 526155068651302744212571)
                    ·
                      rfl

theorem cell22_1537025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_1537025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537025 prefixEnd_1537025 := by exact prefixLift 1537025
  have htrace : WordTrace (prefixWord ++ tailWord_1537025) baseStart_1537025 baseEnd_1537025 := by
    simpa [prefixWord, tailWord_1537025, baseEnd_1537025] using wordTrace_append hprefix tailTrace_1537025
  have hstable : (prefixWord ++ tailWord_1537025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537025).length < 2 ^ (prefixWord ++ tailWord_1537025).sum := by decide
  have hdescent : baseEnd_1537025 < baseStart_1537025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537100 : List Nat := [2, 2, 1, 3, 1, 1, 1, 4, 2, 5]
def baseStart_1537100 : Nat := 118140960795 + 1537100 * 2 ^ 59
def prefixEnd_1537100 : Nat := 4983230072969 + 3 ^ 40 * 1537100 * 2
def baseEnd_1537100 : Nat := 526180742684027548587341

theorem tailTrace_1537100 : CollatzResearch.WordTrace tailWord_1537100 prefixEnd_1537100 526180742684027548587341 := by
  unfold tailWord_1537100
  simp only [CollatzResearch.WordTrace]
  refine ⟨28031321365678345312580377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37375095154237793750107169 28031321365678345312580377)
  ·
    refine ⟨21023491024258758984435283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28031321365678345312580377 21023491024258758984435283)
    ·
      refine ⟨31535236536388138476652925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21023491024258758984435283 31535236536388138476652925)
      ·
        refine ⟨11825713701145551928744847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31535236536388138476652925 11825713701145551928744847)
        ·
          refine ⟨17738570551718327893117271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11825713701145551928744847 17738570551718327893117271)
          ·
            refine ⟨26607855827577491839675907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17738570551718327893117271 26607855827577491839675907)
            ·
              refine ⟨39911783741366237759513861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26607855827577491839675907 39911783741366237759513861)
              ·
                refine ⟨7483459451506169579908849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39911783741366237759513861 7483459451506169579908849)
                ·
                  refine ⟨5612594588629627184931637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7483459451506169579908849 5612594588629627184931637)
                  ·
                    refine ⟨526180742684027548587341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5612594588629627184931637 526180742684027548587341)
                    ·
                      rfl

theorem cell22_1537100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_1537100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537100 prefixEnd_1537100 := by exact prefixLift 1537100
  have htrace : WordTrace (prefixWord ++ tailWord_1537100) baseStart_1537100 baseEnd_1537100 := by
    simpa [prefixWord, tailWord_1537100, baseEnd_1537100] using wordTrace_append hprefix tailTrace_1537100
  have hstable : (prefixWord ++ tailWord_1537100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537100).length < 2 ^ (prefixWord ++ tailWord_1537100).sum := by decide
  have hdescent : baseEnd_1537100 < baseStart_1537100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537102 : List Nat := [4, 1, 1, 1, 1, 3, 4, 2, 5]
def baseStart_1537102 : Nat := 118140960795 + 1537102 * 2 ^ 59
def prefixEnd_1537102 : Nat := 4983230072969 + 3 ^ 40 * 1537102 * 2
def baseEnd_1537102 : Nat := 175393809108300070012445

theorem tailTrace_1537102 : CollatzResearch.WordTrace tailWord_1537102 prefixEnd_1537102 175393809108300070012445 := by
  unfold tailWord_1537102
  simp only [CollatzResearch.WordTrace]
  refine ⟨7007839459668680620841695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37375143784899629977822373 7007839459668680620841695)
  ·
    refine ⟨10511759189503020931262543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7007839459668680620841695 10511759189503020931262543)
    ·
      refine ⟨15767638784254531396893815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10511759189503020931262543 15767638784254531396893815)
      ·
        refine ⟨23651458176381797095340723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15767638784254531396893815 23651458176381797095340723)
        ·
          refine ⟨35477187264572695643011085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23651458176381797095340723 35477187264572695643011085)
          ·
            refine ⟨13303945224214760866129157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35477187264572695643011085 13303945224214760866129157)
            ·
              refine ⟨2494489729540267662399217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13303945224214760866129157 2494489729540267662399217)
              ·
                refine ⟨1870867297155200746799413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2494489729540267662399217 1870867297155200746799413)
                ·
                  refine ⟨175393809108300070012445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1870867297155200746799413 175393809108300070012445)
                  ·
                    rfl

theorem cell22_1537102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_1537102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537102 prefixEnd_1537102 := by exact prefixLift 1537102
  have htrace : WordTrace (prefixWord ++ tailWord_1537102) baseStart_1537102 baseEnd_1537102 := by
    simpa [prefixWord, tailWord_1537102, baseEnd_1537102] using wordTrace_append hprefix tailTrace_1537102
  have hstable : (prefixWord ++ tailWord_1537102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537102).length < 2 ^ (prefixWord ++ tailWord_1537102).sum := by decide
  have hdescent : baseEnd_1537102 < baseStart_1537102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537106 : List Nat := [3, 2, 2, 1, 3, 2, 1, 4, 1, 3]
def baseStart_1537106 : Nat := 118140960795 + 1537106 * 2 ^ 59
def prefixEnd_1537106 : Nat := 4983230072969 + 3 ^ 40 * 1537106 * 2
def baseEnd_1537106 : Nat := 526182796606645532937323

theorem tailTrace_1537106 : CollatzResearch.WordTrace tailWord_1537106 prefixEnd_1537106 526182796606645532937323 := by
  unfold tailWord_1537106
  simp only [CollatzResearch.WordTrace]
  refine ⟨14015715392333738412469793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37375241046223302433252781 14015715392333738412469793)
  ·
    refine ⟨10511786544250303809352345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14015715392333738412469793 10511786544250303809352345)
    ·
      refine ⟨7883839908187727857014259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10511786544250303809352345 7883839908187727857014259)
      ·
        refine ⟨11825759862281591785521389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7883839908187727857014259 11825759862281591785521389)
        ·
          refine ⟨4434659948355596919570521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11825759862281591785521389 4434659948355596919570521)
          ·
            refine ⟨3325994961266697689677891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4434659948355596919570521 3325994961266697689677891)
            ·
              refine ⟨4988992441900046534516837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3325994961266697689677891 4988992441900046534516837)
              ·
                refine ⟨935436082856258725221907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4988992441900046534516837 935436082856258725221907)
                ·
                  refine ⟨1403154124284388087832861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 935436082856258725221907 1403154124284388087832861)
                  ·
                    refine ⟨526182796606645532937323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1403154124284388087832861 526182796606645532937323)
                    ·
                      rfl

theorem cell22_1537106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_1537106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537106 prefixEnd_1537106 := by exact prefixLift 1537106
  have htrace : WordTrace (prefixWord ++ tailWord_1537106) baseStart_1537106 baseEnd_1537106 := by
    simpa [prefixWord, tailWord_1537106, baseEnd_1537106] using wordTrace_append hprefix tailTrace_1537106
  have hstable : (prefixWord ++ tailWord_1537106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537106).length < 2 ^ (prefixWord ++ tailWord_1537106).sum := by decide
  have hdescent : baseEnd_1537106 < baseStart_1537106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537132 : List Nat := [2, 2, 1, 1, 3, 2, 2, 4, 1, 4]
def baseStart_1537132 : Nat := 118140960795 + 1537132 * 2 ^ 59
def prefixEnd_1537132 : Nat := 4983230072969 + 3 ^ 40 * 1537132 * 2
def baseEnd_1537132 : Nat := 526191696937990131787243

theorem tailTrace_1537132 : CollatzResearch.WordTrace tailWord_1537132 prefixEnd_1537132 526191696937990131787243 := by
  unfold tailWord_1537132
  simp only [CollatzResearch.WordTrace]
  refine ⟨28031904933620380045162825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37375873244827173393550433 28031904933620380045162825)
  ·
    refine ⟨21023928700215285033872119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28031904933620380045162825 21023928700215285033872119)
    ·
      refine ⟨31535893050322927550808179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21023928700215285033872119 31535893050322927550808179)
      ·
        refine ⟨47303839575484391326212269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31535893050322927550808179 47303839575484391326212269)
        ·
          refine ⟨17738939840806646747329601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47303839575484391326212269 17738939840806646747329601)
          ·
            refine ⟨13304204880604985060497201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17738939840806646747329601 13304204880604985060497201)
            ·
              refine ⟨9978153660453738795372901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13304204880604985060497201 9978153660453738795372901)
              ·
                refine ⟨1870903811335076024132419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9978153660453738795372901 1870903811335076024132419)
                ·
                  refine ⟨2806355717002614036198629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1870903811335076024132419 2806355717002614036198629)
                  ·
                    refine ⟨526191696937990131787243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2806355717002614036198629 526191696937990131787243)
                    ·
                      rfl

theorem cell22_1537132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_1537132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537132 prefixEnd_1537132 := by exact prefixLift 1537132
  have htrace : WordTrace (prefixWord ++ tailWord_1537132) baseStart_1537132 baseEnd_1537132 := by
    simpa [prefixWord, tailWord_1537132, baseEnd_1537132] using wordTrace_append hprefix tailTrace_1537132
  have hstable : (prefixWord ++ tailWord_1537132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537132).length < 2 ^ (prefixWord ++ tailWord_1537132).sum := by decide
  have hdescent : baseEnd_1537132 < baseStart_1537132 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537194 : List Nat := [3, 1, 5, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1537194 : Nat := 118140960795 + 1537194 * 2 ^ 59
def prefixEnd_1537194 : Nat := 4983230072969 + 3 ^ 40 * 1537194 * 2
def baseEnd_1537194 : Nat := 526212920805042636737053

theorem tailTrace_1537194 : CollatzResearch.WordTrace tailWord_1537194 prefixEnd_1537194 526212920805042636737053 := by
  unfold tailWord_1537194
  simp only [CollatzResearch.WordTrace]
  refine ⟨14016517798254036169770659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37377380795344096452721757 14016517798254036169770659)
  ·
    refine ⟨21024776697381054254655989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14016517798254036169770659 21024776697381054254655989)
    ·
      refine ⟨1971072815379473836373999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21024776697381054254655989 1971072815379473836373999)
      ·
        refine ⟨2956609223069210754560999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1971072815379473836373999 2956609223069210754560999)
        ·
          refine ⟨4434913834603816131841499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2956609223069210754560999 4434913834603816131841499)
          ·
            refine ⟨6652370751905724197762249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4434913834603816131841499 6652370751905724197762249)
            ·
              refine ⟨4989278063929293148321687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6652370751905724197762249 4989278063929293148321687)
              ·
                refine ⟨7483917095893939722482531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4989278063929293148321687 7483917095893939722482531)
                ·
                  refine ⟨11225875643840909583723797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7483917095893939722482531 11225875643840909583723797)
                  ·
                    refine ⟨526212920805042636737053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11225875643840909583723797 526212920805042636737053)
                    ·
                      rfl

theorem cell22_1537194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1537194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537194 prefixEnd_1537194 := by exact prefixLift 1537194
  have htrace : WordTrace (prefixWord ++ tailWord_1537194) baseStart_1537194 baseEnd_1537194 := by
    simpa [prefixWord, tailWord_1537194, baseEnd_1537194] using wordTrace_append hprefix tailTrace_1537194
  have hstable : (prefixWord ++ tailWord_1537194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537194).length < 2 ^ (prefixWord ++ tailWord_1537194).sum := by decide
  have hdescent : baseEnd_1537194 < baseStart_1537194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537224 : List Nat := [2, 1, 3, 1, 2, 1, 5, 1, 3, 3]
def baseStart_1537224 : Nat := 118140960795 + 1537224 * 2 ^ 59
def prefixEnd_1537224 : Nat := 4983230072969 + 3 ^ 40 * 1537224 * 2
def baseEnd_1537224 : Nat := 526223190418132558486961

theorem tailTrace_1537224 : CollatzResearch.WordTrace tailWord_1537224 prefixEnd_1537224 526223190418132558486961 := by
  unfold tailWord_1537224
  simp only [CollatzResearch.WordTrace]
  refine ⟨28033582691453729901337363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37378110255271639868449817 28033582691453729901337363)
  ·
    refine ⟨42050374037180594852006045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28033582691453729901337363 42050374037180594852006045)
    ·
      refine ⟨15768890263942723069502267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42050374037180594852006045 15768890263942723069502267)
      ·
        refine ⟨23653335395914084604253401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15768890263942723069502267 23653335395914084604253401)
        ·
          refine ⟨17740001546935563453190051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23653335395914084604253401 17740001546935563453190051)
          ·
            refine ⟨26610002320403345179785077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17740001546935563453190051 26610002320403345179785077)
            ·
              refine ⟨2494687717537813610604851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26610002320403345179785077 2494687717537813610604851)
              ·
                refine ⟨3742031576306720415907277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2494687717537813610604851 3742031576306720415907277)
                ·
                  refine ⟨1403261841115020155965229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3742031576306720415907277 1403261841115020155965229)
                  ·
                    refine ⟨526223190418132558486961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1403261841115020155965229 526223190418132558486961)
                    ·
                      rfl

theorem cell22_1537224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 3, 3].length) (baseStart_1537224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537224 prefixEnd_1537224 := by exact prefixLift 1537224
  have htrace : WordTrace (prefixWord ++ tailWord_1537224) baseStart_1537224 baseEnd_1537224 := by
    simpa [prefixWord, tailWord_1537224, baseEnd_1537224] using wordTrace_append hprefix tailTrace_1537224
  have hstable : (prefixWord ++ tailWord_1537224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537224).length < 2 ^ (prefixWord ++ tailWord_1537224).sum := by decide
  have hdescent : baseEnd_1537224 < baseStart_1537224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537230 : List Nat := [4, 1, 1, 1, 6, 1, 2, 1, 2, 3]
def baseStart_1537230 : Nat := 118140960795 + 1537230 * 2 ^ 59
def prefixEnd_1537230 : Nat := 4983230072969 + 3 ^ 40 * 1537230 * 2
def baseEnd_1537230 : Nat := 526225244340750542836943

theorem tailTrace_1537230 : CollatzResearch.WordTrace tailWord_1537230 prefixEnd_1537230 526225244340750542836943 := by
  unfold tailWord_1537230
  simp only [CollatzResearch.WordTrace]
  refine ⟨7008423027610715353424143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37378256147257148551595429 7008423027610715353424143)
  ·
    refine ⟨10512634541416073030136215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7008423027610715353424143 10512634541416073030136215)
    ·
      refine ⟨15768951812124109545204323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10512634541416073030136215 15768951812124109545204323)
      ·
        refine ⟨23653427718186164317806485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15768951812124109545204323 23653427718186164317806485)
        ·
          refine ⟨1108754424289976452397179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23653427718186164317806485 1108754424289976452397179)
          ·
            refine ⟨1663131636434964678595769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1108754424289976452397179 1663131636434964678595769)
            ·
              refine ⟨1247348727326223508946827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1663131636434964678595769 1247348727326223508946827)
              ·
                refine ⟨1871023090989335263420241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1247348727326223508946827 1871023090989335263420241)
                ·
                  refine ⟨1403267318242001447565181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1871023090989335263420241 1403267318242001447565181)
                  ·
                    refine ⟨526225244340750542836943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1403267318242001447565181 526225244340750542836943)
                    ·
                      rfl

theorem cell22_1537230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_1537230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537230 prefixEnd_1537230 := by exact prefixLift 1537230
  have htrace : WordTrace (prefixWord ++ tailWord_1537230) baseStart_1537230 baseEnd_1537230 := by
    simpa [prefixWord, tailWord_1537230, baseEnd_1537230] using wordTrace_append hprefix tailTrace_1537230
  have hstable : (prefixWord ++ tailWord_1537230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537230).length < 2 ^ (prefixWord ++ tailWord_1537230).sum := by decide
  have hdescent : baseEnd_1537230 < baseStart_1537230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537284 : List Nat := [2, 3, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_1537284 : Nat := 118140960795 + 1537284 * 2 ^ 59
def prefixEnd_1537284 : Nat := 4983230072969 + 3 ^ 40 * 1537284 * 2
def baseEnd_1537284 : Nat := 526243729644312401986777

theorem tailTrace_1537284 : CollatzResearch.WordTrace tailWord_1537284 prefixEnd_1537284 526243729644312401986777 := by
  unfold tailWord_1537284
  simp only [CollatzResearch.WordTrace]
  refine ⟨28034676881345045024929453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37379569175126726699905937 28034676881345045024929453)
  ·
    refine ⟨10513003830504391884348545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28034676881345045024929453 10513003830504391884348545)
    ·
      refine ⟨7884752872878293913261409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10513003830504391884348545 7884752872878293913261409)
      ·
        refine ⟨5913564654658720434946057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7884752872878293913261409 5913564654658720434946057)
        ·
          refine ⟨4435173490994040326209543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5913564654658720434946057 4435173490994040326209543)
          ·
            refine ⟨6652760236491060489314315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4435173490994040326209543 6652760236491060489314315)
            ·
              refine ⟨9979140354736590733971473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6652760236491060489314315 9979140354736590733971473)
              ·
                refine ⟨7484355266052443050478605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9979140354736590733971473 7484355266052443050478605)
                ·
                  refine ⟨2806633224769666143929477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7484355266052443050478605 2806633224769666143929477)
                  ·
                    refine ⟨526243729644312401986777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2806633224769666143929477 526243729644312401986777)
                    ·
                      rfl

theorem cell22_1537284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_1537284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537284 prefixEnd_1537284 := by exact prefixLift 1537284
  have htrace : WordTrace (prefixWord ++ tailWord_1537284) baseStart_1537284 baseEnd_1537284 := by
    simpa [prefixWord, tailWord_1537284, baseEnd_1537284] using wordTrace_append hprefix tailTrace_1537284
  have hstable : (prefixWord ++ tailWord_1537284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537284).length < 2 ^ (prefixWord ++ tailWord_1537284).sum := by decide
  have hdescent : baseEnd_1537284 < baseStart_1537284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537316 : List Nat := [2, 3, 1, 3, 1, 1, 4, 3, 4]
def baseStart_1537316 : Nat := 118140960795 + 1537316 * 2 ^ 59
def prefixEnd_1537316 : Nat := 4983230072969 + 3 ^ 40 * 1537316 * 2
def baseEnd_1537316 : Nat := 175418227966091661728893

theorem tailTrace_1537316 : CollatzResearch.WordTrace tailWord_1537316 prefixEnd_1537316 175418227966091661728893 := by
  unfold tailWord_1537316
  simp only [CollatzResearch.WordTrace]
  refine ⟨28035260449287079757511901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37380347265716106343349201 28035260449287079757511901)
  ·
    refine ⟨10513222668482654909066963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28035260449287079757511901 10513222668482654909066963)
    ·
      refine ⟨15769834002723982363600445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10513222668482654909066963 15769834002723982363600445)
      ·
        refine ⟨5913687751021493386350167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15769834002723982363600445 5913687751021493386350167)
        ·
          refine ⟨8870531626532240079525251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5913687751021493386350167 8870531626532240079525251)
          ·
            refine ⟨13305797439798360119287877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8870531626532240079525251 13305797439798360119287877)
            ·
              refine ⟨2494837019962192522366477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13305797439798360119287877 2494837019962192522366477)
              ·
                refine ⟨935563882485822195887429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2494837019962192522366477 935563882485822195887429)
                ·
                  refine ⟨175418227966091661728893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 935563882485822195887429 175418227966091661728893)
                  ·
                    rfl

theorem cell22_1537316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_1537316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537316 prefixEnd_1537316 := by exact prefixLift 1537316
  have htrace : WordTrace (prefixWord ++ tailWord_1537316) baseStart_1537316 baseEnd_1537316 := by
    simpa [prefixWord, tailWord_1537316, baseEnd_1537316] using wordTrace_append hprefix tailTrace_1537316
  have hstable : (prefixWord ++ tailWord_1537316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537316).length < 2 ^ (prefixWord ++ tailWord_1537316).sum := by decide
  have hdescent : baseEnd_1537316 < baseStart_1537316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537331 : List Nat := [1, 1, 1, 2, 5, 2, 3, 2, 2, 3]
def baseStart_1537331 : Nat := 118140960795 + 1537331 * 2 ^ 59
def prefixEnd_1537331 : Nat := 4983230072969 + 3 ^ 40 * 1537331 * 2
def baseEnd_1537331 : Nat := 526259818704819946061633

theorem tailTrace_1537331 : CollatzResearch.WordTrace tailWord_1537331 prefixEnd_1537331 526259818704819946061633 := by
  unfold tailWord_1537331
  simp only [CollatzResearch.WordTrace]
  refine ⟨56071067993519817076819847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37380711995679878051213231 56071067993519817076819847)
  ·
    refine ⟨84106601990279725615229771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56071067993519817076819847 84106601990279725615229771)
    ·
      refine ⟨126159902985419588422844657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84106601990279725615229771 126159902985419588422844657)
      ·
        refine ⟨94619927239064691317133493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126159902985419588422844657 94619927239064691317133493)
        ·
          refine ⟨8870618178662314810981265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94619927239064691317133493 8870618178662314810981265)
          ·
            refine ⟨6652963633996736108235949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8870618178662314810981265 6652963633996736108235949)
            ·
              refine ⟨2494861362748776040588481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6652963633996736108235949 2494861362748776040588481)
              ·
                refine ⟨1871146022061582030441361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2494861362748776040588481 1871146022061582030441361)
                ·
                  refine ⟨1403359516546186522831021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1871146022061582030441361 1403359516546186522831021)
                  ·
                    refine ⟨526259818704819946061633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1403359516546186522831021 526259818704819946061633)
                    ·
                      rfl

theorem cell22_1537331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 2, 2, 3].length) (baseStart_1537331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537331 prefixEnd_1537331 := by exact prefixLift 1537331
  have htrace : WordTrace (prefixWord ++ tailWord_1537331) baseStart_1537331 baseEnd_1537331 := by
    simpa [prefixWord, tailWord_1537331, baseEnd_1537331] using wordTrace_append hprefix tailTrace_1537331
  have hstable : (prefixWord ++ tailWord_1537331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537331).length < 2 ^ (prefixWord ++ tailWord_1537331).sum := by decide
  have hdescent : baseEnd_1537331 < baseStart_1537331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537348 : List Nat := [2, 3, 4, 1, 1, 3, 1, 1, 1, 5]
def baseStart_1537348 : Nat := 118140960795 + 1537348 * 2 ^ 59
def prefixEnd_1537348 : Nat := 4983230072969 + 3 ^ 40 * 1537348 * 2
def baseEnd_1537348 : Nat := 526265638152237568386581

theorem tailTrace_1537348 : CollatzResearch.WordTrace tailWord_1537348 prefixEnd_1537348 526265638152237568386581 := by
  unfold tailWord_1537348
  simp only [CollatzResearch.WordTrace]
  refine ⟨28035844017229114490094349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37381125356305485986792465 28035844017229114490094349)
  ·
    refine ⟨10513441506460917933785381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28035844017229114490094349 10513441506460917933785381)
    ·
      refine ⟨1971270282461422112584759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10513441506460917933785381 1971270282461422112584759)
      ·
        refine ⟨2956905423692133168877139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1971270282461422112584759 2956905423692133168877139)
        ·
          refine ⟨4435358135538199753315709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2956905423692133168877139 4435358135538199753315709)
          ·
            refine ⟨1663259300826824907493391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4435358135538199753315709 1663259300826824907493391)
            ·
              refine ⟨2494888951240237361240087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663259300826824907493391 2494888951240237361240087)
              ·
                refine ⟨3742333426860356041860131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2494888951240237361240087 3742333426860356041860131)
                ·
                  refine ⟨5613500140290534062790197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3742333426860356041860131 5613500140290534062790197)
                  ·
                    refine ⟨526265638152237568386581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5613500140290534062790197 526265638152237568386581)
                    ·
                      rfl

theorem cell22_1537348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_1537348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537348 prefixEnd_1537348 := by exact prefixLift 1537348
  have htrace : WordTrace (prefixWord ++ tailWord_1537348) baseStart_1537348 baseEnd_1537348 := by
    simpa [prefixWord, tailWord_1537348, baseEnd_1537348] using wordTrace_append hprefix tailTrace_1537348
  have hstable : (prefixWord ++ tailWord_1537348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537348).length < 2 ^ (prefixWord ++ tailWord_1537348).sum := by decide
  have hdescent : baseEnd_1537348 < baseStart_1537348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537389 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 7]
def baseStart_1537389 : Nat := 118140960795 + 1537389 * 2 ^ 59
def prefixEnd_1537389 : Nat := 4983230072969 + 3 ^ 40 * 1537389 * 2
def baseEnd_1537389 : Nat := 175426557763375709370485

theorem tailTrace_1537389 : CollatzResearch.WordTrace tailWord_1537389 prefixEnd_1537389 175426557763375709370485 := by
  unfold tailWord_1537389
  simp only [CollatzResearch.WordTrace]
  refine ⟨56073183427309692982431221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37382122284873128654954147 56073183427309692982431221)
  ·
    refine ⟨5256860946310283717102927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56073183427309692982431221 5256860946310283717102927)
    ·
      refine ⟨7885291419465425575654391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5256860946310283717102927 7885291419465425575654391)
      ·
        refine ⟨11827937129198138363481587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7885291419465425575654391 11827937129198138363481587)
        ·
          refine ⟨17741905693797207545222381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11827937129198138363481587 17741905693797207545222381)
          ·
            refine ⟨6653214635173952829458393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17741905693797207545222381 6653214635173952829458393)
            ·
              refine ⟨4989910976380464622093795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6653214635173952829458393 4989910976380464622093795)
              ·
                refine ⟨7484866464570696933140693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4989910976380464622093795 7484866464570696933140693)
                ·
                  refine ⟨175426557763375709370485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7484866464570696933140693 175426557763375709370485)
                  ·
                    rfl

theorem cell22_1537389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_1537389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537389 prefixEnd_1537389 := by exact prefixLift 1537389
  have htrace : WordTrace (prefixWord ++ tailWord_1537389) baseStart_1537389 baseEnd_1537389 := by
    simpa [prefixWord, tailWord_1537389, baseEnd_1537389] using wordTrace_append hprefix tailTrace_1537389
  have hstable : (prefixWord ++ tailWord_1537389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537389).length < 2 ^ (prefixWord ++ tailWord_1537389).sum := by decide
  have hdescent : baseEnd_1537389 < baseStart_1537389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537419 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 3, 4]
def baseStart_1537419 : Nat := 118140960795 + 1537419 * 2 ^ 59
def prefixEnd_1537419 : Nat := 4983230072969 + 3 ^ 40 * 1537419 * 2
def baseEnd_1537419 : Nat := 526289942903217049861363

theorem tailTrace_1537419 : CollatzResearch.WordTrace tailWord_1537419 prefixEnd_1537419 526289942903217049861363 := by
  unfold tailWord_1537419
  simp only [CollatzResearch.WordTrace]
  refine ⟨56074277617201008106023311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37382851744800672070682207 56074277617201008106023311)
  ·
    refine ⟨84111416425801512159034967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56074277617201008106023311 84111416425801512159034967)
    ·
      refine ⟨126167124638702268238552451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84111416425801512159034967 126167124638702268238552451)
      ·
        refine ⟨189250686958053402357828677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126167124638702268238552451 189250686958053402357828677)
        ·
          refine ⟨35484503804635012942092877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 189250686958053402357828677 35484503804635012942092877)
          ·
            refine ⟨13306688926738129853284829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35484503804635012942092877 13306688926738129853284829)
            ·
              refine ⟨4990008347526798694981811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13306688926738129853284829 4990008347526798694981811)
              ·
                refine ⟨7485012521290198042472717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4990008347526798694981811 7485012521290198042472717)
                ·
                  refine ⟨2806879695483824265927269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7485012521290198042472717 2806879695483824265927269)
                  ·
                    refine ⟨526289942903217049861363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2806879695483824265927269 526289942903217049861363)
                    ·
                      rfl

theorem cell22_1537419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 3, 4].length) (baseStart_1537419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537419 prefixEnd_1537419 := by exact prefixLift 1537419
  have htrace : WordTrace (prefixWord ++ tailWord_1537419) baseStart_1537419 baseEnd_1537419 := by
    simpa [prefixWord, tailWord_1537419, baseEnd_1537419] using wordTrace_append hprefix tailTrace_1537419
  have hstable : (prefixWord ++ tailWord_1537419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537419).length < 2 ^ (prefixWord ++ tailWord_1537419).sum := by decide
  have hdescent : baseEnd_1537419 < baseStart_1537419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537464 : List Nat := [2, 1, 2, 1, 2, 2, 2, 2, 4, 4]
def baseStart_1537464 : Nat := 118140960795 + 1537464 * 2 ^ 59
def prefixEnd_1537464 : Nat := 4983230072969 + 3 ^ 40 * 1537464 * 2
def baseEnd_1537464 : Nat := 526305347322851932486225

theorem tailTrace_1537464 : CollatzResearch.WordTrace tailWord_1537464 prefixEnd_1537464 526305347322851932486225 := by
  unfold tailWord_1537464
  simp only [CollatzResearch.WordTrace]
  refine ⟨28037959451018990395705723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37383945934691987194274297 28037959451018990395705723)
  ·
    refine ⟨42056939176528485593558585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28037959451018990395705723 42056939176528485593558585)
    ·
      refine ⟨31542704382396364195168939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42056939176528485593558585 31542704382396364195168939)
      ·
        refine ⟨47314056573594546292753409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31542704382396364195168939 47314056573594546292753409)
        ·
          refine ⟨35485542430195909719565057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47314056573594546292753409 35485542430195909719565057)
          ·
            refine ⟨26614156822646932289673793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35485542430195909719565057 26614156822646932289673793)
            ·
              refine ⟨19960617616985199217255345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26614156822646932289673793 19960617616985199217255345)
              ·
                refine ⟨14970463212738899412941509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19960617616985199217255345 14970463212738899412941509)
                ·
                  refine ⟨2806961852388543639926533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14970463212738899412941509 2806961852388543639926533)
                  ·
                    refine ⟨526305347322851932486225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2806961852388543639926533 526305347322851932486225)
                    ·
                      rfl

theorem cell22_1537464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 2, 4, 4].length) (baseStart_1537464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537464 prefixEnd_1537464 := by exact prefixLift 1537464
  have htrace : WordTrace (prefixWord ++ tailWord_1537464) baseStart_1537464 baseEnd_1537464 := by
    simpa [prefixWord, tailWord_1537464, baseEnd_1537464] using wordTrace_append hprefix tailTrace_1537464
  have hstable : (prefixWord ++ tailWord_1537464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537464).length < 2 ^ (prefixWord ++ tailWord_1537464).sum := by decide
  have hdescent : baseEnd_1537464 < baseStart_1537464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537517 : List Nat := [1, 5, 1, 3, 2, 1, 3, 1, 2, 3]
def baseStart_1537517 : Nat := 118140960795 + 1537517 * 2 ^ 59
def prefixEnd_1537517 : Nat := 4983230072969 + 3 ^ 40 * 1537517 * 2
def baseEnd_1537517 : Nat := 526323490305977460911063

theorem tailTrace_1537517 : CollatzResearch.WordTrace tailWord_1537517 prefixEnd_1537517 526323490305977460911063 := by
  unfold tailWord_1537517
  simp only [CollatzResearch.WordTrace]
  refine ⟨56077851970845970843090805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37385234647230647228727203 56077851970845970843090805)
  ·
    refine ⟨5257298622266809766539763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56077851970845970843090805 5257298622266809766539763)
    ·
      refine ⟨7885947933400214649809645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5257298622266809766539763 7885947933400214649809645)
      ·
        refine ⟨2957230475025080493678617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7885947933400214649809645 2957230475025080493678617)
        ·
          refine ⟨2217922856268810370258963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2957230475025080493678617 2217922856268810370258963)
          ·
            refine ⟨3326884284403215555388445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2217922856268810370258963 3326884284403215555388445)
            ·
              refine ⟨1247581606651205833270667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3326884284403215555388445 1247581606651205833270667)
              ·
                refine ⟨1871372409976808749906001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1247581606651205833270667 1871372409976808749906001)
                ·
                  refine ⟨1403529307482606562429501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1871372409976808749906001 1403529307482606562429501)
                  ·
                    refine ⟨526323490305977460911063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1403529307482606562429501 526323490305977460911063)
                    ·
                      rfl

theorem cell22_1537517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_1537517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537517 prefixEnd_1537517 := by exact prefixLift 1537517
  have htrace : WordTrace (prefixWord ++ tailWord_1537517) baseStart_1537517 baseEnd_1537517 := by
    simpa [prefixWord, tailWord_1537517, baseEnd_1537517] using wordTrace_append hprefix tailTrace_1537517
  have hstable : (prefixWord ++ tailWord_1537517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537517).length < 2 ^ (prefixWord ++ tailWord_1537517).sum := by decide
  have hdescent : baseEnd_1537517 < baseStart_1537517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537539 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 4, 5]
def baseStart_1537539 : Nat := 118140960795 + 1537539 * 2 ^ 59
def prefixEnd_1537539 : Nat := 4983230072969 + 3 ^ 40 * 1537539 * 2
def baseEnd_1537539 : Nat := 526331021355576736860995

theorem tailTrace_1537539 : CollatzResearch.WordTrace tailWord_1537539 prefixEnd_1537539 526331021355576736860995 := by
  unfold tailWord_1537539
  simp only [CollatzResearch.WordTrace]
  refine ⟨56078654376766268600391671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37385769584510845733594447 56078654376766268600391671)
  ·
    refine ⟨84117981565149402900587507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56078654376766268600391671 84117981565149402900587507)
    ·
      refine ⟨126176972347724104350881261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84117981565149402900587507 126176972347724104350881261)
      ·
        refine ⟨47316364630396539131580473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126176972347724104350881261 47316364630396539131580473)
        ·
          refine ⟨35487273472797404348685355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47316364630396539131580473 35487273472797404348685355)
          ·
            refine ⟨53230910209196106523028033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35487273472797404348685355 53230910209196106523028033)
            ·
              refine ⟨39923182656897079892271025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53230910209196106523028033 39923182656897079892271025)
              ·
                refine ⟨29942386992672809919203269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39923182656897079892271025 29942386992672809919203269)
                ·
                  refine ⟨5614197561126151859850613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29942386992672809919203269 5614197561126151859850613)
                  ·
                    refine ⟨526331021355576736860995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5614197561126151859850613 526331021355576736860995)
                    ·
                      rfl

theorem cell22_1537539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 4, 5].length) (baseStart_1537539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537539 prefixEnd_1537539 := by exact prefixLift 1537539
  have htrace : WordTrace (prefixWord ++ tailWord_1537539) baseStart_1537539 baseEnd_1537539 := by
    simpa [prefixWord, tailWord_1537539, baseEnd_1537539] using wordTrace_append hprefix tailTrace_1537539
  have hstable : (prefixWord ++ tailWord_1537539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537539).length < 2 ^ (prefixWord ++ tailWord_1537539).sum := by decide
  have hdescent : baseEnd_1537539 < baseStart_1537539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537616 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 2, 4]
def baseStart_1537616 : Nat := 118140960795 + 1537616 * 2 ^ 59
def prefixEnd_1537616 : Nat := 4983230072969 + 3 ^ 40 * 1537616 * 2
def baseEnd_1537616 : Nat := 526357380029174202685759

theorem tailTrace_1537616 : CollatzResearch.WordTrace tailWord_1537616 prefixEnd_1537616 526357380029174202685759 := by
  unfold tailWord_1537616
  simp only [CollatzResearch.WordTrace]
  refine ⟨28040731398743655375472351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37387641864991540500629801 28040731398743655375472351)
  ·
    refine ⟨42061097098115483063208527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28040731398743655375472351 42061097098115483063208527)
    ·
      refine ⟨63091645647173224594812791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42061097098115483063208527 63091645647173224594812791)
      ·
        refine ⟨94637468470759836892219187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63091645647173224594812791 94637468470759836892219187)
        ·
          refine ⟨141956202706139755338328781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94637468470759836892219187 141956202706139755338328781)
          ·
            refine ⟨53233576014802408251873293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 141956202706139755338328781 53233576014802408251873293)
            ·
              refine ⟨19962591005550903094452485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53233576014802408251873293 19962591005550903094452485)
              ·
                refine ⟨3742985813540794330209841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19962591005550903094452485 3742985813540794330209841)
                ·
                  refine ⟨2807239360155595747657381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3742985813540794330209841 2807239360155595747657381)
                  ·
                    refine ⟨526357380029174202685759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2807239360155595747657381 526357380029174202685759)
                    ·
                      rfl

theorem cell22_1537616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 2, 4].length) (baseStart_1537616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537616 prefixEnd_1537616 := by exact prefixLift 1537616
  have htrace : WordTrace (prefixWord ++ tailWord_1537616) baseStart_1537616 baseEnd_1537616 := by
    simpa [prefixWord, tailWord_1537616, baseEnd_1537616] using wordTrace_append hprefix tailTrace_1537616
  have hstable : (prefixWord ++ tailWord_1537616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537616).length < 2 ^ (prefixWord ++ tailWord_1537616).sum := by decide
  have hdescent : baseEnd_1537616 < baseStart_1537616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537648 : List Nat := [2, 1, 1, 1, 6, 2, 3, 6]
def baseStart_1537648 : Nat := 118140960795 + 1537648 * 2 ^ 59
def prefixEnd_1537648 : Nat := 4983230072969 + 3 ^ 40 * 1537648 * 2
def baseEnd_1537648 : Nat := 58485370475904087320629

theorem tailTrace_1537648 : CollatzResearch.WordTrace tailWord_1537648 prefixEnd_1537648 58485370475904087320629 := by
  unfold tailWord_1537648
  simp only [CollatzResearch.WordTrace]
  refine ⟨28041314966685690108054799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37388419955580920144073065 28041314966685690108054799)
  ·
    refine ⟨42061972450028535162082199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28041314966685690108054799 42061972450028535162082199)
    ·
      refine ⟨63092958675042802743123299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42061972450028535162082199 63092958675042802743123299)
      ·
        refine ⟨94639438012564204114684949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63092958675042802743123299 94639438012564204114684949)
        ·
          refine ⟨4436223656838947067875857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 94639438012564204114684949 4436223656838947067875857)
          ·
            refine ⟨3327167742629210300906893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4436223656838947067875857 3327167742629210300906893)
            ·
              refine ⟨1247687903485953862840085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3327167742629210300906893 1247687903485953862840085)
              ·
                refine ⟨58485370475904087320629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1247687903485953862840085 58485370475904087320629)
                ·
                  rfl

theorem cell22_1537648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 3, 6].length) (baseStart_1537648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537648 prefixEnd_1537648 := by exact prefixLift 1537648
  have htrace : WordTrace (prefixWord ++ tailWord_1537648) baseStart_1537648 baseEnd_1537648 := by
    simpa [prefixWord, tailWord_1537648, baseEnd_1537648] using wordTrace_append hprefix tailTrace_1537648
  have hstable : (prefixWord ++ tailWord_1537648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537648).length < 2 ^ (prefixWord ++ tailWord_1537648).sum := by decide
  have hdescent : baseEnd_1537648 < baseStart_1537648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537650 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 2, 4]
def baseStart_1537650 : Nat := 118140960795 + 1537650 * 2 ^ 59
def prefixEnd_1537650 : Nat := 4983230072969 + 3 ^ 40 * 1537650 * 2
def baseEnd_1537650 : Nat := 526369018924009447335655

theorem tailTrace_1537650 : CollatzResearch.WordTrace tailWord_1537650 prefixEnd_1537650 526369018924009447335655 := by
  unfold tailWord_1537650
  simp only [CollatzResearch.WordTrace]
  refine ⟨14020675719841033639420601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37388468586242756371788269 14020675719841033639420601)
  ·
    refine ⟨10515506789880775229565451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14020675719841033639420601 10515506789880775229565451)
    ·
      refine ⟨15773260184821162844348177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10515506789880775229565451 15773260184821162844348177)
      ·
        refine ⟨11829945138615872133261133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15773260184821162844348177 11829945138615872133261133)
        ·
          refine ⟨4436229426980952049972925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11829945138615872133261133 4436229426980952049972925)
          ·
            refine ⟨1663586035117857018739847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4436229426980952049972925 1663586035117857018739847)
            ·
              refine ⟨2495379052676785528109771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1663586035117857018739847 2495379052676785528109771)
              ·
                refine ⟨3743068579015178292164657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495379052676785528109771 3743068579015178292164657)
                ·
                  refine ⟨2807301434261383719123493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3743068579015178292164657 2807301434261383719123493)
                  ·
                    refine ⟨526369018924009447335655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2807301434261383719123493 526369018924009447335655)
                    ·
                      rfl

theorem cell22_1537650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_1537650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537650 prefixEnd_1537650 := by exact prefixLift 1537650
  have htrace : WordTrace (prefixWord ++ tailWord_1537650) baseStart_1537650 baseEnd_1537650 := by
    simpa [prefixWord, tailWord_1537650, baseEnd_1537650] using wordTrace_append hprefix tailTrace_1537650
  have hstable : (prefixWord ++ tailWord_1537650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537650).length < 2 ^ (prefixWord ++ tailWord_1537650).sum := by decide
  have hdescent : baseEnd_1537650 < baseStart_1537650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537676 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 7]
def baseStart_1537676 : Nat := 118140960795 + 1537676 * 2 ^ 59
def prefixEnd_1537676 : Nat := 4983230072969 + 3 ^ 40 * 1537676 * 2
def baseEnd_1537676 : Nat := 175459306418451348728525

theorem tailTrace_1537676 : CollatzResearch.WordTrace tailWord_1537676 prefixEnd_1537676 175459306418451348728525 := by
  unfold tailWord_1537676
  simp only [CollatzResearch.WordTrace]
  refine ⟨28041825588634970499064441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37389100784846627332085921 28041825588634970499064441)
  ·
    refine ⟨21031369191476227874298331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28041825588634970499064441 21031369191476227874298331)
    ·
      refine ⟨31547053787214341811447497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21031369191476227874298331 31547053787214341811447497)
      ·
        refine ⟨23660290340410756358585623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31547053787214341811447497 23660290340410756358585623)
        ·
          refine ⟨35490435510616134537878435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23660290340410756358585623 35490435510616134537878435)
          ·
            refine ⟨53235653265924201806817653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35490435510616134537878435 53235653265924201806817653)
            ·
              refine ⟨4990842493680393919389155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 53235653265924201806817653 4990842493680393919389155)
              ·
                refine ⟨7486263740520590879083733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4990842493680393919389155 7486263740520590879083733)
                ·
                  refine ⟨175459306418451348728525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7486263740520590879083733 175459306418451348728525)
                  ·
                    rfl

theorem cell22_1537676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_1537676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537676 prefixEnd_1537676 := by exact prefixLift 1537676
  have htrace : WordTrace (prefixWord ++ tailWord_1537676) baseStart_1537676 baseEnd_1537676 := by
    simpa [prefixWord, tailWord_1537676, baseEnd_1537676] using wordTrace_append hprefix tailTrace_1537676
  have hstable : (prefixWord ++ tailWord_1537676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537676).length < 2 ^ (prefixWord ++ tailWord_1537676).sum := by decide
  have hdescent : baseEnd_1537676 < baseStart_1537676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537721 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 8]
def baseStart_1537721 : Nat := 118140960795 + 1537721 * 2 ^ 59
def prefixEnd_1537721 : Nat := 4983230072969 + 3 ^ 40 * 1537721 * 2
def baseEnd_1537721 : Nat := 175464441224996309603479

theorem tailTrace_1537721 : CollatzResearch.WordTrace tailWord_1537721 prefixEnd_1537721 175464441224996309603479 := by
  unfold tailWord_1537721
  simp only [CollatzResearch.WordTrace]
  refine ⟨56085292462106913683517017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37390194974737942455678011 56085292462106913683517017)
  ·
    refine ⟨42063969346580185262637763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56085292462106913683517017 42063969346580185262637763)
    ·
      refine ⟨63095954019870277893956645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42063969346580185262637763 63095954019870277893956645)
      ·
        refine ⟨11830491378725677105116871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63095954019870277893956645 11830491378725677105116871)
        ·
          refine ⟨17745737068088515657675307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11830491378725677105116871 17745737068088515657675307)
          ·
            refine ⟨26618605602132773486512961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17745737068088515657675307 26618605602132773486512961)
            ·
              refine ⟨19963954201599580114884721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26618605602132773486512961 19963954201599580114884721)
              ·
                refine ⟨14972965651199685086163541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19963954201599580114884721 14972965651199685086163541)
                ·
                  refine ⟨175464441224996309603479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14972965651199685086163541 175464441224996309603479)
                  ·
                    rfl

theorem cell22_1537721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 8].length) (baseStart_1537721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537721 prefixEnd_1537721 := by exact prefixLift 1537721
  have htrace : WordTrace (prefixWord ++ tailWord_1537721) baseStart_1537721 baseEnd_1537721 := by
    simpa [prefixWord, tailWord_1537721, baseEnd_1537721] using wordTrace_append hprefix tailTrace_1537721
  have hstable : (prefixWord ++ tailWord_1537721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537721).length < 2 ^ (prefixWord ++ tailWord_1537721).sum := by decide
  have hdescent : baseEnd_1537721 < baseStart_1537721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537757 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 3, 4]
def baseStart_1537757 : Nat := 118140960795 + 1537757 * 2 ^ 59
def prefixEnd_1537757 : Nat := 4983230072969 + 3 ^ 40 * 1537757 * 2
def baseEnd_1537757 : Nat := 526405647210696834910327

theorem tailTrace_1537757 : CollatzResearch.WordTrace tailWord_1537757 prefixEnd_1537757 526405647210696834910327 := by
  unfold tailWord_1537757
  simp only [CollatzResearch.WordTrace]
  refine ⟨56086605489976491831827525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37391070326650994554551683 56086605489976491831827525)
  ·
    refine ⟨10516238529370592218467661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56086605489976491831827525 10516238529370592218467661)
    ·
      refine ⟨3943589448513972081925373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10516238529370592218467661 3943589448513972081925373)
      ·
        refine ⟨1478846043192739530722015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3943589448513972081925373 1478846043192739530722015)
        ·
          refine ⟨2218269064789109296083023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478846043192739530722015 2218269064789109296083023)
          ·
            refine ⟨3327403597183663944124535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218269064789109296083023 3327403597183663944124535)
            ·
              refine ⟨4991105395775495916186803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327403597183663944124535 4991105395775495916186803)
              ·
                refine ⟨7486658093663243874280205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4991105395775495916186803 7486658093663243874280205)
                ·
                  refine ⟨2807496785123716452855077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7486658093663243874280205 2807496785123716452855077)
                  ·
                    refine ⟨526405647210696834910327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2807496785123716452855077 526405647210696834910327)
                    ·
                      rfl

theorem cell22_1537757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_1537757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537757 prefixEnd_1537757 := by exact prefixLift 1537757
  have htrace : WordTrace (prefixWord ++ tailWord_1537757) baseStart_1537757 baseEnd_1537757 := by
    simpa [prefixWord, tailWord_1537757, baseEnd_1537757] using wordTrace_append hprefix tailTrace_1537757
  have hstable : (prefixWord ++ tailWord_1537757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537757).length < 2 ^ (prefixWord ++ tailWord_1537757).sum := by decide
  have hdescent : baseEnd_1537757 < baseStart_1537757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537815 : List Nat := [1, 1, 3, 4, 2, 1, 1, 1, 5, 3]
def baseStart_1537815 : Nat := 118140960795 + 1537815 * 2 ^ 59
def prefixEnd_1537815 : Nat := 4983230072969 + 3 ^ 40 * 1537815 * 2
def baseEnd_1537815 : Nat := 526425501796004016960149

theorem tailTrace_1537815 : CollatzResearch.WordTrace tailWord_1537815 prefixEnd_1537815 526425501796004016960149 := by
  unfold tailWord_1537815
  simp only [CollatzResearch.WordTrace]
  refine ⟨56088720923766367737438899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37392480615844245158292599 56088720923766367737438899)
  ·
    refine ⟨84133081385649551606158349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56088720923766367737438899 84133081385649551606158349)
    ·
      refine ⟨31549905519618581852309381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84133081385649551606158349 31549905519618581852309381)
      ·
        refine ⟨5915607284928484097308009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31549905519618581852309381 5915607284928484097308009)
        ·
          refine ⟨4436705463696363072981007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5915607284928484097308009 4436705463696363072981007)
          ·
            refine ⟨6655058195544544609471511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4436705463696363072981007 6655058195544544609471511)
            ·
              refine ⟨9982587293316816914207267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6655058195544544609471511 9982587293316816914207267)
              ·
                refine ⟨14973880939975225371310901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9982587293316816914207267 14973880939975225371310901)
                ·
                  refine ⟨1403801338122677378560397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14973880939975225371310901 1403801338122677378560397)
                  ·
                    refine ⟨526425501796004016960149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1403801338122677378560397 526425501796004016960149)
                    ·
                      rfl

theorem cell22_1537815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_1537815 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537815 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537815 prefixEnd_1537815 := by exact prefixLift 1537815
  have htrace : WordTrace (prefixWord ++ tailWord_1537815) baseStart_1537815 baseEnd_1537815 := by
    simpa [prefixWord, tailWord_1537815, baseEnd_1537815] using wordTrace_append hprefix tailTrace_1537815
  have hstable : (prefixWord ++ tailWord_1537815).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537815).length < 2 ^ (prefixWord ++ tailWord_1537815).sum := by decide
  have hdescent : baseEnd_1537815 < baseStart_1537815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537845 : List Nat := [1, 3, 3, 1, 4, 1, 1, 1, 7]
def baseStart_1537845 : Nat := 118140960795 + 1537845 * 2 ^ 59
def prefixEnd_1537845 : Nat := 4983230072969 + 3 ^ 40 * 1537845 * 2
def baseEnd_1537845 : Nat := 175478590469697979570019

theorem tailTrace_1537845 : CollatzResearch.WordTrace tailWord_1537845 prefixEnd_1537845 175478590469697979570019 := by
  unfold tailWord_1537845
  simp only [CollatzResearch.WordTrace]
  refine ⟨56089815113657682861030989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37393210075771788574020659 56089815113657682861030989)
  ·
    refine ⟨21033680667621631072886621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56089815113657682861030989 21033680667621631072886621)
    ·
      refine ⟨7887630250358111652332483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21033680667621631072886621 7887630250358111652332483)
      ·
        refine ⟨11831445375537167478498725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7887630250358111652332483 11831445375537167478498725)
        ·
          refine ⟨2218396007913218902218511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11831445375537167478498725 2218396007913218902218511)
          ·
            refine ⟨3327594011869828353327767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218396007913218902218511 3327594011869828353327767)
            ·
              refine ⟨4991391017804742529991651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3327594011869828353327767 4991391017804742529991651)
              ·
                refine ⟨7487086526707113794987477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4991391017804742529991651 7487086526707113794987477)
                ·
                  refine ⟨175478590469697979570019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7487086526707113794987477 175478590469697979570019)
                  ·
                    rfl

theorem cell22_1537845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_1537845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537845 prefixEnd_1537845 := by exact prefixLift 1537845
  have htrace : WordTrace (prefixWord ++ tailWord_1537845) baseStart_1537845 baseEnd_1537845 := by
    simpa [prefixWord, tailWord_1537845, baseEnd_1537845] using wordTrace_append hprefix tailTrace_1537845
  have hstable : (prefixWord ++ tailWord_1537845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537845).length < 2 ^ (prefixWord ++ tailWord_1537845).sum := by decide
  have hdescent : baseEnd_1537845 < baseStart_1537845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537849 : List Nat := [1, 2, 1, 7, 1, 1, 2, 1, 3, 3]
def baseStart_1537849 : Nat := 118140960795 + 1537849 * 2 ^ 59
def prefixEnd_1537849 : Nat := 4983230072969 + 3 ^ 40 * 1537849 * 2
def baseEnd_1537849 : Nat := 526437140690839261610045

theorem tailTrace_1537849 : CollatzResearch.WordTrace tailWord_1537849 prefixEnd_1537849 526437140690839261610045 := by
  unfold tailWord_1537849
  simp only [CollatzResearch.WordTrace]
  refine ⟨56089961005643191544176601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37393307337095461029451067 56089961005643191544176601)
  ·
    refine ⟨42067470754232393658132451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56089961005643191544176601 42067470754232393658132451)
    ·
      refine ⟨63101206131348590487198677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42067470754232393658132451 63101206131348590487198677)
      ·
        refine ⟨1478934518703482589543719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 63101206131348590487198677 1478934518703482589543719)
        ·
          refine ⟨2218401778055223884315579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1478934518703482589543719 2218401778055223884315579)
          ·
            refine ⟨3327602667082835826473369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2218401778055223884315579 3327602667082835826473369)
            ·
              refine ⟨2495702000312126869855027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3327602667082835826473369 2495702000312126869855027)
              ·
                refine ⟨3743553000468190304782541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2495702000312126869855027 3743553000468190304782541)
                ·
                  refine ⟨1403832375175571364293453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3743553000468190304782541 1403832375175571364293453)
                  ·
                    refine ⟨526437140690839261610045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1403832375175571364293453 526437140690839261610045)
                    ·
                      rfl

theorem cell22_1537849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 3, 3].length) (baseStart_1537849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537849 prefixEnd_1537849 := by exact prefixLift 1537849
  have htrace : WordTrace (prefixWord ++ tailWord_1537849) baseStart_1537849 baseEnd_1537849 := by
    simpa [prefixWord, tailWord_1537849, baseEnd_1537849] using wordTrace_append hprefix tailTrace_1537849
  have hstable : (prefixWord ++ tailWord_1537849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537849).length < 2 ^ (prefixWord ++ tailWord_1537849).sum := by decide
  have hdescent : baseEnd_1537849 < baseStart_1537849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1537905 : List Nat := [1, 2, 2, 2, 1, 3, 1, 3, 4, 3]
def baseStart_1537905 : Nat := 118140960795 + 1537905 * 2 ^ 59
def prefixEnd_1537905 : Nat := 4983230072969 + 3 ^ 40 * 1537905 * 2
def baseEnd_1537905 : Nat := 526456310635273782209873

theorem tailTrace_1537905 : CollatzResearch.WordTrace tailWord_1537905 prefixEnd_1537905 526456310635273782209873 := by
  unfold tailWord_1537905
  simp only [CollatzResearch.WordTrace]
  refine ⟨56092003493440313108215169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37394668995626875405476779 56092003493440313108215169)
  ·
    refine ⟨42069002620080234831161377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56092003493440313108215169 42069002620080234831161377)
    ·
      refine ⟨31551751965060176123371033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42069002620080234831161377 31551751965060176123371033)
      ·
        refine ⟨23663813973795132092528275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31551751965060176123371033 23663813973795132092528275)
        ·
          refine ⟨35495720960692698138792413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23663813973795132092528275 35495720960692698138792413)
          ·
            refine ⟨13310895360259761802047155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35495720960692698138792413 13310895360259761802047155)
            ·
              refine ⟨19966343040389642703070733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13310895360259761802047155 19966343040389642703070733)
              ·
                refine ⟨7487378640146116013651525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19966343040389642703070733 7487378640146116013651525)
                ·
                  refine ⟨1403883495027396752559661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7487378640146116013651525 1403883495027396752559661)
                  ·
                    refine ⟨526456310635273782209873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1403883495027396752559661 526456310635273782209873)
                    ·
                      rfl

theorem cell22_1537905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_1537905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1537905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1537905 prefixEnd_1537905 := by exact prefixLift 1537905
  have htrace : WordTrace (prefixWord ++ tailWord_1537905) baseStart_1537905 baseEnd_1537905 := by
    simpa [prefixWord, tailWord_1537905, baseEnd_1537905] using wordTrace_append hprefix tailTrace_1537905
  have hstable : (prefixWord ++ tailWord_1537905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1537905).length < 2 ^ (prefixWord ++ tailWord_1537905).sum := by decide
  have hdescent : baseEnd_1537905 < baseStart_1537905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1537905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538072 : List Nat := [2, 1, 2, 3, 2, 1, 3, 2, 2, 4]
def baseStart_1538072 : Nat := 118140960795 + 1538072 * 2 ^ 59
def prefixEnd_1538072 : Nat := 4983230072969 + 3 ^ 40 * 1538072 * 2
def baseEnd_1538072 : Nat := 526513478148141013284361

theorem tailTrace_1538072 : CollatzResearch.WordTrace tailWord_1538072 prefixEnd_1538072 526513478148141013284361 := by
  unfold tailWord_1538072
  simp only [CollatzResearch.WordTrace]
  refine ⟨28049047241917650314772235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37398729655890200419696313 28049047241917650314772235)
  ·
    refine ⟨42073570862876475472158353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28049047241917650314772235 42073570862876475472158353)
    ·
      refine ⟨31555178147157356604118765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42073570862876475472158353 31555178147157356604118765)
      ·
        refine ⟨11833191805184008726544537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31555178147157356604118765 11833191805184008726544537)
        ·
          refine ⟨8874893853888006544908403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11833191805184008726544537 8874893853888006544908403)
          ·
            refine ⟨13312340780832009817362605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8874893853888006544908403 13312340780832009817362605)
            ·
              refine ⟨4992127792812003681510977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13312340780832009817362605 4992127792812003681510977)
              ·
                refine ⟨3744095844609002761133233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4992127792812003681510977 3744095844609002761133233)
                ·
                  refine ⟨2808071883456752070849925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3744095844609002761133233 2808071883456752070849925)
                  ·
                    refine ⟨526513478148141013284361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2808071883456752070849925 526513478148141013284361)
                    ·
                      rfl

theorem cell22_1538072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 2, 2, 4].length) (baseStart_1538072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538072 prefixEnd_1538072 := by exact prefixLift 1538072
  have htrace : WordTrace (prefixWord ++ tailWord_1538072) baseStart_1538072 baseEnd_1538072 := by
    simpa [prefixWord, tailWord_1538072, baseEnd_1538072] using wordTrace_append hprefix tailTrace_1538072
  have hstable : (prefixWord ++ tailWord_1538072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538072).length < 2 ^ (prefixWord ++ tailWord_1538072).sum := by decide
  have hdescent : baseEnd_1538072 < baseStart_1538072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538076 : List Nat := [2, 2, 3, 1, 3, 2, 3, 2, 4]
def baseStart_1538076 : Nat := 118140960795 + 1538076 * 2 ^ 59
def prefixEnd_1538076 : Nat := 4983230072969 + 3 ^ 40 * 1538076 * 2
def baseEnd_1538076 : Nat := 175504949143295445394783

theorem tailTrace_1538076 : CollatzResearch.WordTrace tailWord_1538076 prefixEnd_1538076 175504949143295445394783 := by
  unfold tailWord_1538076
  simp only [CollatzResearch.WordTrace]
  refine ⟨28049120187910404656345041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37398826917213872875126721 28049120187910404656345041)
  ·
    refine ⟨21036840140932803492258781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28049120187910404656345041 21036840140932803492258781)
    ·
      refine ⟨7888815052849801309597043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21036840140932803492258781 7888815052849801309597043)
      ·
        refine ⟨11833222579274701964395565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7888815052849801309597043 11833222579274701964395565)
        ·
          refine ⟨4437458467228013236648337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11833222579274701964395565 4437458467228013236648337)
          ·
            refine ⟨3328093850421009927486253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4437458467228013236648337 3328093850421009927486253)
            ·
              refine ⟨1248035193907878722807345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3328093850421009927486253 1248035193907878722807345)
              ·
                refine ⟨936026395430909042105509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1248035193907878722807345 936026395430909042105509)
                ·
                  refine ⟨175504949143295445394783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 936026395430909042105509 175504949143295445394783)
                  ·
                    rfl

theorem cell22_1538076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 4].length) (baseStart_1538076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538076 prefixEnd_1538076 := by exact prefixLift 1538076
  have htrace : WordTrace (prefixWord ++ tailWord_1538076) baseStart_1538076 baseEnd_1538076 := by
    simpa [prefixWord, tailWord_1538076, baseEnd_1538076] using wordTrace_append hprefix tailTrace_1538076
  have hstable : (prefixWord ++ tailWord_1538076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538076).length < 2 ^ (prefixWord ++ tailWord_1538076).sum := by decide
  have hdescent : baseEnd_1538076 < baseStart_1538076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538115 : List Nat := [1, 1, 1, 3, 1, 2, 2, 4, 7]
def baseStart_1538115 : Nat := 118140960795 + 1538115 * 2 ^ 59
def prefixEnd_1538115 : Nat := 4983230072969 + 3 ^ 40 * 1538115 * 2
def baseEnd_1538115 : Nat := 175509399308967744819743

theorem tailTrace_1538115 : CollatzResearch.WordTrace tailWord_1538115 prefixEnd_1538115 175509399308967744819743 := by
  unfold tailWord_1538115
  simp only [CollatzResearch.WordTrace]
  refine ⟨56099662822679518973359799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37399775215119679315573199 56099662822679518973359799)
  ·
    refine ⟨84149494234019278460039699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56099662822679518973359799 84149494234019278460039699)
    ·
      refine ⟨126224241351028917690059549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84149494234019278460039699 126224241351028917690059549)
      ·
        refine ⟨47334090506635844133772331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126224241351028917690059549 47334090506635844133772331)
        ·
          refine ⟨71001135759953766200658497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47334090506635844133772331 71001135759953766200658497)
          ·
            refine ⟨53250851819965324650493873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71001135759953766200658497 53250851819965324650493873)
            ·
              refine ⟨39938138864973993487870405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53250851819965324650493873 39938138864973993487870405)
              ·
                refine ⟨7488401037182623778975701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39938138864973993487870405 7488401037182623778975701)
                ·
                  refine ⟨175509399308967744819743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7488401037182623778975701 175509399308967744819743)
                  ·
                    rfl

theorem cell22_1538115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 7].length) (baseStart_1538115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538115 prefixEnd_1538115 := by exact prefixLift 1538115
  have htrace : WordTrace (prefixWord ++ tailWord_1538115) baseStart_1538115 baseEnd_1538115 := by
    simpa [prefixWord, tailWord_1538115, baseEnd_1538115] using wordTrace_append hprefix tailTrace_1538115
  have hstable : (prefixWord ++ tailWord_1538115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538115).length < 2 ^ (prefixWord ++ tailWord_1538115).sum := by decide
  have hdescent : baseEnd_1538115 < baseStart_1538115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538136 : List Nat := [2, 1, 2, 2, 1, 5, 1, 4, 1, 3]
def baseStart_1538136 : Nat := 118140960795 + 1538136 * 2 ^ 59
def prefixEnd_1538136 : Nat := 4983230072969 + 3 ^ 40 * 1538136 * 2
def baseEnd_1538136 : Nat := 526535386656066179684165

theorem tailTrace_1538136 : CollatzResearch.WordTrace tailWord_1538136 prefixEnd_1538136 526535386656066179684165 := by
  unfold tailWord_1538136
  simp only [CollatzResearch.WordTrace]
  refine ⟨28050214377801719779937131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37400285837068959706582841 28050214377801719779937131)
  ·
    refine ⟨42075321566702579669905697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28050214377801719779937131 42075321566702579669905697)
    ·
      refine ⟨31556491175026934752429273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42075321566702579669905697 31556491175026934752429273)
      ·
        refine ⟨23667368381270201064321955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31556491175026934752429273 23667368381270201064321955)
        ·
          refine ⟨35501052571905301596482933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23667368381270201064321955 35501052571905301596482933)
          ·
            refine ⟨3328223678616122024670275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35501052571905301596482933 3328223678616122024670275)
            ·
              refine ⟨4992335517924183037005413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328223678616122024670275 4992335517924183037005413)
              ·
                refine ⟨936062909610784319438515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4992335517924183037005413 936062909610784319438515)
                ·
                  refine ⟨1404094364416176479157773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 936062909610784319438515 1404094364416176479157773)
                  ·
                    refine ⟨526535386656066179684165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1404094364416176479157773 526535386656066179684165)
                    ·
                      rfl

theorem cell22_1538136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 1, 3].length) (baseStart_1538136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538136 prefixEnd_1538136 := by exact prefixLift 1538136
  have htrace : WordTrace (prefixWord ++ tailWord_1538136) baseStart_1538136 baseEnd_1538136 := by
    simpa [prefixWord, tailWord_1538136, baseEnd_1538136] using wordTrace_append hprefix tailTrace_1538136
  have hstable : (prefixWord ++ tailWord_1538136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538136).length < 2 ^ (prefixWord ++ tailWord_1538136).sum := by decide
  have hdescent : baseEnd_1538136 < baseStart_1538136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538179 : List Nat := [1, 1, 1, 3, 3, 4, 1, 3, 1, 4]
def baseStart_1538179 : Nat := 118140960795 + 1538179 * 2 ^ 59
def prefixEnd_1538179 : Nat := 4983230072969 + 3 ^ 40 * 1538179 * 2
def baseEnd_1538179 : Nat := 526550106434828400859033

theorem tailTrace_1538179 : CollatzResearch.WordTrace tailWord_1538179 prefixEnd_1538179 526550106434828400859033 := by
  unfold tailWord_1538179
  simp only [CollatzResearch.WordTrace]
  refine ⟨56101997094447657903689591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37401331396298438602459727 56101997094447657903689591)
  ·
    refine ⟨84152995641671486855534387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56101997094447657903689591 84152995641671486855534387)
    ·
      refine ⟨126229493462507230283301581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84152995641671486855534387 126229493462507230283301581)
      ·
        refine ⟨47336060048440211356238093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126229493462507230283301581 47336060048440211356238093)
        ·
          refine ⟨17751022518165079258589285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47336060048440211356238093 17751022518165079258589285)
          ·
            refine ⟨3328316722155952360985491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17751022518165079258589285 3328316722155952360985491)
            ·
              refine ⟨4992475083233928541478237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3328316722155952360985491 4992475083233928541478237)
              ·
                refine ⟨1872178156212723203054339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4992475083233928541478237 1872178156212723203054339)
                ·
                  refine ⟨2808267234319084804581509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872178156212723203054339 2808267234319084804581509)
                  ·
                    refine ⟨526550106434828400859033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2808267234319084804581509 526550106434828400859033)
                    ·
                      rfl

theorem cell22_1538179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 3, 1, 4].length) (baseStart_1538179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538179 prefixEnd_1538179 := by exact prefixLift 1538179
  have htrace : WordTrace (prefixWord ++ tailWord_1538179) baseStart_1538179 baseEnd_1538179 := by
    simpa [prefixWord, tailWord_1538179, baseEnd_1538179] using wordTrace_append hprefix tailTrace_1538179
  have hstable : (prefixWord ++ tailWord_1538179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538179).length < 2 ^ (prefixWord ++ tailWord_1538179).sum := by decide
  have hdescent : baseEnd_1538179 < baseStart_1538179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538194 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 6]
def baseStart_1538194 : Nat := 118140960795 + 1538194 * 2 ^ 59
def prefixEnd_1538194 : Nat := 4983230072969 + 3 ^ 40 * 1538194 * 2
def baseEnd_1538194 : Nat := 175518413747124453911329

theorem tailTrace_1538194 : CollatzResearch.WordTrace tailWord_1538194 prefixEnd_1538194 175518413747124453911329 := by
  unfold tailWord_1538194
  simp only [CollatzResearch.WordTrace]
  refine ⟨14025636047348328866371409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37401696126262210310323757 14025636047348328866371409)
  ·
    refine ⟨10519227035511246649778557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14025636047348328866371409 10519227035511246649778557)
    ·
      refine ⟨3944710138316717493666959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10519227035511246649778557 3944710138316717493666959)
      ·
        refine ⟨5917065207475076240500439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3944710138316717493666959 5917065207475076240500439)
        ·
          refine ⟨8875597811212614360750659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5917065207475076240500439 8875597811212614360750659)
          ·
            refine ⟨13313396716818921541125989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8875597811212614360750659 13313396716818921541125989)
            ·
              refine ⟨2496261884403547788961123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13313396716818921541125989 2496261884403547788961123)
              ·
                refine ⟨3744392826605321683441685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2496261884403547788961123 3744392826605321683441685)
                ·
                  refine ⟨175518413747124453911329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3744392826605321683441685 175518413747124453911329)
                  ·
                    rfl

theorem cell22_1538194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 6].length) (baseStart_1538194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538194 prefixEnd_1538194 := by exact prefixLift 1538194
  have htrace : WordTrace (prefixWord ++ tailWord_1538194) baseStart_1538194 baseEnd_1538194 := by
    simpa [prefixWord, tailWord_1538194, baseEnd_1538194] using wordTrace_append hprefix tailTrace_1538194
  have hstable : (prefixWord ++ tailWord_1538194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538194).length < 2 ^ (prefixWord ++ tailWord_1538194).sum := by decide
  have hdescent : baseEnd_1538194 < baseStart_1538194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538209 : List Nat := [1, 2, 3, 3, 1, 2, 3, 1, 1, 5]
def baseStart_1538209 : Nat := 118140960795 + 1538209 * 2 ^ 59
def prefixEnd_1538209 : Nat := 4983230072969 + 3 ^ 40 * 1538209 * 2
def baseEnd_1538209 : Nat := 526560376047918322608941

theorem tailTrace_1538209 : CollatzResearch.WordTrace tailWord_1538209 prefixEnd_1538209 526560376047918322608941 := by
  unfold tailWord_1538209
  simp only [CollatzResearch.WordTrace]
  refine ⟨56103091284338973027281681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37402060856225982018187787 56103091284338973027281681)
  ·
    refine ⟨42077318463254229770461261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56103091284338973027281681 42077318463254229770461261)
    ·
      refine ⟨15778994423720336163922973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42077318463254229770461261 15778994423720336163922973)
      ·
        refine ⟨5917122908895126061471115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15778994423720336163922973 5917122908895126061471115)
        ·
          refine ⟨8875684363342689092206673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5917122908895126061471115 8875684363342689092206673)
          ·
            refine ⟨6656763272507016819155005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8875684363342689092206673 6656763272507016819155005)
            ·
              refine ⟨2496286227190131307183127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6656763272507016819155005 2496286227190131307183127)
              ·
                refine ⟨3744429340785196960774691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2496286227190131307183127 3744429340785196960774691)
                ·
                  refine ⟨5616644011177795441162037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3744429340785196960774691 5616644011177795441162037)
                  ·
                    refine ⟨526560376047918322608941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5616644011177795441162037 526560376047918322608941)
                    ·
                      rfl

theorem cell22_1538209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_1538209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538209 prefixEnd_1538209 := by exact prefixLift 1538209
  have htrace : WordTrace (prefixWord ++ tailWord_1538209) baseStart_1538209 baseEnd_1538209 := by
    simpa [prefixWord, tailWord_1538209, baseEnd_1538209] using wordTrace_append hprefix tailTrace_1538209
  have hstable : (prefixWord ++ tailWord_1538209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538209).length < 2 ^ (prefixWord ++ tailWord_1538209).sum := by decide
  have hdescent : baseEnd_1538209 < baseStart_1538209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538314 : List Nat := [3, 1, 2, 2, 1, 1, 3, 2, 3, 4]
def baseStart_1538314 : Nat := 118140960795 + 1538314 * 2 ^ 59
def prefixEnd_1538314 : Nat := 4983230072969 + 3 ^ 40 * 1538314 * 2
def baseEnd_1538314 : Nat := 526596319693733048733619

theorem tailTrace_1538314 : CollatzResearch.WordTrace tailWord_1538314 prefixEnd_1538314 526596319693733048733619 := by
  unfold tailWord_1538314
  simp only [CollatzResearch.WordTrace]
  refine ⟨14026730237239643989963499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37404613965972383973235997 14026730237239643989963499)
  ·
    refine ⟨21040095355859465984945249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14026730237239643989963499 21040095355859465984945249)
    ·
      refine ⟨15780071516894599488708937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21040095355859465984945249 15780071516894599488708937)
      ·
        refine ⟨11835053637670949616531703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15780071516894599488708937 11835053637670949616531703)
        ·
          refine ⟨17752580456506424424797555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11835053637670949616531703 17752580456506424424797555)
          ·
            refine ⟨26628870684759636637196333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17752580456506424424797555 26628870684759636637196333)
            ·
              refine ⟨9985826506784863738948625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26628870684759636637196333 9985826506784863738948625)
              ·
                refine ⟨7489369880088647804211469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9985826506784863738948625 7489369880088647804211469)
                ·
                  refine ⟨2808513705033242926579301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7489369880088647804211469 2808513705033242926579301)
                  ·
                    refine ⟨526596319693733048733619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2808513705033242926579301 526596319693733048733619)
                    ·
                      rfl

theorem cell22_1538314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_1538314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538314 prefixEnd_1538314 := by exact prefixLift 1538314
  have htrace : WordTrace (prefixWord ++ tailWord_1538314) baseStart_1538314 baseEnd_1538314 := by
    simpa [prefixWord, tailWord_1538314, baseEnd_1538314] using wordTrace_append hprefix tailTrace_1538314
  have hstable : (prefixWord ++ tailWord_1538314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538314).length < 2 ^ (prefixWord ++ tailWord_1538314).sum := by decide
  have hdescent : baseEnd_1538314 < baseStart_1538314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538359 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 2, 4]
def baseStart_1538359 : Nat := 118140960795 + 1538359 * 2 ^ 59
def prefixEnd_1538359 : Nat := 4983230072969 + 3 ^ 40 * 1538359 * 2
def baseEnd_1538359 : Nat := 526611724113367931358481

theorem tailTrace_1538359 : CollatzResearch.WordTrace tailWord_1538359 prefixEnd_1538359 526611724113367931358481 := by
  unfold tailWord_1538359
  simp only [CollatzResearch.WordTrace]
  refine ⟨56108562233795548645242131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37405708155863699096828087 56108562233795548645242131)
  ·
    refine ⟨84162843350693322967863197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56108562233795548645242131 84162843350693322967863197)
    ·
      refine ⟨31561066256509996112948699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84162843350693322967863197 31561066256509996112948699)
      ·
        refine ⟨47341599384764994169423049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31561066256509996112948699 47341599384764994169423049)
        ·
          refine ⟨35506199538573745627067287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47341599384764994169423049 35506199538573745627067287)
          ·
            refine ⟨53259299307860618440600931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35506199538573745627067287 53259299307860618440600931)
            ·
              refine ⟨79888948961790927660901397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53259299307860618440600931 79888948961790927660901397)
              ·
                refine ⟨3744794482583949734104753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 79888948961790927660901397 3744794482583949734104753)
                ·
                  refine ⟨2808595861937962300578565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3744794482583949734104753 2808595861937962300578565)
                  ·
                    refine ⟨526611724113367931358481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2808595861937962300578565 526611724113367931358481)
                    ·
                      rfl

theorem cell22_1538359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_1538359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538359 prefixEnd_1538359 := by exact prefixLift 1538359
  have htrace : WordTrace (prefixWord ++ tailWord_1538359) baseStart_1538359 baseEnd_1538359 := by
    simpa [prefixWord, tailWord_1538359, baseEnd_1538359] using wordTrace_append hprefix tailTrace_1538359
  have hstable : (prefixWord ++ tailWord_1538359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538359).length < 2 ^ (prefixWord ++ tailWord_1538359).sum := by decide
  have hdescent : baseEnd_1538359 < baseStart_1538359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538436 : List Nat := [2, 3, 2, 1, 1, 2, 3, 3, 5]
def baseStart_1538436 : Nat := 118140960795 + 1538436 * 2 ^ 59
def prefixEnd_1538436 : Nat := 4983230072969 + 3 ^ 40 * 1538436 * 2
def baseEnd_1538436 : Nat := 175546027595655132394415

theorem tailTrace_1538436 : CollatzResearch.WordTrace tailWord_1538436 prefixEnd_1538436 175546027595655132394415 := by
  unfold tailWord_1538436
  simp only [CollatzResearch.WordTrace]
  refine ⟨28055685327258295397897581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37407580436344393863863441 28055685327258295397897581)
  ·
    refine ⟨10520881997721860774211593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28055685327258295397897581 10520881997721860774211593)
    ·
      refine ⟨7890661498291395580658695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10520881997721860774211593 7890661498291395580658695)
      ·
        refine ⟨11835992247437093370988043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7890661498291395580658695 11835992247437093370988043)
        ·
          refine ⟨17753988371155640056482065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11835992247437093370988043 17753988371155640056482065)
          ·
            refine ⟨13315491278366730042361549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17753988371155640056482065 13315491278366730042361549)
            ·
              refine ⟨4993309229387523765885581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13315491278366730042361549 4993309229387523765885581)
              ·
                refine ⟨1872490961020321412207093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4993309229387523765885581 1872490961020321412207093)
                ·
                  refine ⟨175546027595655132394415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1872490961020321412207093 175546027595655132394415)
                  ·
                    rfl

theorem cell22_1538436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_1538436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538436 prefixEnd_1538436 := by exact prefixLift 1538436
  have htrace : WordTrace (prefixWord ++ tailWord_1538436) baseStart_1538436 baseEnd_1538436 := by
    simpa [prefixWord, tailWord_1538436, baseEnd_1538436] using wordTrace_append hprefix tailTrace_1538436
  have hstable : (prefixWord ++ tailWord_1538436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538436).length < 2 ^ (prefixWord ++ tailWord_1538436).sum := by decide
  have hdescent : baseEnd_1538436 < baseStart_1538436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538496 : List Nat := [2, 1, 1, 2, 3, 1, 1, 2, 6, 3]
def baseStart_1538496 : Nat := 118140960795 + 1538496 * 2 ^ 59
def prefixEnd_1538496 : Nat := 4983230072969 + 3 ^ 40 * 1538496 * 2
def baseEnd_1538496 : Nat := 526658622013145240683061

theorem tailTrace_1538496 : CollatzResearch.WordTrace tailWord_1538496 prefixEnd_1538496 526658622013145240683061 := by
  unfold tailWord_1538496
  simp only [CollatzResearch.WordTrace]
  refine ⟨28056779517149610521489671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37409039356199480695319561 28056779517149610521489671)
  ·
    refine ⟨42085169275724415782234507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28056779517149610521489671 42085169275724415782234507)
    ·
      refine ⟨63127753913586623673351761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42085169275724415782234507 63127753913586623673351761)
      ·
        refine ⟨47345815435189967755013821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63127753913586623673351761 47345815435189967755013821)
        ·
          refine ⟨17754680788196237908130183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47345815435189967755013821 17754680788196237908130183)
          ·
            refine ⟨26632021182294356862195275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17754680788196237908130183 26632021182294356862195275)
            ·
              refine ⟨39948031773441535293292913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26632021182294356862195275 39948031773441535293292913)
              ·
                refine ⟨29961023830081151469969685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39948031773441535293292913 29961023830081151469969685)
                ·
                  refine ⟨1404422992035053975154829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29961023830081151469969685 1404422992035053975154829)
                  ·
                    refine ⟨526658622013145240683061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1404422992035053975154829 526658622013145240683061)
                    ·
                      rfl

theorem cell22_1538496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 6, 3].length) (baseStart_1538496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538496 prefixEnd_1538496 := by exact prefixLift 1538496
  have htrace : WordTrace (prefixWord ++ tailWord_1538496) baseStart_1538496 baseEnd_1538496 := by
    simpa [prefixWord, tailWord_1538496, baseEnd_1538496] using wordTrace_append hprefix tailTrace_1538496
  have hstable : (prefixWord ++ tailWord_1538496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538496).length < 2 ^ (prefixWord ++ tailWord_1538496).sum := by decide
  have hdescent : baseEnd_1538496 < baseStart_1538496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538566 : List Nat := [6, 2, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1538566 : Nat := 118140960795 + 1538566 * 2 ^ 59
def prefixEnd_1538566 : Nat := 4983230072969 + 3 ^ 40 * 1538566 * 2
def baseEnd_1538566 : Nat := 175560861481229463810949

theorem tailTrace_1538566 : CollatzResearch.WordTrace tailWord_1538566 prefixEnd_1538566 175560861481229463810949 := by
  unfold tailWord_1538566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1753628504501425718688361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37410741429363748665351701 1753628504501425718688361)
  ·
    refine ⟨1315221378376069289016271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1753628504501425718688361 1315221378376069289016271)
    ·
      refine ⟨1972832067564103933524407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1315221378376069289016271 1972832067564103933524407)
      ·
        refine ⟨2959248101346155900286611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1972832067564103933524407 2959248101346155900286611)
        ·
          refine ⟨4438872152019233850429917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2959248101346155900286611 4438872152019233850429917)
          ·
            refine ⟨1664577057007212693911219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4438872152019233850429917 1664577057007212693911219)
            ·
              refine ⟨2496865585510819040866829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664577057007212693911219 2496865585510819040866829)
              ·
                refine ⟨936324594566557140325061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2496865585510819040866829 936324594566557140325061)
                ·
                  refine ⟨175560861481229463810949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 936324594566557140325061 175560861481229463810949)
                  ·
                    rfl

theorem cell22_1538566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1538566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538566 prefixEnd_1538566 := by exact prefixLift 1538566
  have htrace : WordTrace (prefixWord ++ tailWord_1538566) baseStart_1538566 baseEnd_1538566 := by
    simpa [prefixWord, tailWord_1538566, baseEnd_1538566] using wordTrace_append hprefix tailTrace_1538566
  have hstable : (prefixWord ++ tailWord_1538566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538566).length < 2 ^ (prefixWord ++ tailWord_1538566).sum := by decide
  have hdescent : baseEnd_1538566 < baseStart_1538566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538571 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 7]
def baseStart_1538571 : Nat := 118140960795 + 1538571 * 2 ^ 59
def prefixEnd_1538571 : Nat := 4983230072969 + 3 ^ 40 * 1538571 * 2
def baseEnd_1538571 : Nat := 175561432015290015019277

theorem tailTrace_1538571 : CollatzResearch.WordTrace tailWord_1538571 prefixEnd_1538571 175561432015290015019277 := by
  unfold tailWord_1538571
  simp only [CollatzResearch.WordTrace]
  refine ⟨56116294509027508851959567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37410863006018339234639711 56116294509027508851959567)
  ·
    refine ⟨84174441763541263277939351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56116294509027508851959567 84174441763541263277939351)
    ·
      refine ⟨126261662645311894916909027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84174441763541263277939351 126261662645311894916909027)
      ·
        refine ⟨189392493967967842375363541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126261662645311894916909027 189392493967967842375363541)
        ·
          refine ⟨4438886577374246305672583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 189392493967967842375363541 4438886577374246305672583)
          ·
            refine ⟨6658329866061369458508875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4438886577374246305672583 6658329866061369458508875)
            ·
              refine ⟨9987494799092054187763313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6658329866061369458508875 9987494799092054187763313)
              ·
                refine ⟨7490621099319040640822485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9987494799092054187763313 7490621099319040640822485)
                ·
                  refine ⟨175561432015290015019277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7490621099319040640822485 175561432015290015019277)
                  ·
                    rfl

theorem cell22_1538571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 7].length) (baseStart_1538571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538571 prefixEnd_1538571 := by exact prefixLift 1538571
  have htrace : WordTrace (prefixWord ++ tailWord_1538571) baseStart_1538571 baseEnd_1538571 := by
    simpa [prefixWord, tailWord_1538571, baseEnd_1538571] using wordTrace_append hprefix tailTrace_1538571
  have hstable : (prefixWord ++ tailWord_1538571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538571).length < 2 ^ (prefixWord ++ tailWord_1538571).sum := by decide
  have hdescent : baseEnd_1538571 < baseStart_1538571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538586 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 4, 5]
def baseStart_1538586 : Nat := 118140960795 + 1538586 * 2 ^ 59
def prefixEnd_1538586 : Nat := 4983230072969 + 3 ^ 40 * 1538586 * 2
def baseEnd_1538586 : Nat := 526689430852415005932785

theorem tailTrace_1538586 : CollatzResearch.WordTrace tailWord_1538586 prefixEnd_1538586 526689430852415005932785 := by
  unfold tailWord_1538586
  simp only [CollatzResearch.WordTrace]
  refine ⟨14029210400993291603438903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37411227735982110942503741 14029210400993291603438903)
  ·
    refine ⟨21043815601489937405158355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14029210400993291603438903 21043815601489937405158355)
    ·
      refine ⟨31565723402234906107737533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21043815601489937405158355 31565723402234906107737533)
      ·
        refine ⟨11837146275838089790401575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31565723402234906107737533 11837146275838089790401575)
        ·
          refine ⟨17755719413757134685602363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11837146275838089790401575 17755719413757134685602363)
          ·
            refine ⟨26633579120635702028403545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17755719413757134685602363 26633579120635702028403545)
            ·
              refine ⟨19975184340476776521302659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26633579120635702028403545 19975184340476776521302659)
              ·
                refine ⟨29962776510715164781953989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19975184340476776521302659 29962776510715164781953989)
                ·
                  refine ⟨5618020595759093396616373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29962776510715164781953989 5618020595759093396616373)
                  ·
                    refine ⟨526689430852415005932785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5618020595759093396616373 526689430852415005932785)
                    ·
                      rfl

theorem cell22_1538586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_1538586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538586 prefixEnd_1538586 := by exact prefixLift 1538586
  have htrace : WordTrace (prefixWord ++ tailWord_1538586) baseStart_1538586 baseEnd_1538586 := by
    simpa [prefixWord, tailWord_1538586, baseEnd_1538586] using wordTrace_append hprefix tailTrace_1538586
  have hstable : (prefixWord ++ tailWord_1538586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538586).length < 2 ^ (prefixWord ++ tailWord_1538586).sum := by decide
  have hdescent : baseEnd_1538586 < baseStart_1538586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538592 : List Nat := [2, 1, 1, 6, 2, 2, 1, 1, 3, 3]
def baseStart_1538592 : Nat := 118140960795 + 1538592 * 2 ^ 59
def prefixEnd_1538592 : Nat := 4983230072969 + 3 ^ 40 * 1538592 * 2
def baseEnd_1538592 : Nat := 526691484775032990282767

theorem tailTrace_1538592 : CollatzResearch.WordTrace tailWord_1538592 prefixEnd_1538592 526691484775032990282767 := by
  unfold tailWord_1538592
  simp only [CollatzResearch.WordTrace]
  refine ⟨28058530220975714719237015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37411373627967619625649353 28058530220975714719237015)
  ·
    refine ⟨42087795331463572078855523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28058530220975714719237015 42087795331463572078855523)
    ·
      refine ⟨63131692997195358118283285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42087795331463572078855523 63131692997195358118283285)
      ·
        refine ⟨2959298109243532411794529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63131692997195358118283285 2959298109243532411794529)
        ·
          refine ⟨2219473581932649308845897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2959298109243532411794529 2219473581932649308845897)
          ·
            refine ⟨1664605186449486981634423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2219473581932649308845897 1664605186449486981634423)
            ·
              refine ⟨2496907779674230472451635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664605186449486981634423 2496907779674230472451635)
              ·
                refine ⟨3745361669511345708677453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2496907779674230472451635 3745361669511345708677453)
                ·
                  refine ⟨1404510626066754640754045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3745361669511345708677453 1404510626066754640754045)
                  ·
                    refine ⟨526691484775032990282767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1404510626066754640754045 526691484775032990282767)
                    ·
                      rfl

theorem cell22_1538592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 3, 3].length) (baseStart_1538592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538592 prefixEnd_1538592 := by exact prefixLift 1538592
  have htrace : WordTrace (prefixWord ++ tailWord_1538592) baseStart_1538592 baseEnd_1538592 := by
    simpa [prefixWord, tailWord_1538592, baseEnd_1538592] using wordTrace_append hprefix tailTrace_1538592
  have hstable : (prefixWord ++ tailWord_1538592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538592).length < 2 ^ (prefixWord ++ tailWord_1538592).sum := by decide
  have hdescent : baseEnd_1538592 < baseStart_1538592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538616 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 8]
def baseStart_1538616 : Nat := 118140960795 + 1538616 * 2 ^ 59
def prefixEnd_1538616 : Nat := 4983230072969 + 3 ^ 40 * 1538616 * 2
def baseEnd_1538616 : Nat := 175566566821834975894231

theorem tailTrace_1538616 : CollatzResearch.WordTrace tailWord_1538616 prefixEnd_1538616 175566566821834975894231 := by
  unfold tailWord_1538616
  simp only [CollatzResearch.WordTrace]
  refine ⟨28058967896932240768673851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37411957195909654358231801 28058967896932240768673851)
  ·
    refine ⟨42088451845398361153010777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28058967896932240768673851 42088451845398361153010777)
    ·
      refine ⟨31566338884048770864758083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42088451845398361153010777 31566338884048770864758083)
      ·
        refine ⟨47349508326073156297137125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31566338884048770864758083 47349508326073156297137125)
        ·
          refine ⟨8878032811138716805713211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47349508326073156297137125 8878032811138716805713211)
          ·
            refine ⟨13317049216708075208569817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8878032811138716805713211 13317049216708075208569817)
            ·
              refine ⟨9987786912531056406427363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13317049216708075208569817 9987786912531056406427363)
              ·
                refine ⟨14981680368796584609641045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9987786912531056406427363 14981680368796584609641045)
                ·
                  refine ⟨175566566821834975894231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14981680368796584609641045 175566566821834975894231)
                  ·
                    rfl

theorem cell22_1538616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 8].length) (baseStart_1538616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538616 prefixEnd_1538616 := by exact prefixLift 1538616
  have htrace : WordTrace (prefixWord ++ tailWord_1538616) baseStart_1538616 baseEnd_1538616 := by
    simpa [prefixWord, tailWord_1538616, baseEnd_1538616] using wordTrace_append hprefix tailTrace_1538616
  have hstable : (prefixWord ++ tailWord_1538616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538616).length < 2 ^ (prefixWord ++ tailWord_1538616).sum := by decide
  have hdescent : baseEnd_1538616 < baseStart_1538616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538618 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 3, 4]
def baseStart_1538618 : Nat := 118140960795 + 1538618 * 2 ^ 59
def prefixEnd_1538618 : Nat := 4983230072969 + 3 ^ 40 * 1538618 * 2
def baseEnd_1538618 : Nat := 526700385106377589132687

theorem tailTrace_1538618 : CollatzResearch.WordTrace tailWord_1538618 prefixEnd_1538618 526700385106377589132687 := by
  unfold tailWord_1538618
  simp only [CollatzResearch.WordTrace]
  refine ⟨14029502184964308969730127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37412005826571490585947005 14029502184964308969730127)
  ·
    refine ⟨21044253277446463454595191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14029502184964308969730127 21044253277446463454595191)
    ·
      refine ⟨31566379916169695181892787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21044253277446463454595191 31566379916169695181892787)
      ·
        refine ⟨47349569874254542772839181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31566379916169695181892787 47349569874254542772839181)
        ·
          refine ⟨17756088702845453539814693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47349569874254542772839181 17756088702845453539814693)
          ·
            refine ⟨3329266631783522538715255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17756088702845453539814693 3329266631783522538715255)
            ·
              refine ⟨4993899947675283808072883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3329266631783522538715255 4993899947675283808072883)
              ·
                refine ⟨7490849921512925712109325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4993899947675283808072883 7490849921512925712109325)
                ·
                  refine ⟨2809068720567347142040997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7490849921512925712109325 2809068720567347142040997)
                  ·
                    refine ⟨526700385106377589132687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2809068720567347142040997 526700385106377589132687)
                    ·
                      rfl

theorem cell22_1538618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 3, 4].length) (baseStart_1538618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538618 prefixEnd_1538618 := by exact prefixLift 1538618
  have htrace : WordTrace (prefixWord ++ tailWord_1538618) baseStart_1538618 baseEnd_1538618 := by
    simpa [prefixWord, tailWord_1538618, baseEnd_1538618] using wordTrace_append hprefix tailTrace_1538618
  have hstable : (prefixWord ++ tailWord_1538618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538618).length < 2 ^ (prefixWord ++ tailWord_1538618).sum := by decide
  have hdescent : baseEnd_1538618 < baseStart_1538618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538648 : List Nat := [2, 1, 2, 2, 1, 2, 2, 3, 4, 3]
def baseStart_1538648 : Nat := 118140960795 + 1538648 * 2 ^ 59
def prefixEnd_1538648 : Nat := 4983230072969 + 3 ^ 40 * 1538648 * 2
def baseEnd_1538648 : Nat := 526710654719467510882595

theorem tailTrace_1538648 : CollatzResearch.WordTrace tailWord_1538648 prefixEnd_1538648 526710654719467510882595 := by
  unfold tailWord_1538648
  simp only [CollatzResearch.WordTrace]
  refine ⟨28059551464874275501256299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37412735286499034001675065 28059551464874275501256299)
  ·
    refine ⟨42089327197311413251884449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28059551464874275501256299 42089327197311413251884449)
    ·
      refine ⟨31566995397983559938913337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42089327197311413251884449 31566995397983559938913337)
      ·
        refine ⟨23675246548487669954185003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31566995397983559938913337 23675246548487669954185003)
        ·
          refine ⟨35512869822731504931277505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23675246548487669954185003 35512869822731504931277505)
          ·
            refine ⟨26634652367048628698458129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35512869822731504931277505 26634652367048628698458129)
            ·
              refine ⟨19975989275286471523843597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26634652367048628698458129 19975989275286471523843597)
              ·
                refine ⟨7490995978232426821441349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19975989275286471523843597 7490995978232426821441349)
                ·
                  refine ⟨1404561745918580029020253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7490995978232426821441349 1404561745918580029020253)
                  ·
                    refine ⟨526710654719467510882595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1404561745918580029020253 526710654719467510882595)
                    ·
                      rfl

theorem cell22_1538648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 3, 4, 3].length) (baseStart_1538648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538648 prefixEnd_1538648 := by exact prefixLift 1538648
  have htrace : WordTrace (prefixWord ++ tailWord_1538648) baseStart_1538648 baseEnd_1538648 := by
    simpa [prefixWord, tailWord_1538648, baseEnd_1538648] using wordTrace_append hprefix tailTrace_1538648
  have hstable : (prefixWord ++ tailWord_1538648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538648).length < 2 ^ (prefixWord ++ tailWord_1538648).sum := by decide
  have hdescent : baseEnd_1538648 < baseStart_1538648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538654 : List Nat := [4, 4, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_1538654 : Nat := 118140960795 + 1538654 * 2 ^ 59
def prefixEnd_1538654 : Nat := 4983230072969 + 3 ^ 40 * 1538654 * 2
def baseEnd_1538654 : Nat := 526712708642085495232577

theorem tailTrace_1538654 : CollatzResearch.WordTrace tailWord_1538654 prefixEnd_1538654 526712708642085495232577 := by
  unfold tailWord_1538654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7014915220965851753403877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37412881178484542684820677 7014915220965851753403877)
  ·
    refine ⟨1315296603931097203763227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7014915220965851753403877 1315296603931097203763227)
    ·
      refine ⟨1972944905896645805644841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1315296603931097203763227 1972944905896645805644841)
      ·
        refine ⟨1479708679422484354233631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1972944905896645805644841 1479708679422484354233631)
        ·
          refine ⟨2219563019133726531350447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1479708679422484354233631 2219563019133726531350447)
          ·
            refine ⟨3329344528700589797025671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2219563019133726531350447 3329344528700589797025671)
            ·
              refine ⟨4994016793050884695538507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3329344528700589797025671 4994016793050884695538507)
              ·
                refine ⟨7491025189576327043307761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4994016793050884695538507 7491025189576327043307761)
                ·
                  refine ⟨5618268892182245282480821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7491025189576327043307761 5618268892182245282480821)
                  ·
                    refine ⟨526712708642085495232577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5618268892182245282480821 526712708642085495232577)
                    ·
                      rfl

theorem cell22_1538654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_1538654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538654 prefixEnd_1538654 := by exact prefixLift 1538654
  have htrace : WordTrace (prefixWord ++ tailWord_1538654) baseStart_1538654 baseEnd_1538654 := by
    simpa [prefixWord, tailWord_1538654, baseEnd_1538654] using wordTrace_append hprefix tailTrace_1538654
  have hstable : (prefixWord ++ tailWord_1538654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538654).length < 2 ^ (prefixWord ++ tailWord_1538654).sum := by decide
  have hdescent : baseEnd_1538654 < baseStart_1538654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538787 : List Nat := [1, 1, 1, 7, 1, 1, 3, 2, 1, 4]
def baseStart_1538787 : Nat := 118140960795 + 1538787 * 2 ^ 59
def prefixEnd_1538787 : Nat := 4983230072969 + 3 ^ 40 * 1538787 * 2
def baseEnd_1538787 : Nat := 526758237260117481657169

theorem tailTrace_1538787 : CollatzResearch.WordTrace tailWord_1538787 prefixEnd_1538787 526758237260117481657169 := by
  unfold tailWord_1538787
  simp only [CollatzResearch.WordTrace]
  refine ⟨56124172676244977741822615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37416115117496651827881743 56124172676244977741822615)
  ·
    refine ⟨84186259014367466612733923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56124172676244977741822615 84186259014367466612733923)
    ·
      refine ⟨126279388521551199919100885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84186259014367466612733923 126279388521551199919100885)
      ·
        refine ⟨2959673168473856248103927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 126279388521551199919100885 2959673168473856248103927)
        ·
          refine ⟨4439509752710784372155891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2959673168473856248103927 4439509752710784372155891)
          ·
            refine ⟨6659264629066176558233837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4439509752710784372155891 6659264629066176558233837)
            ·
              refine ⟨2497224235899816209337689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6659264629066176558233837 2497224235899816209337689)
              ·
                refine ⟨1872918176924862157003267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2497224235899816209337689 1872918176924862157003267)
                ·
                  refine ⟨2809377265387293235504901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1872918176924862157003267 2809377265387293235504901)
                  ·
                    refine ⟨526758237260117481657169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2809377265387293235504901 526758237260117481657169)
                    ·
                      rfl

theorem cell22_1538787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 1, 4].length) (baseStart_1538787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538787 prefixEnd_1538787 := by exact prefixLift 1538787
  have htrace : WordTrace (prefixWord ++ tailWord_1538787) baseStart_1538787 baseEnd_1538787 := by
    simpa [prefixWord, tailWord_1538787, baseEnd_1538787] using wordTrace_append hprefix tailTrace_1538787
  have hstable : (prefixWord ++ tailWord_1538787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538787).length < 2 ^ (prefixWord ++ tailWord_1538787).sum := by decide
  have hdescent : baseEnd_1538787 < baseStart_1538787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538828 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 2, 7]
def baseStart_1538828 : Nat := 118140960795 + 1538828 * 2 ^ 59
def prefixEnd_1538828 : Nat := 4983230072969 + 3 ^ 40 * 1538828 * 2
def baseEnd_1538828 : Nat := 526772272398007041382043

theorem tailTrace_1538828 : CollatzResearch.WordTrace tailWord_1538828 prefixEnd_1538828 526772272398007041382043 := by
  unfold tailWord_1538828
  simp only [CollatzResearch.WordTrace]
  refine ⟨28062834034548220872032569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37417112046064294496043425 28062834034548220872032569)
  ·
    refine ⟨21047125525911165654024427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28062834034548220872032569 21047125525911165654024427)
    ·
      refine ⟨31570688288866748481036641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21047125525911165654024427 31570688288866748481036641)
      ·
        refine ⟨23678016216650061360777481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31570688288866748481036641 23678016216650061360777481)
        ·
          refine ⟨17758512162487546020583111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23678016216650061360777481 17758512162487546020583111)
          ·
            refine ⟨26637768243731319030874667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17758512162487546020583111 26637768243731319030874667)
            ·
              refine ⟨39956652365596978546312001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26637768243731319030874667 39956652365596978546312001)
              ·
                refine ⟨29967489274197733909734001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39956652365596978546312001 29967489274197733909734001)
                ·
                  refine ⟨22475616955648300432300501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29967489274197733909734001 22475616955648300432300501)
                  ·
                    refine ⟨526772272398007041382043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22475616955648300432300501 526772272398007041382043)
                    ·
                      rfl

theorem cell22_1538828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_1538828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538828 prefixEnd_1538828 := by exact prefixLift 1538828
  have htrace : WordTrace (prefixWord ++ tailWord_1538828) baseStart_1538828 baseEnd_1538828 := by
    simpa [prefixWord, tailWord_1538828, baseEnd_1538828] using wordTrace_append hprefix tailTrace_1538828
  have hstable : (prefixWord ++ tailWord_1538828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538828).length < 2 ^ (prefixWord ++ tailWord_1538828).sum := by decide
  have hdescent : baseEnd_1538828 < baseStart_1538828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538834 : List Nat := [3, 2, 4, 1, 2, 1, 2, 1, 1, 5]
def baseStart_1538834 : Nat := 118140960795 + 1538834 * 2 ^ 59
def prefixEnd_1538834 : Nat := 4983230072969 + 3 ^ 40 * 1538834 * 2
def baseEnd_1538834 : Nat := 526774326320625025732025

theorem tailTrace_1538834 : CollatzResearch.WordTrace tailWord_1538834 prefixEnd_1538834 526774326320625025732025 := by
  unfold tailWord_1538834
  simp only [CollatzResearch.WordTrace]
  refine ⟨14031471726768676192195889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37417257938049803179189037 14031471726768676192195889)
  ·
    refine ⟨10523603795076507144146917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14031471726768676192195889 10523603795076507144146917)
    ·
      refine ⟨1973175711576845089527547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10523603795076507144146917 1973175711576845089527547)
      ·
        refine ⟨2959763567365267634291321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1973175711576845089527547 2959763567365267634291321)
        ·
          refine ⟨2219822675523950725718491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2959763567365267634291321 2219822675523950725718491)
          ·
            refine ⟨3329734013285926088577737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2219822675523950725718491 3329734013285926088577737)
            ·
              refine ⟨2497300509964444566433303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3329734013285926088577737 2497300509964444566433303)
              ·
                refine ⟨3745950764946666849649955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2497300509964444566433303 3745950764946666849649955)
                ·
                  refine ⟨5618926147420000274474933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3745950764946666849649955 5618926147420000274474933)
                  ·
                    refine ⟨526774326320625025732025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5618926147420000274474933 526774326320625025732025)
                    ·
                      rfl

theorem cell22_1538834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_1538834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538834 prefixEnd_1538834 := by exact prefixLift 1538834
  have htrace : WordTrace (prefixWord ++ tailWord_1538834) baseStart_1538834 baseEnd_1538834 := by
    simpa [prefixWord, tailWord_1538834, baseEnd_1538834] using wordTrace_append hprefix tailTrace_1538834
  have hstable : (prefixWord ++ tailWord_1538834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538834).length < 2 ^ (prefixWord ++ tailWord_1538834).sum := by decide
  have hdescent : baseEnd_1538834 < baseStart_1538834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538868 : List Nat := [2, 5, 1, 1, 4, 1, 1, 2, 2, 3]
def baseStart_1538868 : Nat := 118140960795 + 1538868 * 2 ^ 59
def prefixEnd_1538868 : Nat := 4983230072969 + 3 ^ 40 * 1538868 * 2
def baseEnd_1538868 : Nat := 526785965215460270381921

theorem tailTrace_1538868 : CollatzResearch.WordTrace tailWord_1538868 prefixEnd_1538868 526785965215460270381921 := by
  unfold tailWord_1538868
  simp only [CollatzResearch.WordTrace]
  refine ⟨28063563494475764287760629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37418084659301019050347505 28063563494475764287760629)
  ·
    refine ⟨2630959077607102901977559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28063563494475764287760629 2630959077607102901977559)
    ·
      refine ⟨3946438616410654352966339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2630959077607102901977559 3946438616410654352966339)
      ·
        refine ⟨5919657924615981529449509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3946438616410654352966339 5919657924615981529449509)
        ·
          refine ⟨1109935860865496536771783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5919657924615981529449509 1109935860865496536771783)
          ·
            refine ⟨1664903791298244805157675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1109935860865496536771783 1664903791298244805157675)
            ·
              refine ⟨2497355686947367207736513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664903791298244805157675 2497355686947367207736513)
              ·
                refine ⟨1873016765210525405802385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2497355686947367207736513 1873016765210525405802385)
                ·
                  refine ⟨1404762573907894054351789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1873016765210525405802385 1404762573907894054351789)
                  ·
                    refine ⟨526785965215460270381921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1404762573907894054351789 526785965215460270381921)
                    ·
                      rfl

theorem cell22_1538868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 2, 3].length) (baseStart_1538868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538868 prefixEnd_1538868 := by exact prefixLift 1538868
  have htrace : WordTrace (prefixWord ++ tailWord_1538868) baseStart_1538868 baseEnd_1538868 := by
    simpa [prefixWord, tailWord_1538868, baseEnd_1538868] using wordTrace_append hprefix tailTrace_1538868
  have hstable : (prefixWord ++ tailWord_1538868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538868).length < 2 ^ (prefixWord ++ tailWord_1538868).sum := by decide
  have hdescent : baseEnd_1538868 < baseStart_1538868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538879 : List Nat := [1, 1, 2, 2, 5, 1, 2, 4, 1, 3]
def baseStart_1538879 : Nat := 118140960795 + 1538879 * 2 ^ 59
def prefixEnd_1538879 : Nat := 4983230072969 + 3 ^ 40 * 1538879 * 2
def baseEnd_1538879 : Nat := 526789730740259908356887

theorem tailTrace_1538879 : CollatzResearch.WordTrace tailWord_1538879 prefixEnd_1538879 526789730740259908356887 := by
  unfold tailWord_1538879
  simp only [CollatzResearch.WordTrace]
  refine ⟨56127528191911677454171691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37418352127941118302781127 56127528191911677454171691)
  ·
    refine ⟨84191292287867516181257537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56127528191911677454171691 84191292287867516181257537)
    ·
      refine ⟨63143469215900637135943153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84191292287867516181257537 63143469215900637135943153)
      ·
        refine ⟨47357601911925477851957365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63143469215900637135943153 47357601911925477851957365)
        ·
          refine ⟨4439775179243013548621003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47357601911925477851957365 4439775179243013548621003)
          ·
            refine ⟨6659662768864520322931505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4439775179243013548621003 6659662768864520322931505)
            ·
              refine ⟨4994747076648390242198629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6659662768864520322931505 4994747076648390242198629)
              ·
                refine ⟨936515076871573170412243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4994747076648390242198629 936515076871573170412243)
                ·
                  refine ⟨1404772615307359755618365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 936515076871573170412243 1404772615307359755618365)
                  ·
                    refine ⟨526789730740259908356887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1404772615307359755618365 526789730740259908356887)
                    ·
                      rfl

theorem cell22_1538879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 4, 1, 3].length) (baseStart_1538879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538879 prefixEnd_1538879 := by exact prefixLift 1538879
  have htrace : WordTrace (prefixWord ++ tailWord_1538879) baseStart_1538879 baseEnd_1538879 := by
    simpa [prefixWord, tailWord_1538879, baseEnd_1538879] using wordTrace_append hprefix tailTrace_1538879
  have hstable : (prefixWord ++ tailWord_1538879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538879).length < 2 ^ (prefixWord ++ tailWord_1538879).sum := by decide
  have hdescent : baseEnd_1538879 < baseStart_1538879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538937 : List Nat := [1, 2, 1, 3, 2, 5, 1, 1, 6]
def baseStart_1538937 : Nat := 118140960795 + 1538937 * 2 ^ 59
def prefixEnd_1538937 : Nat := 4983230072969 + 3 ^ 40 * 1538937 * 2
def baseEnd_1538937 : Nat := 175603195108522363468903

theorem tailTrace_1538937 : CollatzResearch.WordTrace tailWord_1538937 prefixEnd_1538937 175603195108522363468903 := by
  unfold tailWord_1538937
  simp only [CollatzResearch.WordTrace]
  refine ⟨56129643625701553359783065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37419762417134368906522043 56129643625701553359783065)
  ·
    refine ⟨42097232719276165019837299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56129643625701553359783065 42097232719276165019837299)
    ·
      refine ⟨63145849078914247529755949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42097232719276165019837299 63145849078914247529755949)
      ·
        refine ⟨23679693404592842823658481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63145849078914247529755949 23679693404592842823658481)
        ·
          refine ⟨17759770053444632117743861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23679693404592842823658481 17759770053444632117743861)
          ·
            refine ⟨1664978442510434261038487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17759770053444632117743861 1664978442510434261038487)
            ·
              refine ⟨2497467663765651391557731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1664978442510434261038487 2497467663765651391557731)
              ·
                refine ⟨3746201495648477087336597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2497467663765651391557731 3746201495648477087336597)
                ·
                  refine ⟨175603195108522363468903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3746201495648477087336597 175603195108522363468903)
                  ·
                    rfl

theorem cell22_1538937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 6].length) (baseStart_1538937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538937 prefixEnd_1538937 := by exact prefixLift 1538937
  have htrace : WordTrace (prefixWord ++ tailWord_1538937) baseStart_1538937 baseEnd_1538937 := by
    simpa [prefixWord, tailWord_1538937, baseEnd_1538937] using wordTrace_append hprefix tailTrace_1538937
  have hstable : (prefixWord ++ tailWord_1538937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538937).length < 2 ^ (prefixWord ++ tailWord_1538937).sum := by decide
  have hdescent : baseEnd_1538937 < baseStart_1538937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538965 : List Nat := [1, 3, 2, 1, 1, 4, 2, 8]
def baseStart_1538965 : Nat := 118140960795 + 1538965 * 2 ^ 59
def prefixEnd_1538965 : Nat := 4983230072969 + 3 ^ 40 * 1538965 * 2
def baseEnd_1538965 : Nat := 58535463366420483411847

theorem tailTrace_1538965 : CollatzResearch.WordTrace tailWord_1538965 prefixEnd_1538965 58535463366420483411847 := by
  unfold tailWord_1538965
  simp only [CollatzResearch.WordTrace]
  refine ⟨56130664869600114141802349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37420443246400076094534899 56130664869600114141802349)
  ·
    refine ⟨21048999326100042803175881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56130664869600114141802349 21048999326100042803175881)
    ·
      refine ⟨15786749494575032102381911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21048999326100042803175881 15786749494575032102381911)
      ·
        refine ⟨23680124241862548153572867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15786749494575032102381911 23680124241862548153572867)
        ·
          refine ⟨35520186362793822230359301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23680124241862548153572867 35520186362793822230359301)
          ·
            refine ⟨6660034943023841668192369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35520186362793822230359301 6660034943023841668192369)
            ·
              refine ⟨4995026207267881251144277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6660034943023841668192369 4995026207267881251144277)
              ·
                refine ⟨58535463366420483411847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4995026207267881251144277 58535463366420483411847)
                ·
                  rfl

theorem cell22_1538965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 8].length) (baseStart_1538965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538965 prefixEnd_1538965 := by exact prefixLift 1538965
  have htrace : WordTrace (prefixWord ++ tailWord_1538965) baseStart_1538965 baseEnd_1538965 := by
    simpa [prefixWord, tailWord_1538965, baseEnd_1538965] using wordTrace_append hprefix tailTrace_1538965
  have hstable : (prefixWord ++ tailWord_1538965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538965).length < 2 ^ (prefixWord ++ tailWord_1538965).sum := by decide
  have hdescent : baseEnd_1538965 < baseStart_1538965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1538967 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 2, 4]
def baseStart_1538967 : Nat := 118140960795 + 1538967 * 2 ^ 59
def prefixEnd_1538967 : Nat := 4983230072969 + 3 ^ 40 * 1538967 * 2
def baseEnd_1538967 : Nat := 526819854938657012156617

theorem tailTrace_1538967 : CollatzResearch.WordTrace tailWord_1538967 prefixEnd_1538967 526819854938657012156617 := by
  unfold tailWord_1538967
  simp only [CollatzResearch.WordTrace]
  refine ⟨56130737815592868483375155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37420491877061912322250103 56130737815592868483375155)
  ·
    refine ⟨84196106723389302725062733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56130737815592868483375155 84196106723389302725062733)
    ·
      refine ⟨31573540021270988521898525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84196106723389302725062733 31573540021270988521898525)
      ·
        refine ⟨11840077507976620695711947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31573540021270988521898525 11840077507976620695711947)
        ·
          refine ⟨17760116261964931043567921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11840077507976620695711947 17760116261964931043567921)
          ·
            refine ⟨13320087196473698282675941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17760116261964931043567921 13320087196473698282675941)
            ·
              refine ⟨2497516349338818428001739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13320087196473698282675941 2497516349338818428001739)
              ·
                refine ⟨3746274524008227642002609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2497516349338818428001739 3746274524008227642002609)
                ·
                  refine ⟨2809705893006170731501957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3746274524008227642002609 2809705893006170731501957)
                  ·
                    refine ⟨526819854938657012156617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2809705893006170731501957 526819854938657012156617)
                    ·
                      rfl

theorem cell22_1538967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_1538967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1538967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1538967 prefixEnd_1538967 := by exact prefixLift 1538967
  have htrace : WordTrace (prefixWord ++ tailWord_1538967) baseStart_1538967 baseEnd_1538967 := by
    simpa [prefixWord, tailWord_1538967, baseEnd_1538967] using wordTrace_append hprefix tailTrace_1538967
  have hstable : (prefixWord ++ tailWord_1538967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1538967).length < 2 ^ (prefixWord ++ tailWord_1538967).sum := by decide
  have hdescent : baseEnd_1538967 < baseStart_1538967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1538967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539025 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 1, 7]
def baseStart_1539025 : Nat := 118140960795 + 1539025 * 2 ^ 59
def prefixEnd_1539025 : Nat := 4983230072969 + 3 ^ 40 * 1539025 * 2
def baseEnd_1539025 : Nat := 526839709523964194206439

theorem tailTrace_1539025 : CollatzResearch.WordTrace tailWord_1539025 prefixEnd_1539025 526839709523964194206439 := by
  unfold tailWord_1539025
  simp only [CollatzResearch.WordTrace]
  refine ⟨56132853249382744388986529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37421902166255162925991019 56132853249382744388986529)
  ·
    refine ⟨42099639937037058291739897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56132853249382744388986529 42099639937037058291739897)
    ·
      refine ⟨31574729952777793718804923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42099639937037058291739897 31574729952777793718804923)
      ·
        refine ⟨47362094929166690578207385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31574729952777793718804923 47362094929166690578207385)
        ·
          refine ⟨35521571196875017933655539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47362094929166690578207385 35521571196875017933655539)
          ·
            refine ⟨53282356795312526900483309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35521571196875017933655539 53282356795312526900483309)
            ·
              refine ⟨19980883798242197587681241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53282356795312526900483309 19980883798242197587681241)
              ·
                refine ⟨14985662848681648190760931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19980883798242197587681241 14985662848681648190760931)
                ·
                  refine ⟨22478494273022472286141397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14985662848681648190760931 22478494273022472286141397)
                  ·
                    refine ⟨526839709523964194206439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22478494273022472286141397 526839709523964194206439)
                    ·
                      rfl

theorem cell22_1539025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_1539025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539025 prefixEnd_1539025 := by exact prefixLift 1539025
  have htrace : WordTrace (prefixWord ++ tailWord_1539025) baseStart_1539025 baseEnd_1539025 := by
    simpa [prefixWord, tailWord_1539025, baseEnd_1539025] using wordTrace_append hprefix tailTrace_1539025
  have hstable : (prefixWord ++ tailWord_1539025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539025).length < 2 ^ (prefixWord ++ tailWord_1539025).sum := by decide
  have hdescent : baseEnd_1539025 < baseStart_1539025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539134 : List Nat := [4, 2, 1, 3, 1, 1, 2, 8]
def baseStart_1539134 : Nat := 118140960795 + 1539134 * 2 ^ 59
def prefixEnd_1539134 : Nat := 4983230072969 + 3 ^ 40 * 1539134 * 2
def baseEnd_1539134 : Nat := 58541891383502693692345

theorem tailTrace_1539134 : CollatzResearch.WordTrace tailWord_1539134 prefixEnd_1539134 58541891383502693692345 := by
  unfold tailWord_1539134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7017103600748482000588057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37424552537325237336469637 7017103600748482000588057)
  ·
    refine ⟨5262827700561361500441043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7017103600748482000588057 5262827700561361500441043)
    ·
      refine ⟨7894241550842042250661565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5262827700561361500441043 7894241550842042250661565)
      ·
        refine ⟨2960340581565765843998087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7894241550842042250661565 2960340581565765843998087)
        ·
          refine ⟨4440510872348648765997131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2960340581565765843998087 4440510872348648765997131)
          ·
            refine ⟨6660766308522973148995697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4440510872348648765997131 6660766308522973148995697)
            ·
              refine ⟨4995574731392229861746773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6660766308522973148995697 4995574731392229861746773)
              ·
                refine ⟨58541891383502693692345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4995574731392229861746773 58541891383502693692345)
                ·
                  rfl

theorem cell22_1539134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_1539134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539134 prefixEnd_1539134 := by exact prefixLift 1539134
  have htrace : WordTrace (prefixWord ++ tailWord_1539134) baseStart_1539134 baseEnd_1539134 := by
    simpa [prefixWord, tailWord_1539134, baseEnd_1539134] using wordTrace_append hprefix tailTrace_1539134
  have hstable : (prefixWord ++ tailWord_1539134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539134).length < 2 ^ (prefixWord ++ tailWord_1539134).sum := by decide
  have hdescent : baseEnd_1539134 < baseStart_1539134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539177 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 1, 7]
def baseStart_1539177 : Nat := 118140960795 + 1539177 * 2 ^ 59
def prefixEnd_1539177 : Nat := 4983230072969 + 3 ^ 40 * 1539177 * 2
def baseEnd_1539177 : Nat := 526891742230286464405973

theorem tailTrace_1539177 : CollatzResearch.WordTrace tailWord_1539177 prefixEnd_1539177 526891742230286464405973 := by
  unfold tailWord_1539177
  simp only [CollatzResearch.WordTrace]
  refine ⟨56138397144832074348519785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37425598096554716232346523 56138397144832074348519785)
  ·
    refine ⟨42103797858624055761389839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56138397144832074348519785 42103797858624055761389839)
    ·
      refine ⟨63155696787936083642084759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42103797858624055761389839 63155696787936083642084759)
      ·
        refine ⟨94733545181904125463127139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63155696787936083642084759 94733545181904125463127139)
        ·
          refine ⟨142100317772856188194690709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94733545181904125463127139 142100317772856188194690709)
          ·
            refine ⟨6660952395602633821626127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142100317772856188194690709 6660952395602633821626127)
            ·
              refine ⟨9991428593403950732439191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6660952395602633821626127 9991428593403950732439191)
              ·
                refine ⟨14987142890105926098658787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9991428593403950732439191 14987142890105926098658787)
                ·
                  refine ⟨22480714335158889147988181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14987142890105926098658787 22480714335158889147988181)
                  ·
                    refine ⟨526891742230286464405973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22480714335158889147988181 526891742230286464405973)
                    ·
                      rfl

theorem cell22_1539177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_1539177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539177 prefixEnd_1539177 := by exact prefixLift 1539177
  have htrace : WordTrace (prefixWord ++ tailWord_1539177) baseStart_1539177 baseEnd_1539177 := by
    simpa [prefixWord, tailWord_1539177, baseEnd_1539177] using wordTrace_append hprefix tailTrace_1539177
  have hstable : (prefixWord ++ tailWord_1539177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539177).length < 2 ^ (prefixWord ++ tailWord_1539177).sum := by decide
  have hdescent : baseEnd_1539177 < baseStart_1539177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539207 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 10]
def baseStart_1539207 : Nat := 118140960795 + 1539207 * 2 ^ 59
def prefixEnd_1539207 : Nat := 4983230072969 + 3 ^ 40 * 1539207 * 2
def baseEnd_1539207 : Nat := 175634003947792128718627

theorem tailTrace_1539207 : CollatzResearch.WordTrace tailWord_1539207 prefixEnd_1539207 175634003947792128718627 := by
  unfold tailWord_1539207
  simp only [CollatzResearch.WordTrace]
  refine ⟨56139491334723389472111875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37426327556482259648074583 56139491334723389472111875)
  ·
    refine ⟨84209237002085084208167813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56139491334723389472111875 84209237002085084208167813)
    ·
      refine ⟨15789231937890953289031465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84209237002085084208167813 15789231937890953289031465)
      ·
        refine ⟨11841923953418214966773599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15789231937890953289031465 11841923953418214966773599)
        ·
          refine ⟨17762885930127322450160399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11841923953418214966773599 17762885930127322450160399)
          ·
            refine ⟨26644328895190983675240599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17762885930127322450160399 26644328895190983675240599)
            ·
              refine ⟨39966493342786475512860899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26644328895190983675240599 39966493342786475512860899)
              ·
                refine ⟨59949740014179713269291349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39966493342786475512860899 59949740014179713269291349)
                ·
                  refine ⟨175634003947792128718627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 59949740014179713269291349 175634003947792128718627)
                  ·
                    rfl

theorem cell22_1539207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 10].length) (baseStart_1539207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539207 prefixEnd_1539207 := by exact prefixLift 1539207
  have htrace : WordTrace (prefixWord ++ tailWord_1539207) baseStart_1539207 baseEnd_1539207 := by
    simpa [prefixWord, tailWord_1539207, baseEnd_1539207] using wordTrace_append hprefix tailTrace_1539207
  have hstable : (prefixWord ++ tailWord_1539207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539207).length < 2 ^ (prefixWord ++ tailWord_1539207).sum := by decide
  have hdescent : baseEnd_1539207 < baseStart_1539207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539224 : List Nat := [2, 1, 2, 4, 2, 1, 1, 3, 6]
def baseStart_1539224 : Nat := 118140960795 + 1539224 * 2 ^ 59
def prefixEnd_1539224 : Nat := 4983230072969 + 3 ^ 40 * 1539224 * 2
def baseEnd_1539224 : Nat := 175635943763598002826943

theorem tailTrace_1539224 : CollatzResearch.WordTrace tailWord_1539224 prefixEnd_1539224 175635943763598002826943 := by
  unfold tailWord_1539224
  simp only [CollatzResearch.WordTrace]
  refine ⟨28070055687830900687740363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37426740917107867583653817 28070055687830900687740363)
  ·
    refine ⟨42105083531746351031610545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28070055687830900687740363 42105083531746351031610545)
    ·
      refine ⟨31578812648809763273707909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42105083531746351031610545 31578812648809763273707909)
      ·
        refine ⟨5921027371651830613820233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31578812648809763273707909 5921027371651830613820233)
        ·
          refine ⟨4440770528738872960365175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5921027371651830613820233 4440770528738872960365175)
          ·
            refine ⟨6661155793108309440547763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4440770528738872960365175 6661155793108309440547763)
            ·
              refine ⟨9991733689662464160821645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6661155793108309440547763 9991733689662464160821645)
              ·
                refine ⟨3746900133623424060308117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9991733689662464160821645 3746900133623424060308117)
                ·
                  refine ⟨175635943763598002826943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3746900133623424060308117 175635943763598002826943)
                  ·
                    rfl

theorem cell22_1539224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 6].length) (baseStart_1539224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539224 prefixEnd_1539224 := by exact prefixLift 1539224
  have htrace : WordTrace (prefixWord ++ tailWord_1539224) baseStart_1539224 baseEnd_1539224 := by
    simpa [prefixWord, tailWord_1539224, baseEnd_1539224] using wordTrace_append hprefix tailTrace_1539224
  have hstable : (prefixWord ++ tailWord_1539224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539224).length < 2 ^ (prefixWord ++ tailWord_1539224).sum := by decide
  have hdescent : baseEnd_1539224 < baseStart_1539224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539331 : List Nat := [1, 1, 1, 3, 2, 5, 2, 2, 5]
def baseStart_1539331 : Nat := 118140960795 + 1539331 * 2 ^ 59
def prefixEnd_1539331 : Nat := 4983230072969 + 3 ^ 40 * 1539331 * 2
def baseEnd_1539331 : Nat := 175648153192493798685167

theorem tailTrace_1539331 : CollatzResearch.WordTrace tailWord_1539331 prefixEnd_1539331 175648153192493798685167 := by
  unfold tailWord_1539331
  simp only [CollatzResearch.WordTrace]
  refine ⟨56144013986274158649625847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37429342657516105766417231 56144013986274158649625847)
  ·
    refine ⟨84216020979411237974438771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56144013986274158649625847 84216020979411237974438771)
    ·
      refine ⟨126324031469116856961658157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84216020979411237974438771 126324031469116856961658157)
      ·
        refine ⟨47371511800918821360621809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126324031469116856961658157 47371511800918821360621809)
        ·
          refine ⟨35528633850689116020466357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47371511800918821360621809 35528633850689116020466357)
          ·
            refine ⟨3330809423502104626918721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35528633850689116020466357 3330809423502104626918721)
            ·
              refine ⟨2498107067626578470189041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3330809423502104626918721 2498107067626578470189041)
              ·
                refine ⟨1873580300719933852641781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2498107067626578470189041 1873580300719933852641781)
                ·
                  refine ⟨175648153192493798685167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1873580300719933852641781 175648153192493798685167)
                  ·
                    rfl

theorem cell22_1539331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 2, 5].length) (baseStart_1539331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539331 prefixEnd_1539331 := by exact prefixLift 1539331
  have htrace : WordTrace (prefixWord ++ tailWord_1539331) baseStart_1539331 baseEnd_1539331 := by
    simpa [prefixWord, tailWord_1539331, baseEnd_1539331] using wordTrace_append hprefix tailTrace_1539331
  have hstable : (prefixWord ++ tailWord_1539331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539331).length < 2 ^ (prefixWord ++ tailWord_1539331).sum := by decide
  have hdescent : baseEnd_1539331 < baseStart_1539331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539361 : List Nat := [1, 2, 3, 2, 1, 1, 1, 6, 1, 4]
def baseStart_1539361 : Nat := 118140960795 + 1539361 * 2 ^ 59
def prefixEnd_1539361 : Nat := 4983230072969 + 3 ^ 40 * 1539361 * 2
def baseEnd_1539361 : Nat := 526954729190571317805409

theorem tailTrace_1539361 : CollatzResearch.WordTrace tailWord_1539361 prefixEnd_1539361 526954729190571317805409 := by
  unfold tailWord_1539361
  simp only [CollatzResearch.WordTrace]
  refine ⟨56145108176165473773217937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37430072117443649182145291 56145108176165473773217937)
  ·
    refine ⟨42108831132124105329913453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56145108176165473773217937 42108831132124105329913453)
    ·
      refine ⟨15790811674546539498717545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42108831132124105329913453 15790811674546539498717545)
      ·
        refine ⟨11843108755909904624038159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15790811674546539498717545 11843108755909904624038159)
        ·
          refine ⟨17764663133864856936057239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11843108755909904624038159 17764663133864856936057239)
          ·
            refine ⟨26646994700797285404085859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17764663133864856936057239 26646994700797285404085859)
            ·
              refine ⟨39970492051195928106128789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26646994700797285404085859 39970492051195928106128789)
              ·
                refine ⟨1873616814899809129974787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39970492051195928106128789 1873616814899809129974787)
                ·
                  refine ⟨2810425222349713694962181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873616814899809129974787 2810425222349713694962181)
                  ·
                    refine ⟨526954729190571317805409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2810425222349713694962181 526954729190571317805409)
                    ·
                      rfl

theorem cell22_1539361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_1539361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539361 prefixEnd_1539361 := by exact prefixLift 1539361
  have htrace : WordTrace (prefixWord ++ tailWord_1539361) baseStart_1539361 baseEnd_1539361 := by
    simpa [prefixWord, tailWord_1539361, baseEnd_1539361] using wordTrace_append hprefix tailTrace_1539361
  have hstable : (prefixWord ++ tailWord_1539361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539361).length < 2 ^ (prefixWord ++ tailWord_1539361).sum := by decide
  have hdescent : baseEnd_1539361 < baseStart_1539361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539378 : List Nat := [3, 2, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_1539378 : Nat := 118140960795 + 1539378 * 2 ^ 59
def prefixEnd_1539378 : Nat := 4983230072969 + 3 ^ 40 * 1539378 * 2
def baseEnd_1539378 : Nat := 526960548637988940130357

theorem tailTrace_1539378 : CollatzResearch.WordTrace tailWord_1539378 prefixEnd_1539378 526960548637988940130357 := by
  unfold tailWord_1539378
  simp only [CollatzResearch.WordTrace]
  refine ⟨14036432054275971419146697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37430485478069257117724525 14036432054275971419146697)
  ·
    refine ⟨10527324040706978564360023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14036432054275971419146697 10527324040706978564360023)
    ·
      refine ⟨15790986061060467846540035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10527324040706978564360023 15790986061060467846540035)
      ·
        refine ⟨23686479091590701769810053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15790986061060467846540035 23686479091590701769810053)
        ·
          refine ⟨4441214829673256581839385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23686479091590701769810053 4441214829673256581839385)
          ·
            refine ⟨3330911122254942436379539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4441214829673256581839385 3330911122254942436379539)
            ·
              refine ⟨4996366683382413654569309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3330911122254942436379539 4996366683382413654569309)
              ·
                refine ⟨1873637506268405120463491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4996366683382413654569309 1873637506268405120463491)
                ·
                  refine ⟨2810456259402607680695237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1873637506268405120463491 2810456259402607680695237)
                  ·
                    refine ⟨526960548637988940130357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2810456259402607680695237 526960548637988940130357)
                    ·
                      rfl

theorem cell22_1539378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_1539378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539378 prefixEnd_1539378 := by exact prefixLift 1539378
  have htrace : WordTrace (prefixWord ++ tailWord_1539378) baseStart_1539378 baseEnd_1539378 := by
    simpa [prefixWord, tailWord_1539378, baseEnd_1539378] using wordTrace_append hprefix tailTrace_1539378
  have hstable : (prefixWord ++ tailWord_1539378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539378).length < 2 ^ (prefixWord ++ tailWord_1539378).sum := by decide
  have hdescent : baseEnd_1539378 < baseStart_1539378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539382 : List Nat := [5, 1, 2, 3, 1, 2, 1, 2, 5]
def baseStart_1539382 : Nat := 118140960795 + 1539382 * 2 ^ 59
def prefixEnd_1539382 : Nat := 4983230072969 + 3 ^ 40 * 1539382 * 2
def baseEnd_1539382 : Nat := 175653972639911421010115

theorem tailTrace_1539382 : CollatzResearch.WordTrace tailWord_1539382 prefixEnd_1539382 175653972639911421010115 := by
  unfold tailWord_1539382
  simp only [CollatzResearch.WordTrace]
  refine ⟨3509117131818087147483275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37430582739392929573154933 3509117131818087147483275)
  ·
    refine ⟨5263675697727130721224913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3509117131818087147483275 5263675697727130721224913)
    ·
      refine ⟨3947756773295348040918685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5263675697727130721224913 3947756773295348040918685)
      ·
        refine ⟨1480408789985755515344507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3947756773295348040918685 1480408789985755515344507)
        ·
          refine ⟨2220613184978633273016761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1480408789985755515344507 2220613184978633273016761)
          ·
            refine ⟨1665459888733974954762571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2220613184978633273016761 1665459888733974954762571)
            ·
              refine ⟨2498189833100962432143857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1665459888733974954762571 2498189833100962432143857)
              ·
                refine ⟨1873642374825721824107893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2498189833100962432143857 1873642374825721824107893)
                ·
                  refine ⟨175653972639911421010115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1873642374825721824107893 175653972639911421010115)
                  ·
                    rfl

theorem cell22_1539382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_1539382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539382 prefixEnd_1539382 := by exact prefixLift 1539382
  have htrace : WordTrace (prefixWord ++ tailWord_1539382) baseStart_1539382 baseEnd_1539382 := by
    simpa [prefixWord, tailWord_1539382, baseEnd_1539382] using wordTrace_append hprefix tailTrace_1539382
  have hstable : (prefixWord ++ tailWord_1539382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539382).length < 2 ^ (prefixWord ++ tailWord_1539382).sum := by decide
  have hdescent : baseEnd_1539382 < baseStart_1539382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539393 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 6]
def baseStart_1539393 : Nat := 118140960795 + 1539393 * 2 ^ 59
def prefixEnd_1539393 : Nat := 4983230072969 + 3 ^ 40 * 1539393 * 2
def baseEnd_1539393 : Nat := 175655227814844633668437

theorem tailTrace_1539393 : CollatzResearch.WordTrace tailWord_1539393 prefixEnd_1539393 175655227814844633668437 := by
  unfold tailWord_1539393
  simp only [CollatzResearch.WordTrace]
  refine ⟨56146275312049543238382833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37430850208033028825588555 56146275312049543238382833)
  ·
    refine ⟨42109706484037157428787125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56146275312049543238382833 42109706484037157428787125)
    ·
      refine ⟨3947784982878483508948793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42109706484037157428787125 3947784982878483508948793)
      ·
        refine ⟨2960838737158862631711595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3947784982878483508948793 2960838737158862631711595)
        ·
          refine ⟨4441258105738293947567393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2960838737158862631711595 4441258105738293947567393)
          ·
            refine ⟨3330943579303720460675545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4441258105738293947567393 3330943579303720460675545)
            ·
              refine ⟨2498207684477790345506659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3330943579303720460675545 2498207684477790345506659)
              ·
                refine ⟨3747311526716685518259989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2498207684477790345506659 3747311526716685518259989)
                ·
                  refine ⟨175655227814844633668437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3747311526716685518259989 175655227814844633668437)
                  ·
                    rfl

theorem cell22_1539393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 6].length) (baseStart_1539393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539393 prefixEnd_1539393 := by exact prefixLift 1539393
  have htrace : WordTrace (prefixWord ++ tailWord_1539393) baseStart_1539393 baseEnd_1539393 := by
    simpa [prefixWord, tailWord_1539393, baseEnd_1539393] using wordTrace_append hprefix tailTrace_1539393
  have hstable : (prefixWord ++ tailWord_1539393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539393).length < 2 ^ (prefixWord ++ tailWord_1539393).sum := by decide
  have hdescent : baseEnd_1539393 < baseStart_1539393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539511 : List Nat := [1, 1, 3, 1, 3, 2, 2, 3, 6]
def baseStart_1539511 : Nat := 118140960795 + 1539511 * 2 ^ 59
def prefixEnd_1539511 : Nat := 4983230072969 + 3 ^ 40 * 1539511 * 2
def baseEnd_1539511 : Nat := 175668692418673642184983

theorem tailTrace_1539511 : CollatzResearch.WordTrace tailWord_1539511 prefixEnd_1539511 175668692418673642184983 := by
  unfold tailWord_1539511
  simp only [CollatzResearch.WordTrace]
  refine ⟨56150579125622049391178387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37433719417081366260785591 56150579125622049391178387)
  ·
    refine ⟨84225868688433074086767581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56150579125622049391178387 84225868688433074086767581)
    ·
      refine ⟨31584700758162402782537843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84225868688433074086767581 31584700758162402782537843)
      ·
        refine ⟨47377051137243604173806765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31584700758162402782537843 47377051137243604173806765)
        ·
          refine ⟨17766394176466351565177537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47377051137243604173806765 17766394176466351565177537)
          ·
            refine ⟨13324795632349763673883153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17766394176466351565177537 13324795632349763673883153)
            ·
              refine ⟨9993596724262322755412365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13324795632349763673883153 9993596724262322755412365)
              ·
                refine ⟨3747598771598371033279637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9993596724262322755412365 3747598771598371033279637)
                ·
                  refine ⟨175668692418673642184983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3747598771598371033279637 175668692418673642184983)
                  ·
                    rfl

theorem cell22_1539511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 3, 6].length) (baseStart_1539511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539511 prefixEnd_1539511 := by exact prefixLift 1539511
  have htrace : WordTrace (prefixWord ++ tailWord_1539511) baseStart_1539511 baseEnd_1539511 := by
    simpa [prefixWord, tailWord_1539511, baseEnd_1539511] using wordTrace_append hprefix tailTrace_1539511
  have hstable : (prefixWord ++ tailWord_1539511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539511).length < 2 ^ (prefixWord ++ tailWord_1539511).sum := by decide
  have hdescent : baseEnd_1539511 < baseStart_1539511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539545 : List Nat := [1, 2, 1, 2, 4, 3, 2, 3, 4]
def baseStart_1539545 : Nat := 118140960795 + 1539545 * 2 ^ 59
def prefixEnd_1539545 : Nat := 4983230072969 + 3 ^ 40 * 1539545 * 2
def baseEnd_1539545 : Nat := 175672572050285390401615

theorem tailTrace_1539545 : CollatzResearch.WordTrace tailWord_1539545 prefixEnd_1539545 175672572050285390401615 := by
  unfold tailWord_1539545
  simp only [CollatzResearch.WordTrace]
  refine ⟨56151819207498873197916089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37434546138332582131944059 56151819207498873197916089)
  ·
    refine ⟨42113864405624154898437067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56151819207498873197916089 42113864405624154898437067)
    ·
      refine ⟨63170796608436232347655601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42113864405624154898437067 63170796608436232347655601)
      ·
        refine ⟨47378097456327174260741701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63170796608436232347655601 47378097456327174260741701)
        ·
          refine ⟨8883393273061345173889069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47378097456327174260741701 8883393273061345173889069)
          ·
            refine ⟨3331272477398004440208401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8883393273061345173889069 3331272477398004440208401)
            ·
              refine ⟨2498454358048503330156301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3331272477398004440208401 2498454358048503330156301)
              ·
                refine ⟨936920384268188748808613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2498454358048503330156301 936920384268188748808613)
                ·
                  refine ⟨175672572050285390401615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 936920384268188748808613 175672572050285390401615)
                  ·
                    rfl

theorem cell22_1539545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 3, 4].length) (baseStart_1539545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539545 prefixEnd_1539545 := by exact prefixLift 1539545
  have htrace : WordTrace (prefixWord ++ tailWord_1539545) baseStart_1539545 baseEnd_1539545 := by
    simpa [prefixWord, tailWord_1539545, baseEnd_1539545] using wordTrace_append hprefix tailTrace_1539545
  have hstable : (prefixWord ++ tailWord_1539545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539545).length < 2 ^ (prefixWord ++ tailWord_1539545).sum := by decide
  have hdescent : baseEnd_1539545 < baseStart_1539545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539601 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 9]
def baseStart_1539601 : Nat := 118140960795 + 1539601 * 2 ^ 59
def prefixEnd_1539601 : Nat := 4983230072969 + 3 ^ 40 * 1539601 * 2
def baseEnd_1539601 : Nat := 175678962031763563934891

theorem tailTrace_1539601 : CollatzResearch.WordTrace tailWord_1539601 prefixEnd_1539601 175678962031763563934891 := by
  unfold tailWord_1539601
  simp only [CollatzResearch.WordTrace]
  refine ⟨56153861695295994761954657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37435907796863996507969771 56153861695295994761954657)
  ·
    refine ⟨42115396271471996071465993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56153861695295994761954657 42115396271471996071465993)
    ·
      refine ⟨31586547203603997053599495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42115396271471996071465993 31586547203603997053599495)
      ·
        refine ⟨47379820805405995580399243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31586547203603997053599495 47379820805405995580399243)
        ·
          refine ⟨71069731208108993370598865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47379820805405995580399243 71069731208108993370598865)
          ·
            refine ⟨53302298406081745027949149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71069731208108993370598865 53302298406081745027949149)
            ·
              refine ⟨19988361902280654385480931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53302298406081745027949149 19988361902280654385480931)
              ·
                refine ⟨29982542853420981578221397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19988361902280654385480931 29982542853420981578221397)
                ·
                  refine ⟨175678962031763563934891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29982542853420981578221397 175678962031763563934891)
                  ·
                    rfl

theorem cell22_1539601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 9].length) (baseStart_1539601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539601 prefixEnd_1539601 := by exact prefixLift 1539601
  have htrace : WordTrace (prefixWord ++ tailWord_1539601) baseStart_1539601 baseEnd_1539601 := by
    simpa [prefixWord, tailWord_1539601, baseEnd_1539601] using wordTrace_append hprefix tailTrace_1539601
  have hstable : (prefixWord ++ tailWord_1539601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539601).length < 2 ^ (prefixWord ++ tailWord_1539601).sum := by decide
  have hdescent : baseEnd_1539601 < baseStart_1539601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539618 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 7]
def baseStart_1539618 : Nat := 118140960795 + 1539618 * 2 ^ 59
def prefixEnd_1539618 : Nat := 4983230072969 + 3 ^ 40 * 1539618 * 2
def baseEnd_1539618 : Nat := 175680901847569438043207

theorem tailTrace_1539618 : CollatzResearch.WordTrace tailWord_1539618 prefixEnd_1539618 175680901847569438043207 := by
  unfold tailWord_1539618
  simp only [CollatzResearch.WordTrace]
  refine ⟨14038620434058601666330877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37436321157489604443549005 14038620434058601666330877)
  ·
    refine ⟨5264482662771975624874079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14038620434058601666330877 5264482662771975624874079)
    ·
      refine ⟨7896723994157963437311119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5264482662771975624874079 7896723994157963437311119)
      ·
        refine ⟨11845085991236945155966679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7896723994157963437311119 11845085991236945155966679)
        ·
          refine ⟨17767628986855417733950019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11845085991236945155966679 17767628986855417733950019)
          ·
            refine ⟨26651443480283126600925029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17767628986855417733950019 26651443480283126600925029)
            ·
              refine ⟨4997145652553086237673443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26651443480283126600925029 4997145652553086237673443)
              ·
                refine ⟨7495718478829629356510165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4997145652553086237673443 7495718478829629356510165)
                ·
                  refine ⟨175680901847569438043207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7495718478829629356510165 175680901847569438043207)
                  ·
                    rfl

theorem cell22_1539618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_1539618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539618 prefixEnd_1539618 := by exact prefixLift 1539618
  have htrace : WordTrace (prefixWord ++ tailWord_1539618) baseStart_1539618 baseEnd_1539618 := by
    simpa [prefixWord, tailWord_1539618, baseEnd_1539618] using wordTrace_append hprefix tailTrace_1539618
  have hstable : (prefixWord ++ tailWord_1539618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539618).length < 2 ^ (prefixWord ++ tailWord_1539618).sum := by decide
  have hdescent : baseEnd_1539618 < baseStart_1539618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539635 : List Nat := [1, 1, 1, 2, 4, 3, 4, 1, 5]
def baseStart_1539635 : Nat := 118140960795 + 1539635 * 2 ^ 59
def prefixEnd_1539635 : Nat := 4983230072969 + 3 ^ 40 * 1539635 * 2
def baseEnd_1539635 : Nat := 175682841663375312151523

theorem tailTrace_1539635 : CollatzResearch.WordTrace tailWord_1539635 prefixEnd_1539635 175682841663375312151523 := by
  unfold tailWord_1539635
  simp only [CollatzResearch.WordTrace]
  refine ⟨56155101777172818568692359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37436734518115212379128239 56155101777172818568692359)
  ·
    refine ⟨84232652665759227853038539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56155101777172818568692359 84232652665759227853038539)
    ·
      refine ⟨126348978998638841779557809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84232652665759227853038539 126348978998638841779557809)
      ·
        refine ⟨94761734248979131334668357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126348978998638841779557809 94761734248979131334668357)
        ·
          refine ⟨17767825171683587125250317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94761734248979131334668357 17767825171683587125250317)
          ·
            refine ⟨6662934439381345171968869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17767825171683587125250317 6662934439381345171968869)
            ·
              refine ⟨1249300207384002219744163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6662934439381345171968869 1249300207384002219744163)
              ·
                refine ⟨1873950311076003329616245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1249300207384002219744163 1873950311076003329616245)
                ·
                  refine ⟨175682841663375312151523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1873950311076003329616245 175682841663375312151523)
                  ·
                    rfl

theorem cell22_1539635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 1, 5].length) (baseStart_1539635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539635 prefixEnd_1539635 := by exact prefixLift 1539635
  have htrace : WordTrace (prefixWord ++ tailWord_1539635) baseStart_1539635 baseEnd_1539635 := by
    simpa [prefixWord, tailWord_1539635, baseEnd_1539635] using wordTrace_append hprefix tailTrace_1539635
  have hstable : (prefixWord ++ tailWord_1539635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539635).length < 2 ^ (prefixWord ++ tailWord_1539635).sum := by decide
  have hdescent : baseEnd_1539635 < baseStart_1539635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539716 : List Nat := [2, 3, 2, 1, 5, 1, 2, 1, 1, 4]
def baseStart_1539716 : Nat := 118140960795 + 1539716 * 2 ^ 59
def prefixEnd_1539716 : Nat := 4983230072969 + 3 ^ 40 * 1539716 * 2
def baseEnd_1539716 : Nat := 527076252945468725179321

theorem tailTrace_1539716 : CollatzResearch.WordTrace tailWord_1539716 prefixEnd_1539716 527076252945468725179321 := by
  unfold tailWord_1539716
  simp only [CollatzResearch.WordTrace]
  refine ⟨28079028044939684701195501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37438704059919579601594001 28079028044939684701195501)
  ·
    refine ⟨10529635516852381762948313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28079028044939684701195501 10529635516852381762948313)
    ·
      refine ⟨7897226637639286322211235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10529635516852381762948313 7897226637639286322211235)
      ·
        refine ⟨11845839956458929483316853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7897226637639286322211235 11845839956458929483316853)
        ·
          refine ⟨1110547495918024639060955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11845839956458929483316853 1110547495918024639060955)
          ·
            refine ⟨1665821243877036958591433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110547495918024639060955 1665821243877036958591433)
            ·
              refine ⟨1249365932907777718943575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1665821243877036958591433 1249365932907777718943575)
              ·
                refine ⟨1874048899361666578415363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1249365932907777718943575 1874048899361666578415363)
                ·
                  refine ⟨2811073349042499867623045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1874048899361666578415363 2811073349042499867623045)
                  ·
                    refine ⟨527076252945468725179321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2811073349042499867623045 527076252945468725179321)
                    ·
                      rfl

theorem cell22_1539716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 1, 4].length) (baseStart_1539716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539716 prefixEnd_1539716 := by exact prefixLift 1539716
  have htrace : WordTrace (prefixWord ++ tailWord_1539716) baseStart_1539716 baseEnd_1539716 := by
    simpa [prefixWord, tailWord_1539716, baseEnd_1539716] using wordTrace_append hprefix tailTrace_1539716
  have hstable : (prefixWord ++ tailWord_1539716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539716).length < 2 ^ (prefixWord ++ tailWord_1539716).sum := by decide
  have hdescent : baseEnd_1539716 < baseStart_1539716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539746 : List Nat := [3, 3, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_1539746 : Nat := 118140960795 + 1539746 * 2 ^ 59
def prefixEnd_1539746 : Nat := 4983230072969 + 3 ^ 40 * 1539746 * 2
def baseEnd_1539746 : Nat := 527086522558558646929229

theorem tailTrace_1539746 : CollatzResearch.WordTrace tailWord_1539746 prefixEnd_1539746 527086522558558646929229 := by
  unfold tailWord_1539746
  simp only [CollatzResearch.WordTrace]
  refine ⟨14039787569942671131495773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37439433519847123017322061 14039787569942671131495773)
  ·
    refine ⟨5264920338728501674310915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14039787569942671131495773 5264920338728501674310915)
    ·
      refine ⟨7897380508092752511466373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5264920338728501674310915 7897380508092752511466373)
      ·
        refine ⟨1480758845267391095899945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7897380508092752511466373 1480758845267391095899945)
        ·
          refine ⟨1110569133950543321924959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1480758845267391095899945 1110569133950543321924959)
          ·
            refine ⟨1665853700925814982887439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1110569133950543321924959 1665853700925814982887439)
            ·
              refine ⟨2498780551388722474331159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1665853700925814982887439 2498780551388722474331159)
              ·
                refine ⟨3748170827083083711496739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2498780551388722474331159 3748170827083083711496739)
                ·
                  refine ⟨5622256240624625567245109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3748170827083083711496739 5622256240624625567245109)
                  ·
                    refine ⟨527086522558558646929229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5622256240624625567245109 527086522558558646929229)
                    ·
                      rfl

theorem cell22_1539746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_1539746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539746 prefixEnd_1539746 := by exact prefixLift 1539746
  have htrace : WordTrace (prefixWord ++ tailWord_1539746) baseStart_1539746 baseEnd_1539746 := by
    simpa [prefixWord, tailWord_1539746, baseEnd_1539746] using wordTrace_append hprefix tailTrace_1539746
  have hstable : (prefixWord ++ tailWord_1539746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539746).length < 2 ^ (prefixWord ++ tailWord_1539746).sum := by decide
  have hdescent : baseEnd_1539746 < baseStart_1539746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539757 : List Nat := [1, 5, 2, 1, 1, 1, 1, 4, 3, 3]
def baseStart_1539757 : Nat := 118140960795 + 1539757 * 2 ^ 59
def prefixEnd_1539757 : Nat := 4983230072969 + 3 ^ 40 * 1539757 * 2
def baseEnd_1539757 : Nat := 527090288083358284904195

theorem tailTrace_1539757 : CollatzResearch.WordTrace tailWord_1539757 prefixEnd_1539757 527090288083358284904195 := by
  unfold tailWord_1539757
  simp only [CollatzResearch.WordTrace]
  refine ⟨56159551482730833404633525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37439700988487222269755683 56159551482730833404633525)
  ·
    refine ⟨5264957951506015631684393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56159551482730833404633525 5264957951506015631684393)
    ·
      refine ⟨3948718463629511723763295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5264957951506015631684393 3948718463629511723763295)
      ·
        refine ⟨5923077695444267585644943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3948718463629511723763295 5923077695444267585644943)
        ·
          refine ⟨8884616543166401378467415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5923077695444267585644943 8884616543166401378467415)
          ·
            refine ⟨13326924814749602067701123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8884616543166401378467415 13326924814749602067701123)
            ·
              refine ⟨19990387222124403101551685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13326924814749602067701123 19990387222124403101551685)
              ·
                refine ⟨3748197604148325581540941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19990387222124403101551685 3748197604148325581540941)
                ·
                  refine ⟨1405574101555622093077853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3748197604148325581540941 1405574101555622093077853)
                  ·
                    refine ⟨527090288083358284904195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1405574101555622093077853 527090288083358284904195)
                    ·
                      rfl

theorem cell22_1539757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_1539757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539757 prefixEnd_1539757 := by exact prefixLift 1539757
  have htrace : WordTrace (prefixWord ++ tailWord_1539757) baseStart_1539757 baseEnd_1539757 := by
    simpa [prefixWord, tailWord_1539757, baseEnd_1539757] using wordTrace_append hprefix tailTrace_1539757
  have hstable : (prefixWord ++ tailWord_1539757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539757).length < 2 ^ (prefixWord ++ tailWord_1539757).sum := by decide
  have hdescent : baseEnd_1539757 < baseStart_1539757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539768 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 1, 7]
def baseStart_1539768 : Nat := 118140960795 + 1539768 * 2 ^ 59
def prefixEnd_1539768 : Nat := 4983230072969 + 3 ^ 40 * 1539768 * 2
def baseEnd_1539768 : Nat := 527094053608157922879161

theorem tailTrace_1539768 : CollatzResearch.WordTrace tailWord_1539768 prefixEnd_1539768 527094053608157922879161 := by
  unfold tailWord_1539768
  simp only [CollatzResearch.WordTrace]
  refine ⟨28079976342845491141641979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37439968457127321522189305 28079976342845491141641979)
  ·
    refine ⟨42119964514268236712462969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28079976342845491141641979 42119964514268236712462969)
    ·
      refine ⟨31589973385701177534347227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42119964514268236712462969 31589973385701177534347227)
      ·
        refine ⟨47384960078551766301520841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31589973385701177534347227 47384960078551766301520841)
        ·
          refine ⟨35538720058913824726140631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47384960078551766301520841 35538720058913824726140631)
          ·
            refine ⟨53308080088370737089210947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35538720058913824726140631 53308080088370737089210947)
            ·
              refine ⟨79962120132556105633816421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53308080088370737089210947 79962120132556105633816421)
              ·
                refine ⟨14992897524854269806340579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79962120132556105633816421 14992897524854269806340579)
                ·
                  refine ⟨22489346287281404709510869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14992897524854269806340579 22489346287281404709510869)
                  ·
                    refine ⟨527094053608157922879161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22489346287281404709510869 527094053608157922879161)
                    ·
                      rfl

theorem cell22_1539768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_1539768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539768 prefixEnd_1539768 := by exact prefixLift 1539768
  have htrace : WordTrace (prefixWord ++ tailWord_1539768) baseStart_1539768 baseEnd_1539768 := by
    simpa [prefixWord, tailWord_1539768, baseEnd_1539768] using wordTrace_append hprefix tailTrace_1539768
  have hstable : (prefixWord ++ tailWord_1539768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539768).length < 2 ^ (prefixWord ++ tailWord_1539768).sum := by decide
  have hdescent : baseEnd_1539768 < baseStart_1539768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539800 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 3, 4]
def baseStart_1539800 : Nat := 118140960795 + 1539800 * 2 ^ 59
def prefixEnd_1539800 : Nat := 4983230072969 + 3 ^ 40 * 1539800 * 2
def baseEnd_1539800 : Nat := 527105007862120506079063

theorem tailTrace_1539800 : CollatzResearch.WordTrace tailWord_1539800 prefixEnd_1539800 527105007862120506079063 := by
  unfold tailWord_1539800
  simp only [CollatzResearch.WordTrace]
  refine ⟨28080559910787525874224427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37440746547716701165632569 28080559910787525874224427)
  ·
    refine ⟨42120839866181288811336641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28080559910787525874224427 42120839866181288811336641)
    ·
      refine ⟨31590629899635966608502481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42120839866181288811336641 31590629899635966608502481)
      ·
        refine ⟨23692972424726974956376861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31590629899635966608502481 23692972424726974956376861)
        ·
          refine ⟨8884864659272615608641323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23692972424726974956376861 8884864659272615608641323)
          ·
            refine ⟨13327296988908923412961985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8884864659272615608641323 13327296988908923412961985)
            ·
              refine ⟨9995472741681692559721489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13327296988908923412961985 9995472741681692559721489)
              ·
                refine ⟨7496604556261269419791117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9995472741681692559721489 7496604556261269419791117)
                ·
                  refine ⟨2811226708597976032421669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7496604556261269419791117 2811226708597976032421669)
                  ·
                    refine ⟨527105007862120506079063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2811226708597976032421669 527105007862120506079063)
                    ·
                      rfl

theorem cell22_1539800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_1539800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539800 prefixEnd_1539800 := by exact prefixLift 1539800
  have htrace : WordTrace (prefixWord ++ tailWord_1539800) baseStart_1539800 baseEnd_1539800 := by
    simpa [prefixWord, tailWord_1539800, baseEnd_1539800] using wordTrace_append hprefix tailTrace_1539800
  have hstable : (prefixWord ++ tailWord_1539800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539800).length < 2 ^ (prefixWord ++ tailWord_1539800).sum := by decide
  have hdescent : baseEnd_1539800 < baseStart_1539800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539804 : List Nat := [2, 2, 5, 1, 2, 1, 1, 3, 5]
def baseStart_1539804 : Nat := 118140960795 + 1539804 * 2 ^ 59
def prefixEnd_1539804 : Nat := 4983230072969 + 3 ^ 40 * 1539804 * 2
def baseEnd_1539804 : Nat := 175702125714621942993017

theorem tailTrace_1539804 : CollatzResearch.WordTrace tailWord_1539804 prefixEnd_1539804 175702125714621942993017 := by
  unfold tailWord_1539804
  simp only [CollatzResearch.WordTrace]
  refine ⟨28080632856780280215797233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37440843809040373621062977 28080632856780280215797233)
  ·
    refine ⟨21060474642585210161847925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28080632856780280215797233 21060474642585210161847925)
    ·
      refine ⟨1974419497742363452673243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21060474642585210161847925 1974419497742363452673243)
      ·
        refine ⟨2961629246613545179009865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1974419497742363452673243 2961629246613545179009865)
        ·
          refine ⟨2221221934960158884257399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2961629246613545179009865 2221221934960158884257399)
          ·
            refine ⟨3331832902440238326386099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221221934960158884257399 3331832902440238326386099)
            ·
              refine ⟨4997749353660357489579149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3331832902440238326386099 4997749353660357489579149)
              ·
                refine ⟨1874156007622634058592181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4997749353660357489579149 1874156007622634058592181)
                ·
                  refine ⟨175702125714621942993017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1874156007622634058592181 175702125714621942993017)
                  ·
                    rfl

theorem cell22_1539804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 5].length) (baseStart_1539804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539804 prefixEnd_1539804 := by exact prefixLift 1539804
  have htrace : WordTrace (prefixWord ++ tailWord_1539804) baseStart_1539804 baseEnd_1539804 := by
    simpa [prefixWord, tailWord_1539804, baseEnd_1539804] using wordTrace_append hprefix tailTrace_1539804
  have hstable : (prefixWord ++ tailWord_1539804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539804).length < 2 ^ (prefixWord ++ tailWord_1539804).sum := by decide
  have hdescent : baseEnd_1539804 < baseStart_1539804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539853 : List Nat := [1, 7, 2, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1539853 : Nat := 118140960795 + 1539853 * 2 ^ 59
def prefixEnd_1539853 : Nat := 4983230072969 + 3 ^ 40 * 1539853 * 2
def baseEnd_1539853 : Nat := 527123150845246034503901

theorem tailTrace_1539853 : CollatzResearch.WordTrace tailWord_1539853 prefixEnd_1539853 527123150845246034503901 := by
  unfold tailWord_1539853
  simp only [CollatzResearch.WordTrace]
  refine ⟨56163052890383041800128213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37442035260255361200085475 56163052890383041800128213)
  ·
    refine ⟨1316321552118352542190505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 56163052890383041800128213 1316321552118352542190505)
    ·
      refine ⟨987241164088764406642879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1316321552118352542190505 987241164088764406642879)
      ·
        refine ⟨1480861746133146609964319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 987241164088764406642879 1480861746133146609964319)
        ·
          refine ⟨2221292619199719914946479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1480861746133146609964319 2221292619199719914946479)
          ·
            refine ⟨3331938928799579872419719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221292619199719914946479 3331938928799579872419719)
            ·
              refine ⟨4997908393199369808629579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3331938928799579872419719 4997908393199369808629579)
              ·
                refine ⟨7496862589799054712944369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4997908393199369808629579 7496862589799054712944369)
                ·
                  refine ⟨5622646942349291034708277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7496862589799054712944369 5622646942349291034708277)
                  ·
                    refine ⟨527123150845246034503901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5622646942349291034708277 527123150845246034503901)
                    ·
                      rfl

theorem cell22_1539853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1539853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539853 prefixEnd_1539853 := by exact prefixLift 1539853
  have htrace : WordTrace (prefixWord ++ tailWord_1539853) baseStart_1539853 baseEnd_1539853 := by
    simpa [prefixWord, tailWord_1539853, baseEnd_1539853] using wordTrace_append hprefix tailTrace_1539853
  have hstable : (prefixWord ++ tailWord_1539853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539853).length < 2 ^ (prefixWord ++ tailWord_1539853).sum := by decide
  have hdescent : baseEnd_1539853 < baseStart_1539853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539877 : List Nat := [1, 3, 1, 2, 3, 3, 3, 6]
def baseStart_1539877 : Nat := 118140960795 + 1539877 * 2 ^ 59
def prefixEnd_1539877 : Nat := 4983230072969 + 3 ^ 40 * 1539877 * 2
def baseEnd_1539877 : Nat := 58570151837301996878203

theorem tailTrace_1539877 : CollatzResearch.WordTrace tailWord_1539877 prefixEnd_1539877 58570151837301996878203 := by
  unfold tailWord_1539877
  simp only [CollatzResearch.WordTrace]
  refine ⟨56163928242296093899001885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37442618828197395932667923 56163928242296093899001885)
  ·
    refine ⟨21061473090861035212125707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56163928242296093899001885 21061473090861035212125707)
    ·
      refine ⟨31592209636291552818188561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21061473090861035212125707 31592209636291552818188561)
      ·
        refine ⟨23694157227218664613641421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31592209636291552818188561 23694157227218664613641421)
        ·
          refine ⟨8885308960206999230115533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23694157227218664613641421 8885308960206999230115533)
          ·
            refine ⟨3331990860077624711293325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8885308960206999230115533 3331990860077624711293325)
            ·
              refine ⟨1249496572529109266734997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3331990860077624711293325 1249496572529109266734997)
              ·
                refine ⟨58570151837301996878203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1249496572529109266734997 58570151837301996878203)
                ·
                  rfl

theorem cell22_1539877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 6].length) (baseStart_1539877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539877 prefixEnd_1539877 := by exact prefixLift 1539877
  have htrace : WordTrace (prefixWord ++ tailWord_1539877) baseStart_1539877 baseEnd_1539877 := by
    simpa [prefixWord, tailWord_1539877, baseEnd_1539877] using wordTrace_append hprefix tailTrace_1539877
  have hstable : (prefixWord ++ tailWord_1539877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539877).length < 2 ^ (prefixWord ++ tailWord_1539877).sum := by decide
  have hdescent : baseEnd_1539877 < baseStart_1539877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539909 : List Nat := [1, 3, 1, 1, 1, 2, 3, 6, 1, 3]
def baseStart_1539909 : Nat := 118140960795 + 1539909 * 2 ^ 59
def prefixEnd_1539909 : Nat := 4983230072969 + 3 ^ 40 * 1539909 * 2
def baseEnd_1539909 : Nat := 527142320789680555103729

theorem tailTrace_1539909 : CollatzResearch.WordTrace tailWord_1539909 prefixEnd_1539909 527142320789680555103729 := by
  unfold tailWord_1539909
  simp only [CollatzResearch.WordTrace]
  refine ⟨56165095378180163364166781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37443396918786775576111187 56165095378180163364166781)
  ·
    refine ⟨21061910766817561261562543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56165095378180163364166781 21061910766817561261562543)
    ·
      refine ⟨31592866150226341892343815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21061910766817561261562543 31592866150226341892343815)
      ·
        refine ⟨47389299225339512838515723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31592866150226341892343815 47389299225339512838515723)
        ·
          refine ⟨71083948838009269257773585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47389299225339512838515723 71083948838009269257773585)
          ·
            refine ⟨53312961628506951943330189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71083948838009269257773585 53312961628506951943330189)
            ·
              refine ⟨19992360610690106978748821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53312961628506951943330189 19992360610690106978748821)
              ·
                refine ⟨937141903626098764628851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19992360610690106978748821 937141903626098764628851)
                ·
                  refine ⟨1405712855439148146943277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 937141903626098764628851 1405712855439148146943277)
                  ·
                    refine ⟨527142320789680555103729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1405712855439148146943277 527142320789680555103729)
                    ·
                      rfl

theorem cell22_1539909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_1539909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539909 prefixEnd_1539909 := by exact prefixLift 1539909
  have htrace : WordTrace (prefixWord ++ tailWord_1539909) baseStart_1539909 baseEnd_1539909 := by
    simpa [prefixWord, tailWord_1539909, baseEnd_1539909] using wordTrace_append hprefix tailTrace_1539909
  have hstable : (prefixWord ++ tailWord_1539909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539909).length < 2 ^ (prefixWord ++ tailWord_1539909).sum := by decide
  have hdescent : baseEnd_1539909 < baseStart_1539909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539986 : List Nat := [3, 2, 3, 2, 1, 1, 3, 2, 1, 4]
def baseStart_1539986 : Nat := 118140960795 + 1539986 * 2 ^ 59
def prefixEnd_1539986 : Nat := 4983230072969 + 3 ^ 40 * 1539986 * 2
def baseEnd_1539986 : Nat := 527168679463278020928493

theorem tailTrace_1539986 : CollatzResearch.WordTrace tailWord_1539986 prefixEnd_1539986 527168679463278020928493 := by
  unfold tailWord_1539986
  simp only [CollatzResearch.WordTrace]
  refine ⟨14041975949725301378679953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37445269199267470343146541 14041975949725301378679953)
  ·
    refine ⟨10531481962293976034009965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14041975949725301378679953 10531481962293976034009965)
    ·
      refine ⟨3949305735860241012753737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10531481962293976034009965 3949305735860241012753737)
      ·
        refine ⟨2961979301895180759565303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3949305735860241012753737 2961979301895180759565303)
        ·
          refine ⟨4442968952842771139347955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2961979301895180759565303 4442968952842771139347955)
          ·
            refine ⟨6664453429264156709021933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4442968952842771139347955 6664453429264156709021933)
            ·
              refine ⟨2499170035974058765883225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6664453429264156709021933 2499170035974058765883225)
              ·
                refine ⟨1874377526980544074412419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2499170035974058765883225 1874377526980544074412419)
                ·
                  refine ⟨2811566290470816111618629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1874377526980544074412419 2811566290470816111618629)
                  ·
                    refine ⟨527168679463278020928493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2811566290470816111618629 527168679463278020928493)
                    ·
                      rfl

theorem cell22_1539986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_1539986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539986 prefixEnd_1539986 := by exact prefixLift 1539986
  have htrace : WordTrace (prefixWord ++ tailWord_1539986) baseStart_1539986 baseEnd_1539986 := by
    simpa [prefixWord, tailWord_1539986, baseEnd_1539986] using wordTrace_append hprefix tailTrace_1539986
  have hstable : (prefixWord ++ tailWord_1539986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539986).length < 2 ^ (prefixWord ++ tailWord_1539986).sum := by decide
  have hdescent : baseEnd_1539986 < baseStart_1539986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1539999 : List Nat := [1, 1, 2, 5, 3, 1, 1, 2, 1, 5]
def baseStart_1539999 : Nat := 118140960795 + 1539999 * 2 ^ 59
def prefixEnd_1539999 : Nat := 4983230072969 + 3 ^ 40 * 1539999 * 2
def baseEnd_1539999 : Nat := 527173129628950320353453

theorem tailTrace_1539999 : CollatzResearch.WordTrace tailWord_1539999 prefixEnd_1539999 527173129628950320353453 := by
  unfold tailWord_1539999
  simp only [CollatzResearch.WordTrace]
  refine ⟨56168377947854108734943051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37445585298569405823295367 56168377947854108734943051)
  ·
    refine ⟨84252566921781163102414577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56168377947854108734943051 84252566921781163102414577)
    ·
      refine ⟨63189425191335872326810933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84252566921781163102414577 63189425191335872326810933)
      ·
        refine ⟨5924008611687738030638525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63189425191335872326810933 5924008611687738030638525)
        ·
          refine ⟨2221503229382901761489447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5924008611687738030638525 2221503229382901761489447)
          ·
            refine ⟨3332254844074352642234171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2221503229382901761489447 3332254844074352642234171)
            ·
              refine ⟨4998382266111528963351257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3332254844074352642234171 4998382266111528963351257)
              ·
                refine ⟨3748786699583646722513443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4998382266111528963351257 3748786699583646722513443)
                ·
                  refine ⟨5623180049375470083770165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3748786699583646722513443 5623180049375470083770165)
                  ·
                    refine ⟨527173129628950320353453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5623180049375470083770165 527173129628950320353453)
                    ·
                      rfl

theorem cell22_1539999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 5].length) (baseStart_1539999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1539999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1539999 prefixEnd_1539999 := by exact prefixLift 1539999
  have htrace : WordTrace (prefixWord ++ tailWord_1539999) baseStart_1539999 baseEnd_1539999 := by
    simpa [prefixWord, tailWord_1539999, baseEnd_1539999] using wordTrace_append hprefix tailTrace_1539999
  have hstable : (prefixWord ++ tailWord_1539999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1539999).length < 2 ^ (prefixWord ++ tailWord_1539999).sum := by decide
  have hdescent : baseEnd_1539999 < baseStart_1539999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1539999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540029 : List Nat := [1, 4, 1, 2, 3, 3, 1, 7]
def baseStart_1540029 : Nat := 118140960795 + 1540029 * 2 ^ 59
def prefixEnd_1540029 : Nat := 4983230072969 + 3 ^ 40 * 1540029 * 2
def baseEnd_1540029 : Nat := 58575933249115582455929

theorem tailTrace_1540029 : CollatzResearch.WordTrace tailWord_1540029 prefixEnd_1540029 58575933249115582455929 := by
  unfold tailWord_1540029
  simp only [CollatzResearch.WordTrace]
  refine ⟨56169472137745423858535141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37446314758496949239023427 56169472137745423858535141)
  ·
    refine ⟨10531776025827266973475339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56169472137745423858535141 10531776025827266973475339)
    ·
      refine ⟨15797664038740900460213009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10531776025827266973475339 15797664038740900460213009)
      ·
        refine ⟨11848248029055675345159757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15797664038740900460213009 11848248029055675345159757)
        ·
          refine ⟨4443093010895878254434909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11848248029055675345159757 4443093010895878254434909)
          ·
            refine ⟨1666159879085954345413091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4443093010895878254434909 1666159879085954345413091)
            ·
              refine ⟨2499239818628931518119637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1666159879085954345413091 2499239818628931518119637)
              ·
                refine ⟨58575933249115582455929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2499239818628931518119637 58575933249115582455929)
                ·
                  rfl

theorem cell22_1540029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 7].length) (baseStart_1540029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540029 prefixEnd_1540029 := by exact prefixLift 1540029
  have htrace : WordTrace (prefixWord ++ tailWord_1540029) baseStart_1540029 baseEnd_1540029 := by
    simpa [prefixWord, tailWord_1540029, baseEnd_1540029] using wordTrace_append hprefix tailTrace_1540029
  have hstable : (prefixWord ++ tailWord_1540029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540029).length < 2 ^ (prefixWord ++ tailWord_1540029).sum := by decide
  have hdescent : baseEnd_1540029 < baseStart_1540029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540044 : List Nat := [2, 2, 1, 4, 1, 2, 1, 1, 5, 3]
def baseStart_1540044 : Nat := 118140960795 + 1540044 * 2 ^ 59
def prefixEnd_1540044 : Nat := 4983230072969 + 3 ^ 40 * 1540044 * 2
def baseEnd_1540044 : Nat := 527188534048585202978315

theorem tailTrace_1540044 : CollatzResearch.WordTrace tailWord_1540044 prefixEnd_1540044 527188534048585202978315 := by
  unfold tailWord_1540044
  simp only [CollatzResearch.WordTrace]
  refine ⟨28085009616345540710165593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37446679488460720946887457 28085009616345540710165593)
  ·
    refine ⟨21063757212259155532624195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28085009616345540710165593 21063757212259155532624195)
    ·
      refine ⟨31595635818388733298936293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21063757212259155532624195 31595635818388733298936293)
      ·
        refine ⟨5924181715947887493550555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31595635818388733298936293 5924181715947887493550555)
        ·
          refine ⟨8886272573921831240325833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5924181715947887493550555 8886272573921831240325833)
          ·
            refine ⟨6664704430441373430244375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8886272573921831240325833 6664704430441373430244375)
            ·
              refine ⟨9997056645662060145366563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6664704430441373430244375 9997056645662060145366563)
              ·
                refine ⟨14995584968493090218049845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9997056645662060145366563 14995584968493090218049845)
                ·
                  refine ⟨1405836090796227207942173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14995584968493090218049845 1405836090796227207942173)
                  ·
                    refine ⟨527188534048585202978315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1405836090796227207942173 527188534048585202978315)
                    ·
                      rfl

theorem cell22_1540044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_1540044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540044 prefixEnd_1540044 := by exact prefixLift 1540044
  have htrace : WordTrace (prefixWord ++ tailWord_1540044) baseStart_1540044 baseEnd_1540044 := by
    simpa [prefixWord, tailWord_1540044, baseEnd_1540044] using wordTrace_append hprefix tailTrace_1540044
  have hstable : (prefixWord ++ tailWord_1540044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540044).length < 2 ^ (prefixWord ++ tailWord_1540044).sum := by decide
  have hdescent : baseEnd_1540044 < baseStart_1540044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540078 : List Nat := [4, 1, 2, 1, 3, 1, 2, 4, 1, 3]
def baseStart_1540078 : Nat := 118140960795 + 1540078 * 2 ^ 59
def prefixEnd_1540078 : Nat := 4983230072969 + 3 ^ 40 * 1540078 * 2
def baseEnd_1540078 : Nat := 527200172943420447628211

theorem tailTrace_1540078 : CollatzResearch.WordTrace tailWord_1540078 prefixEnd_1540078 527200172943420447628211 := by
  unfold tailWord_1540078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7021407414320988153383611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37447506209711936818045925 7021407414320988153383611)
  ·
    refine ⟨10532111121481482230075417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7021407414320988153383611 10532111121481482230075417)
    ·
      refine ⟨7899083341111111672556563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10532111121481482230075417 7899083341111111672556563)
      ·
        refine ⟨11848625011666667508834845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7899083341111111672556563 11848625011666667508834845)
        ·
          refine ⟨4443234379375000315813067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11848625011666667508834845 4443234379375000315813067)
          ·
            refine ⟨6664851569062500473719601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4443234379375000315813067 6664851569062500473719601)
            ·
              refine ⟨4998638676796875355289701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6664851569062500473719601 4998638676796875355289701)
              ·
                refine ⟨937244751899414129116819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4998638676796875355289701 937244751899414129116819)
                ·
                  refine ⟨1405867127849121193675229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 937244751899414129116819 1405867127849121193675229)
                  ·
                    refine ⟨527200172943420447628211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1405867127849121193675229 527200172943420447628211)
                    ·
                      rfl

theorem cell22_1540078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_1540078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540078 prefixEnd_1540078 := by exact prefixLift 1540078
  have htrace : WordTrace (prefixWord ++ tailWord_1540078) baseStart_1540078 baseEnd_1540078 := by
    simpa [prefixWord, tailWord_1540078, baseEnd_1540078] using wordTrace_append hprefix tailTrace_1540078
  have hstable : (prefixWord ++ tailWord_1540078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540078).length < 2 ^ (prefixWord ++ tailWord_1540078).sum := by decide
  have hdescent : baseEnd_1540078 < baseStart_1540078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540147 : List Nat := [1, 1, 1, 2, 4, 1, 3, 9]
def baseStart_1540147 : Nat := 118140960795 + 1540147 * 2 ^ 59
def prefixEnd_1540147 : Nat := 4983230072969 + 3 ^ 40 * 1540147 * 2
def baseEnd_1540147 : Nat := 58580421450391918628111

theorem tailTrace_1540147 : CollatzResearch.WordTrace tailWord_1540147 prefixEnd_1540147 58580421450391918628111 := by
  unfold tailWord_1540147
  simp only [CollatzResearch.WordTrace]
  refine ⟨56173775951317930011330695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37449183967545286674220463 56173775951317930011330695)
  ·
    refine ⟨84260663926976895016996043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56173775951317930011330695 84260663926976895016996043)
    ·
      refine ⟨126390995890465342525494065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84260663926976895016996043 126390995890465342525494065)
      ·
        refine ⟨94793246917849006894120549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126390995890465342525494065 94793246917849006894120549)
        ·
          refine ⟨17773733797096688792647603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 94793246917849006894120549 17773733797096688792647603)
          ·
            refine ⟨26660600695645033188971405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17773733797096688792647603 26660600695645033188971405)
            ·
              refine ⟨9997725260866887445864277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26660600695645033188971405 9997725260866887445864277)
              ·
                refine ⟨58580421450391918628111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9997725260866887445864277 58580421450391918628111)
                ·
                  rfl

theorem cell22_1540147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 9].length) (baseStart_1540147 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540147 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540147 prefixEnd_1540147 := by exact prefixLift 1540147
  have htrace : WordTrace (prefixWord ++ tailWord_1540147) baseStart_1540147 baseEnd_1540147 := by
    simpa [prefixWord, tailWord_1540147, baseEnd_1540147] using wordTrace_append hprefix tailTrace_1540147
  have hstable : (prefixWord ++ tailWord_1540147).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540147).length < 2 ^ (prefixWord ++ tailWord_1540147).sum := by decide
  have hdescent : baseEnd_1540147 < baseStart_1540147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540209 : List Nat := [1, 2, 2, 2, 1, 1, 3, 5, 5]
def baseStart_1540209 : Nat := 118140960795 + 1540209 * 2 ^ 59
def prefixEnd_1540209 : Nat := 4983230072969 + 3 ^ 40 * 1540209 * 2
def baseEnd_1540209 : Nat := 175748338973526590867603

theorem tailTrace_1540209 : CollatzResearch.WordTrace tailWord_1540209 prefixEnd_1540209 175748338973526590867603 := by
  unfold tailWord_1540209
  simp only [CollatzResearch.WordTrace]
  refine ⟨56176037277093314600087681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37450691518062209733391787 56176037277093314600087681)
  ·
    refine ⟨42132027957819985950065761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56176037277093314600087681 42132027957819985950065761)
    ·
      refine ⟨31599020968364989462549321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42132027957819985950065761 31599020968364989462549321)
      ·
        refine ⟨23699265726273742096911991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31599020968364989462549321 23699265726273742096911991)
        ·
          refine ⟨35548898589410613145367987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23699265726273742096911991 35548898589410613145367987)
          ·
            refine ⟨53323347884115919718051981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35548898589410613145367987 53323347884115919718051981)
            ·
              refine ⟨19996255456543469894269493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 53323347884115919718051981 19996255456543469894269493)
              ·
                refine ⟨1874648949050950302587765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19996255456543469894269493 1874648949050950302587765)
                ·
                  refine ⟨175748338973526590867603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1874648949050950302587765 175748338973526590867603)
                  ·
                    rfl

theorem cell22_1540209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 5].length) (baseStart_1540209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540209 prefixEnd_1540209 := by exact prefixLift 1540209
  have htrace : WordTrace (prefixWord ++ tailWord_1540209) baseStart_1540209 baseEnd_1540209 := by
    simpa [prefixWord, tailWord_1540209, baseEnd_1540209] using wordTrace_append hprefix tailTrace_1540209
  have hstable : (prefixWord ++ tailWord_1540209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540209).length < 2 ^ (prefixWord ++ tailWord_1540209).sum := by decide
  have hdescent : baseEnd_1540209 < baseStart_1540209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540288 : List Nat := [2, 1, 1, 2, 5, 1, 3, 3, 4]
def baseStart_1540288 : Nat := 118140960795 + 1540288 * 2 ^ 59
def prefixEnd_1540288 : Nat := 4983230072969 + 3 ^ 40 * 1540288 * 2
def baseEnd_1540288 : Nat := 175757353411683299959189

theorem tailTrace_1540288 : CollatzResearch.WordTrace tailWord_1540288 prefixEnd_1540288 175757353411683299959189 := by
  unfold tailWord_1540288
  simp only [CollatzResearch.WordTrace]
  refine ⟨28089459321903555546106759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37452612429204740728142345 28089459321903555546106759)
  ·
    refine ⟨42134188982855333319160139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28089459321903555546106759 42134188982855333319160139)
    ·
      refine ⟨63201283474282999978740209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42134188982855333319160139 63201283474282999978740209)
      ·
        refine ⟨47400962605712249984055157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63201283474282999978740209 47400962605712249984055157)
        ·
          refine ⟨4443840244285523436005171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47400962605712249984055157 4443840244285523436005171)
          ·
            refine ⟨6665760366428285154007757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4443840244285523436005171 6665760366428285154007757)
            ·
              refine ⟨2499660137410606932752909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6665760366428285154007757 2499660137410606932752909)
              ·
                refine ⟨937372551528977599782341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2499660137410606932752909 937372551528977599782341)
                ·
                  refine ⟨175757353411683299959189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 937372551528977599782341 175757353411683299959189)
                  ·
                    rfl

theorem cell22_1540288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 3, 4].length) (baseStart_1540288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540288 prefixEnd_1540288 := by exact prefixLift 1540288
  have htrace : WordTrace (prefixWord ++ tailWord_1540288) baseStart_1540288 baseEnd_1540288 := by
    simpa [prefixWord, tailWord_1540288, baseEnd_1540288] using wordTrace_append hprefix tailTrace_1540288
  have hstable : (prefixWord ++ tailWord_1540288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540288).length < 2 ^ (prefixWord ++ tailWord_1540288).sum := by decide
  have hdescent : baseEnd_1540288 < baseStart_1540288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540329 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 2, 6]
def baseStart_1540329 : Nat := 118140960795 + 1540329 * 2 ^ 59
def prefixEnd_1540329 : Nat := 4983230072969 + 3 ^ 40 * 1540329 * 2
def baseEnd_1540329 : Nat := 527286095372939459602441

theorem tailTrace_1540329 : CollatzResearch.WordTrace tailWord_1540329 prefixEnd_1540329 527286095372939459602441 := by
  unfold tailWord_1540329
  simp only [CollatzResearch.WordTrace]
  refine ⟨56180414036658575094456041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37453609357772383396304027 56180414036658575094456041)
  ·
    refine ⟨42135310527493931320842031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56180414036658575094456041 42135310527493931320842031)
    ·
      refine ⟨63202965791240896981263047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42135310527493931320842031 63202965791240896981263047)
      ·
        refine ⟨94804448686861345471894571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63202965791240896981263047 94804448686861345471894571)
        ·
          refine ⟨142206673030292018207841857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94804448686861345471894571 142206673030292018207841857)
          ·
            refine ⟨106655004772719013655881393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142206673030292018207841857 106655004772719013655881393)
            ·
              refine ⟨79991253579539260241911045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 106655004772719013655881393 79991253579539260241911045)
              ·
                refine ⟨14998360046163611295358321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 79991253579539260241911045 14998360046163611295358321)
                ·
                  refine ⟨11248770034622708471518741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14998360046163611295358321 11248770034622708471518741)
                  ·
                    refine ⟨527286095372939459602441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11248770034622708471518741 527286095372939459602441)
                    ·
                      rfl

theorem cell22_1540329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_1540329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540329 prefixEnd_1540329 := by exact prefixLift 1540329
  have htrace : WordTrace (prefixWord ++ tailWord_1540329) baseStart_1540329 baseEnd_1540329 := by
    simpa [prefixWord, tailWord_1540329, baseEnd_1540329] using wordTrace_append hprefix tailTrace_1540329
  have hstable : (prefixWord ++ tailWord_1540329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540329).length < 2 ^ (prefixWord ++ tailWord_1540329).sum := by decide
  have hdescent : baseEnd_1540329 < baseStart_1540329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540331 : List Nat := [1, 1, 1, 1, 2, 5, 2, 1, 5, 3]
def baseStart_1540331 : Nat := 118140960795 + 1540331 * 2 ^ 59
def prefixEnd_1540331 : Nat := 4983230072969 + 3 ^ 40 * 1540331 * 2
def baseEnd_1540331 : Nat := 527286780013812121052435

theorem tailTrace_1540331 : CollatzResearch.WordTrace tailWord_1540331 prefixEnd_1540331 527286780013812121052435 := by
  unfold tailWord_1540331
  simp only [CollatzResearch.WordTrace]
  refine ⟨56180486982651329436028847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37453657988434219624019231 56180486982651329436028847)
  ·
    refine ⟨84270730473976994154043271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56180486982651329436028847 84270730473976994154043271)
    ·
      refine ⟨126406095710965491231064907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84270730473976994154043271 126406095710965491231064907)
      ·
        refine ⟨189609143566448236846597361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126406095710965491231064907 189609143566448236846597361)
        ·
          refine ⟨142206857674836177634948021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 189609143566448236846597361 142206857674836177634948021)
          ·
            refine ⟨13331892907015891653276377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 142206857674836177634948021 13331892907015891653276377)
            ·
              refine ⟨9998919680261918739957283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13331892907015891653276377 9998919680261918739957283)
              ·
                refine ⟨14998379520392878109935925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9998919680261918739957283 14998379520392878109935925)
                ·
                  refine ⟨1406098080036832322806493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14998379520392878109935925 1406098080036832322806493)
                  ·
                    refine ⟨527286780013812121052435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1406098080036832322806493 527286780013812121052435)
                    ·
                      rfl

theorem cell22_1540331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 1, 5, 3].length) (baseStart_1540331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540331 prefixEnd_1540331 := by exact prefixLift 1540331
  have htrace : WordTrace (prefixWord ++ tailWord_1540331) baseStart_1540331 baseEnd_1540331 := by
    simpa [prefixWord, tailWord_1540331, baseEnd_1540331] using wordTrace_append hprefix tailTrace_1540331
  have hstable : (prefixWord ++ tailWord_1540331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540331).length < 2 ^ (prefixWord ++ tailWord_1540331).sum := by decide
  have hdescent : baseEnd_1540331 < baseStart_1540331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540344 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 9]
def baseStart_1540344 : Nat := 118140960795 + 1540344 * 2 ^ 59
def prefixEnd_1540344 : Nat := 4983230072969 + 3 ^ 40 * 1540344 * 2
def baseEnd_1540344 : Nat := 175763743393161473492465

theorem tailTrace_1540344 : CollatzResearch.WordTrace tailWord_1540344 prefixEnd_1540344 175763743393161473492465 := by
  unfold tailWord_1540344
  simp only [CollatzResearch.WordTrace]
  refine ⟨28090480565802116328126043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37453974087736155104168057 28090480565802116328126043)
  ·
    refine ⟨42135720848703174492189065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28090480565802116328126043 42135720848703174492189065)
    ·
      refine ⟨31601790636527380869141799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42135720848703174492189065 31601790636527380869141799)
      ·
        refine ⟨47402685954791071303712699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31601790636527380869141799 47402685954791071303712699)
        ·
          refine ⟨71104028932186606955569049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47402685954791071303712699 71104028932186606955569049)
          ·
            refine ⟨53328021699139955216676787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71104028932186606955569049 53328021699139955216676787)
            ·
              refine ⟨79992032548709932825015181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53328021699139955216676787 79992032548709932825015181)
              ·
                refine ⟨29997012205766224809380693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 79992032548709932825015181 29997012205766224809380693)
                ·
                  refine ⟨175763743393161473492465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29997012205766224809380693 175763743393161473492465)
                  ·
                    rfl

theorem cell22_1540344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 9].length) (baseStart_1540344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540344 prefixEnd_1540344 := by exact prefixLift 1540344
  have htrace : WordTrace (prefixWord ++ tailWord_1540344) baseStart_1540344 baseEnd_1540344 := by
    simpa [prefixWord, tailWord_1540344, baseEnd_1540344] using wordTrace_append hprefix tailTrace_1540344
  have hstable : (prefixWord ++ tailWord_1540344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540344).length < 2 ^ (prefixWord ++ tailWord_1540344).sum := by decide
  have hdescent : baseEnd_1540344 < baseStart_1540344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540361 : List Nat := [1, 2, 1, 1, 3, 4, 1, 4, 5]
def baseStart_1540361 : Nat := 118140960795 + 1540361 * 2 ^ 59
def prefixEnd_1540361 : Nat := 4983230072969 + 3 ^ 40 * 1540361 * 2
def baseEnd_1540361 : Nat := 175765683208967347600781

theorem tailTrace_1540361 : CollatzResearch.WordTrace tailWord_1540361 prefixEnd_1540361 175765683208967347600781 := by
  unfold tailWord_1540361
  simp only [CollatzResearch.WordTrace]
  refine ⟨56181581172542644559620937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37454387448361763039747291 56181581172542644559620937)
  ·
    refine ⟨42136185879406983419715703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56181581172542644559620937 42136185879406983419715703)
    ·
      refine ⟨63204278819110475129573555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42136185879406983419715703 63204278819110475129573555)
      ·
        refine ⟨94806418228665712694360333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63204278819110475129573555 94806418228665712694360333)
        ·
          refine ⟨35552406835749642260385125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94806418228665712694360333 35552406835749642260385125)
          ·
            refine ⟨6666076281703057923822211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35552406835749642260385125 6666076281703057923822211)
            ·
              refine ⟨9999114422554586885733317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6666076281703057923822211 9999114422554586885733317)
              ·
                refine ⟨1874833954228985041074997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9999114422554586885733317 1874833954228985041074997)
                ·
                  refine ⟨175765683208967347600781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1874833954228985041074997 175765683208967347600781)
                  ·
                    rfl

theorem cell22_1540361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 5].length) (baseStart_1540361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540361 prefixEnd_1540361 := by exact prefixLift 1540361
  have htrace : WordTrace (prefixWord ++ tailWord_1540361) baseStart_1540361 baseEnd_1540361 := by
    simpa [prefixWord, tailWord_1540361, baseEnd_1540361] using wordTrace_append hprefix tailTrace_1540361
  have hstable : (prefixWord ++ tailWord_1540361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540361).length < 2 ^ (prefixWord ++ tailWord_1540361).sum := by decide
  have hdescent : baseEnd_1540361 < baseStart_1540361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540376 : List Nat := [2, 1, 2, 3, 1, 2, 3, 1, 2, 5]
def baseStart_1540376 : Nat := 118140960795 + 1540376 * 2 ^ 59
def prefixEnd_1540376 : Nat := 4983230072969 + 3 ^ 40 * 1540376 * 2
def baseEnd_1540376 : Nat := 527302184433447003677297

theorem tailTrace_1540376 : CollatzResearch.WordTrace tailWord_1540376 prefixEnd_1540376 527302184433447003677297 := by
  unfold tailWord_1540376
  simp only [CollatzResearch.WordTrace]
  refine ⟨28091064133744151060708491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37454752178325534747611321 28091064133744151060708491)
  ·
    refine ⟨42136596200616226591062737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28091064133744151060708491 42136596200616226591062737)
    ·
      refine ⟨31602447150462169943297053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42136596200616226591062737 31602447150462169943297053)
      ·
        refine ⟨11850917681423313728736395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31602447150462169943297053 11850917681423313728736395)
        ·
          refine ⟨17776376522134970593104593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11850917681423313728736395 17776376522134970593104593)
          ·
            refine ⟨13332282391601227944828445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17776376522134970593104593 13332282391601227944828445)
            ·
              refine ⟨4999605896850460479310667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13332282391601227944828445 4999605896850460479310667)
              ·
                refine ⟨7499408845275690718966001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4999605896850460479310667 7499408845275690718966001)
                ·
                  refine ⟨5624556633956768039224501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7499408845275690718966001 5624556633956768039224501)
                  ·
                    refine ⟨527302184433447003677297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5624556633956768039224501 527302184433447003677297)
                    ·
                      rfl

theorem cell22_1540376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_1540376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540376 prefixEnd_1540376 := by exact prefixLift 1540376
  have htrace : WordTrace (prefixWord ++ tailWord_1540376) baseStart_1540376 baseEnd_1540376 := by
    simpa [prefixWord, tailWord_1540376, baseEnd_1540376] using wordTrace_append hprefix tailTrace_1540376
  have hstable : (prefixWord ++ tailWord_1540376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540376).length < 2 ^ (prefixWord ++ tailWord_1540376).sum := by decide
  have hdescent : baseEnd_1540376 < baseStart_1540376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540382 : List Nat := [4, 3, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1540382 : Nat := 118140960795 + 1540382 * 2 ^ 59
def prefixEnd_1540382 : Nat := 4983230072969 + 3 ^ 40 * 1540382 * 2
def baseEnd_1540382 : Nat := 527304238356064988027279

theorem tailTrace_1540382 : CollatzResearch.WordTrace tailWord_1540382 prefixEnd_1540382 527304238356064988027279 := by
  unfold tailWord_1540382
  simp only [CollatzResearch.WordTrace]
  refine ⟨7022793388183320643266925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37454898070311043430756933 7022793388183320643266925)
  ·
    refine ⟨2633547520568745241225097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7022793388183320643266925 2633547520568745241225097)
    ·
      refine ⟨1975160640426558930918823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2633547520568745241225097 1975160640426558930918823)
      ·
        refine ⟨2962740960639838396378235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1975160640426558930918823 2962740960639838396378235)
        ·
          refine ⟨4444111440959757594567353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2962740960639838396378235 4444111440959757594567353)
          ·
            refine ⟨3333083580719818195925515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4444111440959757594567353 3333083580719818195925515)
            ·
              refine ⟨4999625371079727293888273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3333083580719818195925515 4999625371079727293888273)
              ·
                refine ⟨3749719028309795470416205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4999625371079727293888273 3749719028309795470416205)
                ·
                  refine ⟨1406144635616173301406077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3749719028309795470416205 1406144635616173301406077)
                  ·
                    refine ⟨527304238356064988027279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1406144635616173301406077 527304238356064988027279)
                    ·
                      rfl

theorem cell22_1540382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1540382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540382 prefixEnd_1540382 := by exact prefixLift 1540382
  have htrace : WordTrace (prefixWord ++ tailWord_1540382) baseStart_1540382 baseEnd_1540382 := by
    simpa [prefixWord, tailWord_1540382, baseEnd_1540382] using wordTrace_append hprefix tailTrace_1540382
  have hstable : (prefixWord ++ tailWord_1540382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540382).length < 2 ^ (prefixWord ++ tailWord_1540382).sum := by decide
  have hdescent : baseEnd_1540382 < baseStart_1540382 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540423 : List Nat := [1, 1, 4, 1, 2, 2, 1, 6, 4]
def baseStart_1540423 : Nat := 118140960795 + 1540423 * 2 ^ 59
def prefixEnd_1540423 : Nat := 4983230072969 + 3 ^ 40 * 1540423 * 2
def baseEnd_1540423 : Nat := 175772757831318182584051

theorem tailTrace_1540423 : CollatzResearch.WordTrace tailWord_1540423 prefixEnd_1540423 175772757831318182584051 := by
  unfold tailWord_1540423
  simp only [CollatzResearch.WordTrace]
  refine ⟨56183842498318029148377923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37455894998878686098918615 56183842498318029148377923)
  ·
    refine ⟨84275763747477043722566885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56183842498318029148377923 84275763747477043722566885)
    ·
      refine ⟨15801705702651945697981291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 84275763747477043722566885 15801705702651945697981291)
      ·
        refine ⟨23702558553977918546971937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15801705702651945697981291 23702558553977918546971937)
        ·
          refine ⟨17776918915483438910228953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23702558553977918546971937 17776918915483438910228953)
          ·
            refine ⟨13332689186612579182671715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17776918915483438910228953 13332689186612579182671715)
            ·
              refine ⟨19999033779918868774007573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13332689186612579182671715 19999033779918868774007573)
              ·
                refine ⟨937454708433696973781605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19999033779918868774007573 937454708433696973781605)
                ·
                  refine ⟨175772757831318182584051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 937454708433696973781605 175772757831318182584051)
                  ·
                    rfl

theorem cell22_1540423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 6, 4].length) (baseStart_1540423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540423 prefixEnd_1540423 := by exact prefixLift 1540423
  have htrace : WordTrace (prefixWord ++ tailWord_1540423) baseStart_1540423 baseEnd_1540423 := by
    simpa [prefixWord, tailWord_1540423, baseEnd_1540423] using wordTrace_append hprefix tailTrace_1540423
  have hstable : (prefixWord ++ tailWord_1540423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540423).length < 2 ^ (prefixWord ++ tailWord_1540423).sum := by decide
  have hdescent : baseEnd_1540423 < baseStart_1540423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540451 : List Nat := [1, 1, 1, 5, 2, 1, 3, 8]
def baseStart_1540451 : Nat := 118140960795 + 1540451 * 2 ^ 59
def prefixEnd_1540451 : Nat := 4983230072969 + 3 ^ 40 * 1540451 * 2
def baseEnd_1540451 : Nat := 58591984274019089783563

theorem tailTrace_1540451 : CollatzResearch.WordTrace tailWord_1540451 prefixEnd_1540451 58591984274019089783563 := by
  unfold tailWord_1540451
  simp only [CollatzResearch.WordTrace]
  refine ⟨56184863742216589930397207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37456575828144393286931471 56184863742216589930397207)
  ·
    refine ⟨84277295613324884895595811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56184863742216589930397207 84277295613324884895595811)
    ·
      refine ⟨126415943419987327343393717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84277295613324884895595811 126415943419987327343393717)
      ·
        refine ⟨11851494695623811938443161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126415943419987327343393717 11851494695623811938443161)
        ·
          refine ⟨8888621021717858953832371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11851494695623811938443161 8888621021717858953832371)
          ·
            refine ⟨13332931532576788430748557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8888621021717858953832371 13332931532576788430748557)
            ·
              refine ⟨4999849324716295661530709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13332931532576788430748557 4999849324716295661530709)
              ·
                refine ⟨58591984274019089783563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4999849324716295661530709 58591984274019089783563)
                ·
                  rfl

theorem cell22_1540451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 8].length) (baseStart_1540451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540451 prefixEnd_1540451 := by exact prefixLift 1540451
  have htrace : WordTrace (prefixWord ++ tailWord_1540451) baseStart_1540451 baseEnd_1540451 := by
    simpa [prefixWord, tailWord_1540451, baseEnd_1540451] using wordTrace_append hprefix tailTrace_1540451
  have hstable : (prefixWord ++ tailWord_1540451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540451).length < 2 ^ (prefixWord ++ tailWord_1540451).sum := by decide
  have hdescent : baseEnd_1540451 < baseStart_1540451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540575 : List Nat := [1, 1, 2, 3, 3, 2, 1, 5, 4]
def baseStart_1540575 : Nat := 118140960795 + 1540575 * 2 ^ 59
def prefixEnd_1540575 : Nat := 4983230072969 + 3 ^ 40 * 1540575 * 2
def baseEnd_1540575 : Nat := 175790102066758939317229

theorem tailTrace_1540575 : CollatzResearch.WordTrace tailWord_1540575 prefixEnd_1540575 175790102066758939317229 := by
  unfold tailWord_1540575
  simp only [CollatzResearch.WordTrace]
  refine ⟨56189386393767359107911179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37459590929178239405274119 56189386393767359107911179)
  ·
    refine ⟨84284079590651038661866769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56189386393767359107911179 84284079590651038661866769)
    ·
      refine ⟨63213059692988278996400077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84284079590651038661866769 63213059692988278996400077)
      ·
        refine ⟨23704897384870604623650029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63213059692988278996400077 23704897384870604623650029)
        ·
          refine ⟨8889336519326476733868761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23704897384870604623650029 8889336519326476733868761)
          ·
            refine ⟨6667002389494857550401571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8889336519326476733868761 6667002389494857550401571)
            ·
              refine ⟨10000503584242286325602357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6667002389494857550401571 10000503584242286325602357)
              ·
                refine ⟨937547211022714343025221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10000503584242286325602357 937547211022714343025221)
                ·
                  refine ⟨175790102066758939317229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 937547211022714343025221 175790102066758939317229)
                  ·
                    rfl

theorem cell22_1540575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 4].length) (baseStart_1540575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540575 prefixEnd_1540575 := by exact prefixLift 1540575
  have htrace : WordTrace (prefixWord ++ tailWord_1540575) baseStart_1540575 baseEnd_1540575 := by
    simpa [prefixWord, tailWord_1540575, baseEnd_1540575] using wordTrace_append hprefix tailTrace_1540575
  have hstable : (prefixWord ++ tailWord_1540575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540575).length < 2 ^ (prefixWord ++ tailWord_1540575).sum := by decide
  have hdescent : baseEnd_1540575 < baseStart_1540575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540588 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 4, 4]
def baseStart_1540588 : Nat := 118140960795 + 1540588 * 2 ^ 59
def prefixEnd_1540588 : Nat := 4983230072969 + 3 ^ 40 * 1540588 * 2
def baseEnd_1540588 : Nat := 527374756365949117376647

theorem tailTrace_1540588 : CollatzResearch.WordTrace tailWord_1540588 prefixEnd_1540588 527374756365949117376647 := by
  unfold tailWord_1540588
  simp only [CollatzResearch.WordTrace]
  refine ⟨28094930271360131164067209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37459907028480174885422945 28094930271360131164067209)
  ·
    refine ⟨21071197703520098373050407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28094930271360131164067209 21071197703520098373050407)
    ·
      refine ⟨31606796555280147559575611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21071197703520098373050407 31606796555280147559575611)
      ·
        refine ⟨47410194832920221339363417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31606796555280147559575611 47410194832920221339363417)
        ·
          refine ⟨35557646124690166004522563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47410194832920221339363417 35557646124690166004522563)
          ·
            refine ⟨53336469187035249006783845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35557646124690166004522563 53336469187035249006783845)
            ·
              refine ⟨10000587972569109188771971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53336469187035249006783845 10000587972569109188771971)
              ·
                refine ⟨15000881958853663783157957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10000587972569109188771971 15000881958853663783157957)
                ·
                  refine ⟨2812665367285061959342117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15000881958853663783157957 2812665367285061959342117)
                  ·
                    refine ⟨527374756365949117376647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2812665367285061959342117 527374756365949117376647)
                    ·
                      rfl

theorem cell22_1540588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_1540588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540588 prefixEnd_1540588 := by exact prefixLift 1540588
  have htrace : WordTrace (prefixWord ++ tailWord_1540588) baseStart_1540588 baseEnd_1540588 := by
    simpa [prefixWord, tailWord_1540588, baseEnd_1540588] using wordTrace_append hprefix tailTrace_1540588
  have hstable : (prefixWord ++ tailWord_1540588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540588).length < 2 ^ (prefixWord ++ tailWord_1540588).sum := by decide
  have hdescent : baseEnd_1540588 < baseStart_1540588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540607 : List Nat := [1, 1, 2, 2, 1, 2, 7, 1, 2, 3]
def baseStart_1540607 : Nat := 118140960795 + 1540607 * 2 ^ 59
def prefixEnd_1540607 : Nat := 4983230072969 + 3 ^ 40 * 1540607 * 2
def baseEnd_1540607 : Nat := 527381260454239401151589

theorem tailTrace_1540607 : CollatzResearch.WordTrace tailWord_1540607 prefixEnd_1540607 527381260454239401151589 := by
  unfold tailWord_1540607
  simp only [CollatzResearch.WordTrace]
  refine ⟨56190553529651428573076075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37460369019767619048717383 56190553529651428573076075)
  ·
    refine ⟨84285830294477142859614113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56190553529651428573076075 84285830294477142859614113)
    ·
      refine ⟨63214372720857857144710585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84285830294477142859614113 63214372720857857144710585)
      ·
        refine ⟨47410779540643392858532939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63214372720857857144710585 47410779540643392858532939)
        ·
          refine ⟨71116169310965089287799409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47410779540643392858532939 71116169310965089287799409)
          ·
            refine ⟨53337126983223816965849557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71116169310965089287799409 53337126983223816965849557)
            ·
              refine ⟨1250088913669308210137099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 53337126983223816965849557 1250088913669308210137099)
              ·
                refine ⟨1875133370503962315205649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1250088913669308210137099 1875133370503962315205649)
                ·
                  refine ⟨1406350027877971736404237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1875133370503962315205649 1406350027877971736404237)
                  ·
                    refine ⟨527381260454239401151589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1406350027877971736404237 527381260454239401151589)
                    ·
                      rfl

theorem cell22_1540607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 7, 1, 2, 3].length) (baseStart_1540607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540607 prefixEnd_1540607 := by exact prefixLift 1540607
  have htrace : WordTrace (prefixWord ++ tailWord_1540607) baseStart_1540607 baseEnd_1540607 := by
    simpa [prefixWord, tailWord_1540607, baseEnd_1540607] using wordTrace_append hprefix tailTrace_1540607
  have hstable : (prefixWord ++ tailWord_1540607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540607).length < 2 ^ (prefixWord ++ tailWord_1540607).sum := by decide
  have hdescent : baseEnd_1540607 < baseStart_1540607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540618 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 2, 7]
def baseStart_1540618 : Nat := 118140960795 + 1540618 * 2 ^ 59
def prefixEnd_1540618 : Nat := 4983230072969 + 3 ^ 40 * 1540618 * 2
def baseEnd_1540618 : Nat := 527385025979039039126555

theorem tailTrace_1540618 : CollatzResearch.WordTrace tailWord_1540618 prefixEnd_1540618 527385025979039039126555 := by
  unfold tailWord_1540618
  simp only [CollatzResearch.WordTrace]
  refine ⟨14047738683152894362931627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37460636488407718301151005 14047738683152894362931627)
  ·
    refine ⟨21071608024729341544397441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14047738683152894362931627 21071608024729341544397441)
    ·
      refine ⟨15803706018547006158298081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21071608024729341544397441 15803706018547006158298081)
      ·
        refine ⟨11852779513910254618723561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15803706018547006158298081 11852779513910254618723561)
        ·
          refine ⟨8889584635432690964042671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11852779513910254618723561 8889584635432690964042671)
          ·
            refine ⟨13334376953149036446064007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8889584635432690964042671 13334376953149036446064007)
            ·
              refine ⟨20001565429723554669096011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13334376953149036446064007 20001565429723554669096011)
              ·
                refine ⟨30002348144585332003644017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20001565429723554669096011 30002348144585332003644017)
                ·
                  refine ⟨22501761108438999002733013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30002348144585332003644017 22501761108438999002733013)
                  ·
                    refine ⟨527385025979039039126555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22501761108438999002733013 527385025979039039126555)
                    ·
                      rfl

theorem cell22_1540618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_1540618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540618 prefixEnd_1540618 := by exact prefixLift 1540618
  have htrace : WordTrace (prefixWord ++ tailWord_1540618) baseStart_1540618 baseEnd_1540618 := by
    simpa [prefixWord, tailWord_1540618, baseEnd_1540618] using wordTrace_append hprefix tailTrace_1540618
  have hstable : (prefixWord ++ tailWord_1540618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540618).length < 2 ^ (prefixWord ++ tailWord_1540618).sum := by decide
  have hdescent : baseEnd_1540618 < baseStart_1540618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540620 : List Nat := [2, 2, 1, 2, 4, 1, 4, 6]
def baseStart_1540620 : Nat := 118140960795 + 1540620 * 2 ^ 59
def prefixEnd_1540620 : Nat := 4983230072969 + 3 ^ 40 * 1540620 * 2
def baseEnd_1540620 : Nat := 58598412291101300064061

theorem tailTrace_1540620 : CollatzResearch.WordTrace tailWord_1540620 prefixEnd_1540620 58598412291101300064061 := by
  unfold tailWord_1540620
  simp only [CollatzResearch.WordTrace]
  refine ⟨28095513839302165896649657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37460685119069554528866209 28095513839302165896649657)
  ·
    refine ⟨21071635379476624422487243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28095513839302165896649657 21071635379476624422487243)
    ·
      refine ⟨31607453069214936633730865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21071635379476624422487243 31607453069214936633730865)
      ·
        refine ⟨23705589801911202475298149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31607453069214936633730865 23705589801911202475298149)
        ·
          refine ⟨4444798087858350464118403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23705589801911202475298149 4444798087858350464118403)
          ·
            refine ⟨6667197131787525696177605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4444798087858350464118403 6667197131787525696177605)
            ·
              refine ⟨1250099462210161068033301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6667197131787525696177605 1250099462210161068033301)
              ·
                refine ⟨58598412291101300064061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1250099462210161068033301 58598412291101300064061)
                ·
                  rfl

theorem cell22_1540620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 6].length) (baseStart_1540620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540620 prefixEnd_1540620 := by exact prefixLift 1540620
  have htrace : WordTrace (prefixWord ++ tailWord_1540620) baseStart_1540620 baseEnd_1540620 := by
    simpa [prefixWord, tailWord_1540620, baseEnd_1540620] using wordTrace_append hprefix tailTrace_1540620
  have hstable : (prefixWord ++ tailWord_1540620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540620).length < 2 ^ (prefixWord ++ tailWord_1540620).sum := by decide
  have hdescent : baseEnd_1540620 < baseStart_1540620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540652 : List Nat := [2, 2, 1, 1, 1, 2, 1, 8, 1, 3]
def baseStart_1540652 : Nat := 118140960795 + 1540652 * 2 ^ 59
def prefixEnd_1540652 : Nat := 4983230072969 + 3 ^ 40 * 1540652 * 2
def baseEnd_1540652 : Nat := 527396664873874283776451

theorem tailTrace_1540652 : CollatzResearch.WordTrace tailWord_1540652 prefixEnd_1540652 527396664873874283776451 := by
  unfold tailWord_1540652
  simp only [CollatzResearch.WordTrace]
  refine ⟨28096097407244200629232105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37461463209658934172309473 28096097407244200629232105)
  ·
    refine ⟨21072073055433150471924079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28096097407244200629232105 21072073055433150471924079)
    ·
      refine ⟨31608109583149725707886119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21072073055433150471924079 31608109583149725707886119)
      ·
        refine ⟨47412164374724588561829179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31608109583149725707886119 47412164374724588561829179)
        ·
          refine ⟨71118246562086882842743769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47412164374724588561829179 71118246562086882842743769)
          ·
            refine ⟨53338684921565162132057827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71118246562086882842743769 53338684921565162132057827)
            ·
              refine ⟨80008027382347743198086741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53338684921565162132057827 80008027382347743198086741)
              ·
                refine ⟨937594070886887615602579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 80008027382347743198086741 937594070886887615602579)
                ·
                  refine ⟨1406391106330331423403869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 937594070886887615602579 1406391106330331423403869)
                  ·
                    refine ⟨527396664873874283776451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1406391106330331423403869 527396664873874283776451)
                    ·
                      rfl

theorem cell22_1540652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 8, 1, 3].length) (baseStart_1540652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540652 prefixEnd_1540652 := by exact prefixLift 1540652
  have htrace : WordTrace (prefixWord ++ tailWord_1540652) baseStart_1540652 baseEnd_1540652 := by
    simpa [prefixWord, tailWord_1540652, baseEnd_1540652] using wordTrace_append hprefix tailTrace_1540652
  have hstable : (prefixWord ++ tailWord_1540652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540652).length < 2 ^ (prefixWord ++ tailWord_1540652).sum := by decide
  have hdescent : baseEnd_1540652 < baseStart_1540652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540663 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 1, 7]
def baseStart_1540663 : Nat := 118140960795 + 1540663 * 2 ^ 59
def prefixEnd_1540663 : Nat := 4983230072969 + 3 ^ 40 * 1540663 * 2
def baseEnd_1540663 : Nat := 527400430398673921751417

theorem tailTrace_1540663 : CollatzResearch.WordTrace tailWord_1540663 prefixEnd_1540663 527400430398673921751417 := by
  unfold tailWord_1540663
  simp only [CollatzResearch.WordTrace]
  refine ⟨56192596017448550137114643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37461730678299033424743095 56192596017448550137114643)
  ·
    refine ⟨84288894026172825205671965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56192596017448550137114643 84288894026172825205671965)
    ·
      refine ⟨31608335259814809452126987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84288894026172825205671965 31608335259814809452126987)
      ·
        refine ⟨47412502889722214178190481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31608335259814809452126987 47412502889722214178190481)
        ·
          refine ⟨35559377167291660633642861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47412502889722214178190481 35559377167291660633642861)
          ·
            refine ⟨13334766437734372737616073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35559377167291660633642861 13334766437734372737616073)
            ·
              refine ⟨10001074828300779553212055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13334766437734372737616073 10001074828300779553212055)
              ·
                refine ⟨15001612242451169329818083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10001074828300779553212055 15001612242451169329818083)
                ·
                  refine ⟨22502418363676753994727125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15001612242451169329818083 22502418363676753994727125)
                  ·
                    refine ⟨527400430398673921751417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22502418363676753994727125 527400430398673921751417)
                    ·
                      rfl

theorem cell22_1540663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_1540663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540663 prefixEnd_1540663 := by exact prefixLift 1540663
  have htrace : WordTrace (prefixWord ++ tailWord_1540663) baseStart_1540663 baseEnd_1540663 := by
    simpa [prefixWord, tailWord_1540663, baseEnd_1540663] using wordTrace_append hprefix tailTrace_1540663
  have hstable : (prefixWord ++ tailWord_1540663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540663).length < 2 ^ (prefixWord ++ tailWord_1540663).sum := by decide
  have hdescent : baseEnd_1540663 < baseStart_1540663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540665 : List Nat := [1, 2, 1, 5, 1, 1, 3, 3, 5]
def baseStart_1540665 : Nat := 118140960795 + 1540665 * 2 ^ 59
def prefixEnd_1540665 : Nat := 4983230072969 + 3 ^ 40 * 1540665 * 2
def baseEnd_1540665 : Nat := 175800371679848861067137

theorem tailTrace_1540665 : CollatzResearch.WordTrace tailWord_1540665 prefixEnd_1540665 175800371679848861067137 := by
  unfold tailWord_1540665
  simp only [CollatzResearch.WordTrace]
  refine ⟨56192668963441304478687449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37461779308960869652458299 56192668963441304478687449)
  ·
    refine ⟨42144501722580978359015587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56192668963441304478687449 42144501722580978359015587)
    ·
      refine ⟨63216752583871467538523381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42144501722580978359015587 63216752583871467538523381)
      ·
        refine ⟨5926570554737950081736567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63216752583871467538523381 5926570554737950081736567)
        ·
          refine ⟨8889855832106925122604851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5926570554737950081736567 8889855832106925122604851)
          ·
            refine ⟨13334783748160387683907277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8889855832106925122604851 13334783748160387683907277)
            ·
              refine ⟨5000543905560145381465229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13334783748160387683907277 5000543905560145381465229)
              ·
                refine ⟨1875203964585054518049461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5000543905560145381465229 1875203964585054518049461)
                ·
                  refine ⟨175800371679848861067137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1875203964585054518049461 175800371679848861067137)
                  ·
                    rfl

theorem cell22_1540665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 5].length) (baseStart_1540665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540665 prefixEnd_1540665 := by exact prefixLift 1540665
  have htrace : WordTrace (prefixWord ++ tailWord_1540665) baseStart_1540665 baseEnd_1540665 := by
    simpa [prefixWord, tailWord_1540665, baseEnd_1540665] using wordTrace_append hprefix tailTrace_1540665
  have hstable : (prefixWord ++ tailWord_1540665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540665).length < 2 ^ (prefixWord ++ tailWord_1540665).sum := by decide
  have hdescent : baseEnd_1540665 < baseStart_1540665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540746 : List Nat := [3, 1, 2, 3, 3, 2, 2, 1, 1, 4]
def baseStart_1540746 : Nat := 118140960795 + 1540746 * 2 ^ 59
def prefixEnd_1540746 : Nat := 4983230072969 + 3 ^ 40 * 1540746 * 2
def baseEnd_1540746 : Nat := 527428842994889371926163

theorem tailTrace_1540746 : CollatzResearch.WordTrace tailWord_1540746 prefixEnd_1540746 527428842994889371926163 := by
  unfold tailWord_1540746
  simp only [CollatzResearch.WordTrace]
  refine ⟨14048905819036963828096523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37463748850765236874924061 14048905819036963828096523)
  ·
    refine ⟨21073358728555445742144785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14048905819036963828096523 21073358728555445742144785)
    ·
      refine ⟨15805019046416584306608589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21073358728555445742144785 15805019046416584306608589)
      ·
        refine ⟨5926882142406219114978221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15805019046416584306608589 5926882142406219114978221)
        ·
          refine ⟨2222580803402332168116833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5926882142406219114978221 2222580803402332168116833)
          ·
            refine ⟨1666935602551749126087625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2222580803402332168116833 1666935602551749126087625)
            ·
              refine ⟨1250201701913811844565719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1666935602551749126087625 1250201701913811844565719)
              ·
                refine ⟨1875302552870717766848579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1250201701913811844565719 1875302552870717766848579)
                ·
                  refine ⟨2812953829306076650272869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875302552870717766848579 2812953829306076650272869)
                  ·
                    refine ⟨527428842994889371926163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2812953829306076650272869 527428842994889371926163)
                    ·
                      rfl

theorem cell22_1540746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_1540746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540746 prefixEnd_1540746 := by exact prefixLift 1540746
  have htrace : WordTrace (prefixWord ++ tailWord_1540746) baseStart_1540746 baseEnd_1540746 := by
    simpa [prefixWord, tailWord_1540746, baseEnd_1540746] using wordTrace_append hprefix tailTrace_1540746
  have hstable : (prefixWord ++ tailWord_1540746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540746).length < 2 ^ (prefixWord ++ tailWord_1540746).sum := by decide
  have hdescent : baseEnd_1540746 < baseStart_1540746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540787 : List Nat := [1, 1, 1, 2, 3, 4, 2, 2, 3, 3]
def baseStart_1540787 : Nat := 118140960795 + 1540787 * 2 ^ 59
def prefixEnd_1540787 : Nat := 4983230072969 + 3 ^ 40 * 1540787 * 2
def baseEnd_1540787 : Nat := 527442878132778931651037

theorem tailTrace_1540787 : CollatzResearch.WordTrace tailWord_1540787 prefixEnd_1540787 527442878132778931651037 := by
  unfold tailWord_1540787
  simp only [CollatzResearch.WordTrace]
  refine ⟨56197118668999319314628615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37464745779332879543085743 56197118668999319314628615)
  ·
    refine ⟨84295678003498978971942923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56197118668999319314628615 84295678003498978971942923)
    ·
      refine ⟨126443517005248468457914385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84295678003498978971942923 126443517005248468457914385)
      ·
        refine ⟨94832637753936351343435789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126443517005248468457914385 94832637753936351343435789)
        ·
          refine ⟨35562239157726131753788421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94832637753936351343435789 35562239157726131753788421)
          ·
            refine ⟨6667919842073649703835329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 35562239157726131753788421 6667919842073649703835329)
            ·
              refine ⟨5000939881555237277876497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6667919842073649703835329 5000939881555237277876497)
              ·
                refine ⟨3750704911166427958407373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5000939881555237277876497 3750704911166427958407373)
                ·
                  refine ⟨1406514341687410484402765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3750704911166427958407373 1406514341687410484402765)
                  ·
                    refine ⟨527442878132778931651037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1406514341687410484402765 527442878132778931651037)
                    ·
                      rfl

theorem cell22_1540787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 2, 3, 3].length) (baseStart_1540787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540787 prefixEnd_1540787 := by exact prefixLift 1540787
  have htrace : WordTrace (prefixWord ++ tailWord_1540787) baseStart_1540787 baseEnd_1540787 := by
    simpa [prefixWord, tailWord_1540787, baseEnd_1540787] using wordTrace_append hprefix tailTrace_1540787
  have hstable : (prefixWord ++ tailWord_1540787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540787).length < 2 ^ (prefixWord ++ tailWord_1540787).sum := by decide
  have hdescent : baseEnd_1540787 < baseStart_1540787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540789 : List Nat := [1, 3, 3, 3, 1, 3, 2, 6]
def baseStart_1540789 : Nat := 118140960795 + 1540789 * 2 ^ 59
def prefixEnd_1540789 : Nat := 4983230072969 + 3 ^ 40 * 1540789 * 2
def baseEnd_1540789 : Nat := 58604840308183510344559

theorem tailTrace_1540789 : CollatzResearch.WordTrace tailWord_1540789 prefixEnd_1540789 58604840308183510344559 := by
  unfold tailWord_1540789
  simp only [CollatzResearch.WordTrace]
  refine ⟨56197191614992073656201421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37464794409994715770800947 56197191614992073656201421)
  ·
    refine ⟨21073946855622027621075533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56197191614992073656201421 21073946855622027621075533)
    ·
      refine ⟨7902730070858260357903325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21073946855622027621075533 7902730070858260357903325)
      ·
        refine ⟨2963523776571847634213747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7902730070858260357903325 2963523776571847634213747)
        ·
          refine ⟨4445285664857771451320621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2963523776571847634213747 4445285664857771451320621)
          ·
            refine ⟨1666982124321664294245233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4445285664857771451320621 1666982124321664294245233)
            ·
              refine ⟨1250236593241248220683925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1666982124321664294245233 1250236593241248220683925)
              ·
                refine ⟨58604840308183510344559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1250236593241248220683925 58604840308183510344559)
                ·
                  rfl

theorem cell22_1540789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 6].length) (baseStart_1540789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540789 prefixEnd_1540789 := by exact prefixLift 1540789
  have htrace : WordTrace (prefixWord ++ tailWord_1540789) baseStart_1540789 baseEnd_1540789 := by
    simpa [prefixWord, tailWord_1540789, baseEnd_1540789] using wordTrace_append hprefix tailTrace_1540789
  have hstable : (prefixWord ++ tailWord_1540789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540789).length < 2 ^ (prefixWord ++ tailWord_1540789).sum := by decide
  have hdescent : baseEnd_1540789 < baseStart_1540789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540800 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 7]
def baseStart_1540800 : Nat := 118140960795 + 1540800 * 2 ^ 59
def prefixEnd_1540800 : Nat := 4983230072969 + 3 ^ 40 * 1540800 * 2
def baseEnd_1540800 : Nat := 175815776099483743691999

theorem tailTrace_1540800 : CollatzResearch.WordTrace tailWord_1540800 prefixEnd_1540800 175815776099483743691999 := by
  unfold tailWord_1540800
  simp only [CollatzResearch.WordTrace]
  refine ⟨28098796408976111267425927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37465061878634815023234569 28098796408976111267425927)
  ·
    refine ⟨42148194613464166901138891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28098796408976111267425927 42148194613464166901138891)
    ·
      refine ⟨63222291920196250351708337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42148194613464166901138891 63222291920196250351708337)
      ·
        refine ⟨47416718940147187763781253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63222291920196250351708337 47416718940147187763781253)
        ·
          refine ⟨8890634801277597705708985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47416718940147187763781253 8890634801277597705708985)
          ·
            refine ⟨6667976100958198279281739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8890634801277597705708985 6667976100958198279281739)
            ·
              refine ⟨10001964151437297418922609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6667976100958198279281739 10001964151437297418922609)
              ·
                refine ⟨7501473113577973064191957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10001964151437297418922609 7501473113577973064191957)
                ·
                  refine ⟨175815776099483743691999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7501473113577973064191957 175815776099483743691999)
                  ·
                    rfl

theorem cell22_1540800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 7].length) (baseStart_1540800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540800 prefixEnd_1540800 := by exact prefixLift 1540800
  have htrace : WordTrace (prefixWord ++ tailWord_1540800) baseStart_1540800 baseEnd_1540800 := by
    simpa [prefixWord, tailWord_1540800, baseEnd_1540800] using wordTrace_append hprefix tailTrace_1540800
  have hstable : (prefixWord ++ tailWord_1540800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540800).length < 2 ^ (prefixWord ++ tailWord_1540800).sum := by decide
  have hdescent : baseEnd_1540800 < baseStart_1540800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540806 : List Nat := [6, 1, 2, 1, 2, 2, 8]
def baseStart_1540806 : Nat := 118140960795 + 1540806 * 2 ^ 59
def prefixEnd_1540806 : Nat := 4983230072969 + 3 ^ 40 * 1540806 * 2
def baseEnd_1540806 : Nat := 19535162304484045015777

theorem tailTrace_1540806 : CollatzResearch.WordTrace tailWord_1540806 prefixEnd_1540806 19535162304484045015777 := by
  unfold tailWord_1540806
  simp only [CollatzResearch.WordTrace]
  refine ⟨1756181614247827673736571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37465207770620323706380181 1756181614247827673736571)
  ·
    refine ⟨2634272421371741510604857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1756181614247827673736571 2634272421371741510604857)
    ·
      refine ⟨1975704316028806132953643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2634272421371741510604857 1975704316028806132953643)
      ·
        refine ⟨2963556474043209199430465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1975704316028806132953643 2963556474043209199430465)
        ·
          refine ⟨2222667355532406899572849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2963556474043209199430465 2222667355532406899572849)
          ·
            refine ⟨1667000516649305174679637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2222667355532406899572849 1667000516649305174679637)
            ·
              refine ⟨19535162304484045015777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1667000516649305174679637 19535162304484045015777)
              ·
                rfl

theorem cell22_1540806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 8].length) (baseStart_1540806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540806 prefixEnd_1540806 := by exact prefixLift 1540806
  have htrace : WordTrace (prefixWord ++ tailWord_1540806) baseStart_1540806 baseEnd_1540806 := by
    simpa [prefixWord, tailWord_1540806, baseEnd_1540806] using wordTrace_append hprefix tailTrace_1540806
  have hstable : (prefixWord ++ tailWord_1540806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540806).length < 2 ^ (prefixWord ++ tailWord_1540806).sum := by decide
  have hdescent : baseEnd_1540806 < baseStart_1540806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540847 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 3, 4]
def baseStart_1540847 : Nat := 118140960795 + 1540847 * 2 ^ 59
def prefixEnd_1540847 : Nat := 4983230072969 + 3 ^ 40 * 1540847 * 2
def baseEnd_1540847 : Nat := 527463417358958775150853

theorem tailTrace_1540847 : CollatzResearch.WordTrace tailWord_1540847 prefixEnd_1540847 527463417358958775150853 := by
  unfold tailWord_1540847
  simp only [CollatzResearch.WordTrace]
  refine ⟨56199307048781949561812795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37466204699187966374541863 56199307048781949561812795)
  ·
    refine ⟨84298960573172924342719193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56199307048781949561812795 84298960573172924342719193)
    ·
      refine ⟨63224220429879693257039395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84298960573172924342719193 63224220429879693257039395)
      ·
        refine ⟨94836330644819539885559093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63224220429879693257039395 94836330644819539885559093)
        ·
          refine ⟨8890905997951831864271165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 94836330644819539885559093 8890905997951831864271165)
          ·
            refine ⟨3334089749231936949101687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8890905997951831864271165 3334089749231936949101687)
            ·
              refine ⟨5001134623847905423652531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3334089749231936949101687 5001134623847905423652531)
              ·
                refine ⟨7501701935771858135478797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5001134623847905423652531 7501701935771858135478797)
                ·
                  refine ⟨2813138225914446800804549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7501701935771858135478797 2813138225914446800804549)
                  ·
                    refine ⟨527463417358958775150853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2813138225914446800804549 527463417358958775150853)
                    ·
                      rfl

theorem cell22_1540847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 3, 4].length) (baseStart_1540847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540847 prefixEnd_1540847 := by exact prefixLift 1540847
  have htrace : WordTrace (prefixWord ++ tailWord_1540847) baseStart_1540847 baseEnd_1540847 := by
    simpa [prefixWord, tailWord_1540847, baseEnd_1540847] using wordTrace_append hprefix tailTrace_1540847
  have hstable : (prefixWord ++ tailWord_1540847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540847).length < 2 ^ (prefixWord ++ tailWord_1540847).sum := by decide
  have hdescent : baseEnd_1540847 < baseStart_1540847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540875 : List Nat := [1, 1, 1, 1, 5, 1, 1, 2, 3, 6]
def baseStart_1540875 : Nat := 118140960795 + 1540875 * 2 ^ 59
def prefixEnd_1540875 : Nat := 4983230072969 + 3 ^ 40 * 1540875 * 2
def baseEnd_1540875 : Nat := 527473002331176035450767

theorem tailTrace_1540875 : CollatzResearch.WordTrace tailWord_1540875 prefixEnd_1540875 527473002331176035450767 := by
  unfold tailWord_1540875
  simp only [CollatzResearch.WordTrace]
  refine ⟨56200328292680510343832079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37466885528453673562554719 56200328292680510343832079)
  ·
    refine ⟨84300492439020765515748119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56200328292680510343832079 84300492439020765515748119)
    ·
      refine ⟨126450738658531148273622179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84300492439020765515748119 126450738658531148273622179)
      ·
        refine ⟨189676107987796722410433269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126450738658531148273622179 189676107987796722410433269)
        ·
          refine ⟨17782135123855942725978119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 189676107987796722410433269 17782135123855942725978119)
          ·
            refine ⟨26673202685783914088967179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17782135123855942725978119 26673202685783914088967179)
            ·
              refine ⟨40009804028675871133450769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26673202685783914088967179 40009804028675871133450769)
              ·
                refine ⟨30007353021506903350088077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40009804028675871133450769 30007353021506903350088077)
                ·
                  refine ⟨11252757383065088756283029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30007353021506903350088077 11252757383065088756283029)
                  ·
                    refine ⟨527473002331176035450767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11252757383065088756283029 527473002331176035450767)
                    ·
                      rfl

theorem cell22_1540875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 3, 6].length) (baseStart_1540875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540875 prefixEnd_1540875 := by exact prefixLift 1540875
  have htrace : WordTrace (prefixWord ++ tailWord_1540875) baseStart_1540875 baseEnd_1540875 := by
    simpa [prefixWord, tailWord_1540875, baseEnd_1540875] using wordTrace_append hprefix tailTrace_1540875
  have hstable : (prefixWord ++ tailWord_1540875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540875).length < 2 ^ (prefixWord ++ tailWord_1540875).sum := by decide
  have hdescent : baseEnd_1540875 < baseStart_1540875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540905 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 2, 7]
def baseStart_1540905 : Nat := 118140960795 + 1540905 * 2 ^ 59
def prefixEnd_1540905 : Nat := 4983230072969 + 3 ^ 40 * 1540905 * 2
def baseEnd_1540905 : Nat := 527483271944265957200675

theorem tailTrace_1540905 : CollatzResearch.WordTrace tailWord_1540905 prefixEnd_1540905 527483271944265957200675 := by
  unfold tailWord_1540905
  simp only [CollatzResearch.WordTrace]
  refine ⟨56201422482571825467424169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37467614988381216978282779 56201422482571825467424169)
  ·
    refine ⟨42151066861928869100568127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56201422482571825467424169 42151066861928869100568127)
    ·
      refine ⟨63226600292893303650852191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42151066861928869100568127 63226600292893303650852191)
      ·
        refine ⟨94839900439339955476278287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63226600292893303650852191 94839900439339955476278287)
        ·
          refine ⟨142259850659009933214417431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94839900439339955476278287 142259850659009933214417431)
          ·
            refine ⟨213389775988514899821626147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142259850659009933214417431 213389775988514899821626147)
            ·
              refine ⟨320084663982772349732439221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213389775988514899821626147 320084663982772349732439221)
              ·
                refine ⟨30007937248384907787416177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 320084663982772349732439221 30007937248384907787416177)
                ·
                  refine ⟨22505952936288680840562133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30007937248384907787416177 22505952936288680840562133)
                  ·
                    refine ⟨527483271944265957200675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22505952936288680840562133 527483271944265957200675)
                    ·
                      rfl

theorem cell22_1540905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_1540905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540905 prefixEnd_1540905 := by exact prefixLift 1540905
  have htrace : WordTrace (prefixWord ++ tailWord_1540905) baseStart_1540905 baseEnd_1540905 := by
    simpa [prefixWord, tailWord_1540905, baseEnd_1540905] using wordTrace_append hprefix tailTrace_1540905
  have hstable : (prefixWord ++ tailWord_1540905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540905).length < 2 ^ (prefixWord ++ tailWord_1540905).sum := by decide
  have hdescent : baseEnd_1540905 < baseStart_1540905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540952 : List Nat := [2, 1, 2, 2, 1, 1, 1, 7, 5]
def baseStart_1540952 : Nat := 118140960795 + 1540952 * 2 ^ 59
def prefixEnd_1540952 : Nat := 4983230072969 + 3 ^ 40 * 1540952 * 2
def baseEnd_1540952 : Nat := 175833120334924500425177

theorem tailTrace_1540952 : CollatzResearch.WordTrace tailWord_1540952 prefixEnd_1540952 175833120334924500425177 := by
  unfold tailWord_1540952
  simp only [CollatzResearch.WordTrace]
  refine ⟨28101568356700776247192555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37468757808934368329590073 28101568356700776247192555)
  ·
    refine ⟨42152352535051164370788833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28101568356700776247192555 42152352535051164370788833)
    ·
      refine ⟨31614264401288373278091625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42152352535051164370788833 31614264401288373278091625)
      ·
        refine ⟨23710698300966279958568719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31614264401288373278091625 23710698300966279958568719)
        ·
          refine ⟨35566047451449419937853079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23710698300966279958568719 35566047451449419937853079)
          ·
            refine ⟨53349071177174129906779619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35566047451449419937853079 53349071177174129906779619)
            ·
              refine ⟨80023606765761194860169429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 53349071177174129906779619 80023606765761194860169429)
              ·
                refine ⟨1875553283572528004535221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 80023606765761194860169429 1875553283572528004535221)
                ·
                  refine ⟨175833120334924500425177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1875553283572528004535221 175833120334924500425177)
                  ·
                    rfl

theorem cell22_1540952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 7, 5].length) (baseStart_1540952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540952 prefixEnd_1540952 := by exact prefixLift 1540952
  have htrace : WordTrace (prefixWord ++ tailWord_1540952) baseStart_1540952 baseEnd_1540952 := by
    simpa [prefixWord, tailWord_1540952, baseEnd_1540952] using wordTrace_append hprefix tailTrace_1540952
  have hstable : (prefixWord ++ tailWord_1540952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540952).length < 2 ^ (prefixWord ++ tailWord_1540952).sum := by decide
  have hdescent : baseEnd_1540952 < baseStart_1540952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540956 : List Nat := [2, 2, 4, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1540956 : Nat := 118140960795 + 1540956 * 2 ^ 59
def prefixEnd_1540956 : Nat := 4983230072969 + 3 ^ 40 * 1540956 * 2
def baseEnd_1540956 : Nat := 527500730286518824175519

theorem tailTrace_1540956 : CollatzResearch.WordTrace tailWord_1540956 prefixEnd_1540956 527500730286518824175519 := by
  unfold tailWord_1540956
  simp only [CollatzResearch.WordTrace]
  refine ⟨28101641302693530588765361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37468855070258040785020481 28101641302693530588765361)
  ·
    refine ⟨21076230977020147941574021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28101641302693530588765361 21076230977020147941574021)
    ·
      refine ⟨3951793308191277739045129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21076230977020147941574021 3951793308191277739045129)
      ·
        refine ⟨2963844981143458304283847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3951793308191277739045129 2963844981143458304283847)
        ·
          refine ⟨4445767471715187456425771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2963844981143458304283847 4445767471715187456425771)
          ·
            refine ⟨6668651207572781184638657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4445767471715187456425771 6668651207572781184638657)
            ·
              refine ⟨5001488405679585888478993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6668651207572781184638657 5001488405679585888478993)
              ·
                refine ⟨3751116304259689416359245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5001488405679585888478993 3751116304259689416359245)
                ·
                  refine ⟨1406668614097383531134717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3751116304259689416359245 1406668614097383531134717)
                  ·
                    refine ⟨527500730286518824175519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1406668614097383531134717 527500730286518824175519)
                    ·
                      rfl

theorem cell22_1540956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1540956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540956 prefixEnd_1540956 := by exact prefixLift 1540956
  have htrace : WordTrace (prefixWord ++ tailWord_1540956) baseStart_1540956 baseEnd_1540956 := by
    simpa [prefixWord, tailWord_1540956, baseEnd_1540956] using wordTrace_append hprefix tailTrace_1540956
  have hstable : (prefixWord ++ tailWord_1540956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540956).length < 2 ^ (prefixWord ++ tailWord_1540956).sum := by decide
  have hdescent : baseEnd_1540956 < baseStart_1540956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1540990 : List Nat := [4, 2, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_1540990 : Nat := 118140960795 + 1540990 * 2 ^ 59
def prefixEnd_1540990 : Nat := 4983230072969 + 3 ^ 40 * 1540990 * 2
def baseEnd_1540990 : Nat := 527512369181354068825415

theorem tailTrace_1540990 : CollatzResearch.WordTrace tailWord_1540990 prefixEnd_1540990 527512369181354068825415 := by
  unfold tailWord_1540990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7025565335907985623033553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37469681791509256656178949 7025565335907985623033553)
  ·
    refine ⟨5269174001930989217275165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7025565335907985623033553 5269174001930989217275165)
    ·
      refine ⟨1975940250724120956478187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5269174001930989217275165 1975940250724120956478187)
      ·
        refine ⟨2963910376086181434717281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1975940250724120956478187 2963910376086181434717281)
        ·
          refine ⟨2222932782064636076037961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2963910376086181434717281 2222932782064636076037961)
          ·
            refine ⟨1667199586548477057028471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2222932782064636076037961 1667199586548477057028471)
            ·
              refine ⟨2500799379822715585542707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667199586548477057028471 2500799379822715585542707)
              ·
                refine ⟨3751199069734073378314061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2500799379822715585542707 3751199069734073378314061)
                ·
                  refine ⟨1406699651150277516867773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3751199069734073378314061 1406699651150277516867773)
                  ·
                    refine ⟨527512369181354068825415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1406699651150277516867773 527512369181354068825415)
                    ·
                      rfl

theorem cell22_1540990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_1540990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1540990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1540990 prefixEnd_1540990 := by exact prefixLift 1540990
  have htrace : WordTrace (prefixWord ++ tailWord_1540990) baseStart_1540990 baseEnd_1540990 := by
    simpa [prefixWord, tailWord_1540990, baseEnd_1540990] using wordTrace_append hprefix tailTrace_1540990
  have hstable : (prefixWord ++ tailWord_1540990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1540990).length < 2 ^ (prefixWord ++ tailWord_1540990).sum := by decide
  have hdescent : baseEnd_1540990 < baseStart_1540990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1540990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541027 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 1, 6]
def baseStart_1541027 : Nat := 118140960795 + 1541027 * 2 ^ 59
def prefixEnd_1541027 : Nat := 4983230072969 + 3 ^ 40 * 1541027 * 2
def baseEnd_1541027 : Nat := 527525035037498305650301

theorem tailTrace_1541027 : CollatzResearch.WordTrace tailWord_1541027 prefixEnd_1541027 527525035037498305650301 := by
  unfold tailWord_1541027
  simp only [CollatzResearch.WordTrace]
  refine ⟨56205872188129840303365335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37470581458753226868910223 56205872188129840303365335)
  ·
    refine ⟨84308808282194760455048003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56205872188129840303365335 84308808282194760455048003)
    ·
      refine ⟨126463212423292140682572005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84308808282194760455048003 126463212423292140682572005)
      ·
        refine ⟨23711852329367276377982251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126463212423292140682572005 23711852329367276377982251)
        ·
          refine ⟨35567778494050914566973377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23711852329367276377982251 35567778494050914566973377)
          ·
            refine ⟨26675833870538185925230033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35567778494050914566973377 26675833870538185925230033)
            ·
              refine ⟨20006875402903639443922525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26675833870538185925230033 20006875402903639443922525)
              ·
                refine ⟨7502578276088864791470947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20006875402903639443922525 7502578276088864791470947)
                ·
                  refine ⟨11253867414133297187206421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7502578276088864791470947 11253867414133297187206421)
                  ·
                    refine ⟨527525035037498305650301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11253867414133297187206421 527525035037498305650301)
                    ·
                      rfl

theorem cell22_1541027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 6].length) (baseStart_1541027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541027 prefixEnd_1541027 := by exact prefixLift 1541027
  have htrace : WordTrace (prefixWord ++ tailWord_1541027) baseStart_1541027 baseEnd_1541027 := by
    simpa [prefixWord, tailWord_1541027, baseEnd_1541027] using wordTrace_append hprefix tailTrace_1541027
  have hstable : (prefixWord ++ tailWord_1541027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541027).length < 2 ^ (prefixWord ++ tailWord_1541027).sum := by decide
  have hdescent : baseEnd_1541027 < baseStart_1541027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541048 : List Nat := [2, 1, 2, 1, 2, 6, 2, 2, 4]
def baseStart_1541048 : Nat := 118140960795 + 1541048 * 2 ^ 59
def prefixEnd_1541048 : Nat := 4983230072969 + 3 ^ 40 * 1541048 * 2
def baseEnd_1541048 : Nat := 175844074588887083625079

theorem tailTrace_1541048 : CollatzResearch.WordTrace tailWord_1541048 prefixEnd_1541048 175844074588887083625079 := by
  unfold tailWord_1541048
  simp only [CollatzResearch.WordTrace]
  refine ⟨28103319060526880444939899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37471092080702507259919865 28103319060526880444939899)
  ·
    refine ⟨42154978590790320667409849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28103319060526880444939899 42154978590790320667409849)
    ·
      refine ⟨31616233943092740500557387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42154978590790320667409849 31616233943092740500557387)
      ·
        refine ⟨47424350914639110750836081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31616233943092740500557387 47424350914639110750836081)
        ·
          refine ⟨35568263185979333063127061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47424350914639110750836081 35568263185979333063127061)
          ·
            refine ⟨1667262336842781237334081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35568263185979333063127061 1667262336842781237334081)
            ·
              refine ⟨1250446752632085928000561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1667262336842781237334081 1250446752632085928000561)
              ·
                refine ⟨937835064474064446000421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1250446752632085928000561 937835064474064446000421)
                ·
                  refine ⟨175844074588887083625079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 937835064474064446000421 175844074588887083625079)
                  ·
                    rfl

theorem cell22_1541048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 2, 4].length) (baseStart_1541048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541048 prefixEnd_1541048 := by exact prefixLift 1541048
  have htrace : WordTrace (prefixWord ++ tailWord_1541048) baseStart_1541048 baseEnd_1541048 := by
    simpa [prefixWord, tailWord_1541048, baseEnd_1541048] using wordTrace_append hprefix tailTrace_1541048
  have hstable : (prefixWord ++ tailWord_1541048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541048).length < 2 ^ (prefixWord ++ tailWord_1541048).sum := by decide
  have hdescent : baseEnd_1541048 < baseStart_1541048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541072 : List Nat := [2, 1, 1, 1, 1, 2, 3, 1, 4, 6]
def baseStart_1541072 : Nat := 118140960795 + 1541072 * 2 ^ 59
def prefixEnd_1541072 : Nat := 4983230072969 + 3 ^ 40 * 1541072 * 2
def baseEnd_1541072 : Nat := 527540439457133188275163

theorem tailTrace_1541072 : CollatzResearch.WordTrace tailWord_1541072 prefixEnd_1541072 527540439457133188275163 := by
  unfold tailWord_1541072
  simp only [CollatzResearch.WordTrace]
  refine ⟨28103756736483406494376735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37471675648644541992502313 28103756736483406494376735)
  ·
    refine ⟨42155635104725109741565103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28103756736483406494376735 42155635104725109741565103)
    ·
      refine ⟨63233452657087664612347655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42155635104725109741565103 63233452657087664612347655)
      ·
        refine ⟨94850178985631496918521483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63233452657087664612347655 94850178985631496918521483)
        ·
          refine ⟨142275268478447245377782225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94850178985631496918521483 142275268478447245377782225)
          ·
            refine ⟨106706451358835434033336669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 142275268478447245377782225 106706451358835434033336669)
            ·
              refine ⟨40014919259563287762501251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 106706451358835434033336669 40014919259563287762501251)
              ·
                refine ⟨60022378889344931643751877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40014919259563287762501251 60022378889344931643751877)
                ·
                  refine ⟨11254196041752174683203477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 60022378889344931643751877 11254196041752174683203477)
                  ·
                    refine ⟨527540439457133188275163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11254196041752174683203477 527540439457133188275163)
                    ·
                      rfl

theorem cell22_1541072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_1541072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541072 prefixEnd_1541072 := by exact prefixLift 1541072
  have htrace : WordTrace (prefixWord ++ tailWord_1541072) baseStart_1541072 baseEnd_1541072 := by
    simpa [prefixWord, tailWord_1541072, baseEnd_1541072] using wordTrace_append hprefix tailTrace_1541072
  have hstable : (prefixWord ++ tailWord_1541072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541072).length < 2 ^ (prefixWord ++ tailWord_1541072).sum := by decide
  have hdescent : baseEnd_1541072 < baseStart_1541072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541076 : List Nat := [2, 4, 1, 2, 1, 3, 3, 6]
def baseStart_1541076 : Nat := 118140960795 + 1541076 * 2 ^ 59
def prefixEnd_1541076 : Nat := 4983230072969 + 3 ^ 40 * 1541076 * 2
def baseEnd_1541076 : Nat := 58615756526542056797239

theorem tailTrace_1541076 : CollatzResearch.WordTrace tailWord_1541076 prefixEnd_1541076 58615756526542056797239 := by
  unfold tailWord_1541076
  simp only [CollatzResearch.WordTrace]
  refine ⟨28103829682476160835949541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37471772909968214447932721 28103829682476160835949541)
  ·
    refine ⟨5269468065464280156740539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28103829682476160835949541 5269468065464280156740539)
    ·
      refine ⟨7904202098196420235110809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5269468065464280156740539 7904202098196420235110809)
      ·
        refine ⟨5928151573647315176333107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7904202098196420235110809 5928151573647315176333107)
        ·
          refine ⟨8892227360470972764499661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5928151573647315176333107 8892227360470972764499661)
          ·
            refine ⟨3334585260176614786687373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8892227360470972764499661 3334585260176614786687373)
            ·
              refine ⟨1250469472566230545007765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3334585260176614786687373 1250469472566230545007765)
              ·
                refine ⟨58615756526542056797239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1250469472566230545007765 58615756526542056797239)
                ·
                  rfl

theorem cell22_1541076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 6].length) (baseStart_1541076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541076 prefixEnd_1541076 := by exact prefixLift 1541076
  have htrace : WordTrace (prefixWord ++ tailWord_1541076) baseStart_1541076 baseEnd_1541076 := by
    simpa [prefixWord, tailWord_1541076, baseEnd_1541076] using wordTrace_append hprefix tailTrace_1541076
  have hstable : (prefixWord ++ tailWord_1541076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541076).length < 2 ^ (prefixWord ++ tailWord_1541076).sum := by decide
  have hdescent : baseEnd_1541076 < baseStart_1541076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541078 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1541078 : Nat := 118140960795 + 1541078 * 2 ^ 59
def prefixEnd_1541078 : Nat := 4983230072969 + 3 ^ 40 * 1541078 * 2
def baseEnd_1541078 : Nat := 527542493379751172625145

theorem tailTrace_1541078 : CollatzResearch.WordTrace tailWord_1541078 prefixEnd_1541078 527542493379751172625145 := by
  unfold tailWord_1541078
  simp only [CollatzResearch.WordTrace]
  refine ⟨3512983269434067250841993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37471821540630050675647925 3512983269434067250841993)
  ·
    refine ⟨2634737452075550438131495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3512983269434067250841993 2634737452075550438131495)
    ·
      refine ⟨3952106178113325657197243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2634737452075550438131495 3952106178113325657197243)
      ·
        refine ⟨5928159267169988485795865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3952106178113325657197243 5928159267169988485795865)
        ·
          refine ⟨4446119450377491364346899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5928159267169988485795865 4446119450377491364346899)
          ·
            refine ⟨6669179175566237046520349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4446119450377491364346899 6669179175566237046520349)
            ·
              refine ⟨2500942190837338892445131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6669179175566237046520349 2500942190837338892445131)
              ·
                refine ⟨3751413286256008338667697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2500942190837338892445131 3751413286256008338667697)
                ·
                  refine ⟨2813559964692006254000773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3751413286256008338667697 2813559964692006254000773)
                  ·
                    refine ⟨527542493379751172625145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2813559964692006254000773 527542493379751172625145)
                    ·
                      rfl

theorem cell22_1541078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1541078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541078 prefixEnd_1541078 := by exact prefixLift 1541078
  have htrace : WordTrace (prefixWord ++ tailWord_1541078) baseStart_1541078 baseEnd_1541078 := by
    simpa [prefixWord, tailWord_1541078, baseEnd_1541078] using wordTrace_append hprefix tailTrace_1541078
  have hstable : (prefixWord ++ tailWord_1541078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541078).length < 2 ^ (prefixWord ++ tailWord_1541078).sum := by decide
  have hdescent : baseEnd_1541078 < baseStart_1541078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541151 : List Nat := [1, 1, 2, 4, 1, 3, 2, 3, 1, 4]
def baseStart_1541151 : Nat := 118140960795 + 1541151 * 2 ^ 59
def prefixEnd_1541151 : Nat := 4983230072969 + 3 ^ 40 * 1541151 * 2
def baseEnd_1541151 : Nat := 527567482771603315549921

theorem tailTrace_1541151 : CollatzResearch.WordTrace tailWord_1541151 prefixEnd_1541151 527567482771603315549921 := by
  unfold tailWord_1541151
  simp only [CollatzResearch.WordTrace]
  refine ⟨56210394839680609480879307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37473596559787072987252871 56210394839680609480879307)
  ·
    refine ⟨84315592259520914221318961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56210394839680609480879307 84315592259520914221318961)
    ·
      refine ⟨63236694194640685665989221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84315592259520914221318961 63236694194640685665989221)
      ·
        refine ⟨11856880161495128562372979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 63236694194640685665989221 11856880161495128562372979)
        ·
          refine ⟨17785320242242692843559469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11856880161495128562372979 17785320242242692843559469)
          ·
            refine ⟨6669495090841009816334801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17785320242242692843559469 6669495090841009816334801)
            ·
              refine ⟨5002121318130757362251101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6669495090841009816334801 5002121318130757362251101)
              ·
                refine ⟨1875795494299034010844163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5002121318130757362251101 1875795494299034010844163)
                ·
                  refine ⟨2813693241448551016266245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875795494299034010844163 2813693241448551016266245)
                  ·
                    refine ⟨527567482771603315549921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2813693241448551016266245 527567482771603315549921)
                    ·
                      rfl

theorem cell22_1541151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 1, 4].length) (baseStart_1541151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541151 prefixEnd_1541151 := by exact prefixLift 1541151
  have htrace : WordTrace (prefixWord ++ tailWord_1541151) baseStart_1541151 baseEnd_1541151 := by
    simpa [prefixWord, tailWord_1541151, baseEnd_1541151] using wordTrace_append hprefix tailTrace_1541151
  have hstable : (prefixWord ++ tailWord_1541151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541151).length < 2 ^ (prefixWord ++ tailWord_1541151).sum := by decide
  have hdescent : baseEnd_1541151 < baseStart_1541151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541185 : List Nat := [1, 2, 5, 1, 3, 2, 1, 2, 1, 4]
def baseStart_1541185 : Nat := 118140960795 + 1541185 * 2 ^ 59
def prefixEnd_1541185 : Nat := 4983230072969 + 3 ^ 40 * 1541185 * 2
def baseEnd_1541185 : Nat := 527579121666438560199817

theorem tailTrace_1541185 : CollatzResearch.WordTrace tailWord_1541185 prefixEnd_1541185 527579121666438560199817 := by
  unfold tailWord_1541185
  simp only [CollatzResearch.WordTrace]
  refine ⟨56211634921557433287617009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37474423281038288858411339 56211634921557433287617009)
  ·
    refine ⟨42158726191168074965712757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56211634921557433287617009 42158726191168074965712757)
    ·
      refine ⟨3952380580422007028035571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42158726191168074965712757 3952380580422007028035571)
      ·
        refine ⟨5928570870633010542053357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3952380580422007028035571 5928570870633010542053357)
        ·
          refine ⟨2223214076487378953270009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5928570870633010542053357 2223214076487378953270009)
          ·
            refine ⟨1667410557365534214952507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2223214076487378953270009 1667410557365534214952507)
            ·
              refine ⟨2501115836048301322428761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667410557365534214952507 2501115836048301322428761)
              ·
                refine ⟨1875836877036225991821571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2501115836048301322428761 1875836877036225991821571)
                ·
                  refine ⟨2813755315554338987732357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875836877036225991821571 2813755315554338987732357)
                  ·
                    refine ⟨527579121666438560199817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2813755315554338987732357 527579121666438560199817)
                    ·
                      rfl

theorem cell22_1541185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_1541185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541185 prefixEnd_1541185 := by exact prefixLift 1541185
  have htrace : WordTrace (prefixWord ++ tailWord_1541185) baseStart_1541185 baseEnd_1541185 := by
    simpa [prefixWord, tailWord_1541185, baseEnd_1541185] using wordTrace_append hprefix tailTrace_1541185
  have hstable : (prefixWord ++ tailWord_1541185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541185).length < 2 ^ (prefixWord ++ tailWord_1541185).sum := by decide
  have hdescent : baseEnd_1541185 < baseStart_1541185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541194 : List Nat := [3, 1, 2, 1, 1, 2, 4, 8]
def baseStart_1541194 : Nat := 118140960795 + 1541194 * 2 ^ 59
def prefixEnd_1541194 : Nat := 4983230072969 + 3 ^ 40 * 1541194 * 2
def baseEnd_1541194 : Nat := 58620244727818392969421

theorem tailTrace_1541194 : CollatzResearch.WordTrace tailWord_1541194 prefixEnd_1541194 58620244727818392969421 := by
  unfold tailWord_1541194
  simp only [CollatzResearch.WordTrace]
  refine ⟨14052990794631206956173659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37474642119016551883129757 14052990794631206956173659)
  ·
    refine ⟨21079486191946810434260489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14052990794631206956173659 21079486191946810434260489)
    ·
      refine ⟨15809614643960107825695367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21079486191946810434260489 15809614643960107825695367)
      ·
        refine ⟨23714421965940161738543051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15809614643960107825695367 23714421965940161738543051)
        ·
          refine ⟨35571632948910242607814577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23714421965940161738543051 35571632948910242607814577)
          ·
            refine ⟨26678724711682681955860933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35571632948910242607814577 26678724711682681955860933)
            ·
              refine ⟨5002260883440502866723925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26678724711682681955860933 5002260883440502866723925)
              ·
                refine ⟨58620244727818392969421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5002260883440502866723925 58620244727818392969421)
                ·
                  rfl

theorem cell22_1541194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 8].length) (baseStart_1541194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541194 prefixEnd_1541194 := by exact prefixLift 1541194
  have htrace : WordTrace (prefixWord ++ tailWord_1541194) baseStart_1541194 baseEnd_1541194 := by
    simpa [prefixWord, tailWord_1541194, baseEnd_1541194] using wordTrace_append hprefix tailTrace_1541194
  have hstable : (prefixWord ++ tailWord_1541194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541194).length < 2 ^ (prefixWord ++ tailWord_1541194).sum := by decide
  have hdescent : baseEnd_1541194 < baseStart_1541194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541271 : List Nat := [1, 1, 3, 3, 3, 1, 1, 2, 2, 5]
def baseStart_1541271 : Nat := 118140960795 + 1541271 * 2 ^ 59
def prefixEnd_1541271 : Nat := 4983230072969 + 3 ^ 40 * 1541271 * 2
def baseEnd_1541271 : Nat := 527608561223963002549553

theorem tailTrace_1541271 : CollatzResearch.WordTrace tailWord_1541271 prefixEnd_1541271 527608561223963002549553 := by
  unfold tailWord_1541271
  simp only [CollatzResearch.WordTrace]
  refine ⟨56214771599245869975247667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37476514399497246650165111 56214771599245869975247667)
  ·
    refine ⟨84322157398868804962871501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56214771599245869975247667 84322157398868804962871501)
    ·
      refine ⟨31620809024575801861076813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84322157398868804962871501 31620809024575801861076813)
      ·
        refine ⟨11857803384215925697903805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31620809024575801861076813 11857803384215925697903805)
        ·
          refine ⟨4446676269080972136713927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11857803384215925697903805 4446676269080972136713927)
          ·
            refine ⟨6670014403621458205070891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4446676269080972136713927 6670014403621458205070891)
            ·
              refine ⟨10005021605432187307606337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6670014403621458205070891 10005021605432187307606337)
              ·
                refine ⟨7503766204074140480704753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10005021605432187307606337 7503766204074140480704753)
                ·
                  refine ⟨5627824653055605360528565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7503766204074140480704753 5627824653055605360528565)
                  ·
                    refine ⟨527608561223963002549553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5627824653055605360528565 527608561223963002549553)
                    ·
                      rfl

theorem cell22_1541271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_1541271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541271 prefixEnd_1541271 := by exact prefixLift 1541271
  have htrace : WordTrace (prefixWord ++ tailWord_1541271) baseStart_1541271 baseEnd_1541271 := by
    simpa [prefixWord, tailWord_1541271, baseEnd_1541271] using wordTrace_append hprefix tailTrace_1541271
  have hstable : (prefixWord ++ tailWord_1541271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541271).length < 2 ^ (prefixWord ++ tailWord_1541271).sum := by decide
  have hdescent : baseEnd_1541271 < baseStart_1541271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541303 : List Nat := [1, 1, 3, 1, 4, 1, 4, 2, 1, 4]
def baseStart_1541303 : Nat := 118140960795 + 1541303 * 2 ^ 59
def prefixEnd_1541303 : Nat := 4983230072969 + 3 ^ 40 * 1541303 * 2
def baseEnd_1541303 : Nat := 527619515477925585749455

theorem tailTrace_1541303 : CollatzResearch.WordTrace tailWord_1541303 prefixEnd_1541303 527619515477925585749455 := by
  unfold tailWord_1541303
  simp only [CollatzResearch.WordTrace]
  refine ⟨56215938735129939440412563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37477292490086626293608375 56215938735129939440412563)
  ·
    refine ⟨84323908102694909160618845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56215938735129939440412563 84323908102694909160618845)
    ·
      refine ⟨31621465538510590935232067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84323908102694909160618845 31621465538510590935232067)
      ·
        refine ⟨47432198307765886402848101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31621465538510590935232067 47432198307765886402848101)
        ·
          refine ⟨8893537182706103700534019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 47432198307765886402848101 8893537182706103700534019)
          ·
            refine ⟨13340305774059155550801029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8893537182706103700534019 13340305774059155550801029)
            ·
              refine ⟨2501307332636091665775193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13340305774059155550801029 2501307332636091665775193)
              ·
                refine ⟨1875980499477068749331395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2501307332636091665775193 1875980499477068749331395)
                ·
                  refine ⟨2813970749215603123997093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1875980499477068749331395 2813970749215603123997093)
                  ·
                    refine ⟨527619515477925585749455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2813970749215603123997093 527619515477925585749455)
                    ·
                      rfl

theorem cell22_1541303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_1541303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541303 prefixEnd_1541303 := by exact prefixLift 1541303
  have htrace : WordTrace (prefixWord ++ tailWord_1541303) baseStart_1541303 baseEnd_1541303 := by
    simpa [prefixWord, tailWord_1541303, baseEnd_1541303] using wordTrace_append hprefix tailTrace_1541303
  have hstable : (prefixWord ++ tailWord_1541303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541303).length < 2 ^ (prefixWord ++ tailWord_1541303).sum := by decide
  have hdescent : baseEnd_1541303 < baseStart_1541303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541331 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 2, 4]
def baseStart_1541331 : Nat := 118140960795 + 1541331 * 2 ^ 59
def prefixEnd_1541331 : Nat := 4983230072969 + 3 ^ 40 * 1541331 * 2
def baseEnd_1541331 : Nat := 527629100450142846049369

theorem tailTrace_1541331 : CollatzResearch.WordTrace tailWord_1541331 prefixEnd_1541331 527629100450142846049369 := by
  unfold tailWord_1541331
  simp only [CollatzResearch.WordTrace]
  refine ⟨56216959979028500222431847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37477973319352333481621231 56216959979028500222431847)
  ·
    refine ⟨84325439968542750333647771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56216959979028500222431847 84325439968542750333647771)
    ·
      refine ⟨126488159952814125500471657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84325439968542750333647771 126488159952814125500471657)
      ·
        refine ⟨94866119964610594125353743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126488159952814125500471657 94866119964610594125353743)
        ·
          refine ⟨142299179946915891188030615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94866119964610594125353743 142299179946915891188030615)
          ·
            refine ⟨213448769920373836782045923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 142299179946915891188030615 213448769920373836782045923)
            ·
              refine ⟨320173154880560755173068885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 213448769920373836782045923 320173154880560755173068885)
              ·
                refine ⟨3752029158756571349684401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 320173154880560755173068885 3752029158756571349684401)
                ·
                  refine ⟨2814021869067428512263301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3752029158756571349684401 2814021869067428512263301)
                  ·
                    refine ⟨527629100450142846049369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2814021869067428512263301 527629100450142846049369)
                    ·
                      rfl

theorem cell22_1541331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 2, 4].length) (baseStart_1541331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541331 prefixEnd_1541331 := by exact prefixLift 1541331
  have htrace : WordTrace (prefixWord ++ tailWord_1541331) baseStart_1541331 baseEnd_1541331 := by
    simpa [prefixWord, tailWord_1541331, baseEnd_1541331] using wordTrace_append hprefix tailTrace_1541331
  have hstable : (prefixWord ++ tailWord_1541331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541331).length < 2 ^ (prefixWord ++ tailWord_1541331).sum := by decide
  have hdescent : baseEnd_1541331 < baseStart_1541331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541446 : List Nat := [6, 1, 1, 3, 1, 1, 2, 1, 3, 3]
def baseStart_1541446 : Nat := 118140960795 + 1541446 * 2 ^ 59
def prefixEnd_1541446 : Nat := 4983230072969 + 3 ^ 40 * 1541446 * 2
def baseEnd_1541446 : Nat := 527668467300320879424017

theorem tailTrace_1541446 : CollatzResearch.WordTrace tailWord_1541446 prefixEnd_1541446 527668467300320879424017 := by
  unfold tailWord_1541446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1756911074175371089464631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37480769582407916575245461 1756911074175371089464631)
  ·
    refine ⟨2635366611263056634196947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1756911074175371089464631 2635366611263056634196947)
    ·
      refine ⟨3953049916894584951295421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2635366611263056634196947 3953049916894584951295421)
      ·
        refine ⟨1482393718835469356735783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3953049916894584951295421 1482393718835469356735783)
        ·
          refine ⟨2223590578253204035103675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482393718835469356735783 2223590578253204035103675)
          ·
            refine ⟨3335385867379806052655513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2223590578253204035103675 3335385867379806052655513)
            ·
              refine ⟨2501539400534854539491635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3335385867379806052655513 2501539400534854539491635)
              ·
                refine ⟨3752309100802281809237453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2501539400534854539491635 3752309100802281809237453)
                ·
                  refine ⟨1407115912800855678464045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3752309100802281809237453 1407115912800855678464045)
                  ·
                    refine ⟨527668467300320879424017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1407115912800855678464045 527668467300320879424017)
                    ·
                      rfl

theorem cell22_1541446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 3, 3].length) (baseStart_1541446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541446 prefixEnd_1541446 := by exact prefixLift 1541446
  have htrace : WordTrace (prefixWord ++ tailWord_1541446) baseStart_1541446 baseEnd_1541446 := by
    simpa [prefixWord, tailWord_1541446, baseEnd_1541446] using wordTrace_append hprefix tailTrace_1541446
  have hstable : (prefixWord ++ tailWord_1541446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541446).length < 2 ^ (prefixWord ++ tailWord_1541446).sum := by decide
  have hdescent : baseEnd_1541446 < baseStart_1541446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541485 : List Nat := [1, 5, 1, 1, 1, 3, 1, 2, 4, 3]
def baseStart_1541485 : Nat := 118140960795 + 1541485 * 2 ^ 59
def prefixEnd_1541485 : Nat := 4983230072969 + 3 ^ 40 * 1541485 * 2
def baseEnd_1541485 : Nat := 527681817797337777698897

theorem tailTrace_1541485 : CollatzResearch.WordTrace tailWord_1541485 prefixEnd_1541485 527681817797337777698897 := by
  unfold tailWord_1541485
  simp only [CollatzResearch.WordTrace]
  refine ⟨56222576820470584523537909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37481717880313723015691939 56222576820470584523537909)
  ·
    refine ⟨5270866576919117299081679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56222576820470584523537909 5270866576919117299081679)
    ·
      refine ⟨7906299865378675948622519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5270866576919117299081679 7906299865378675948622519)
      ·
        refine ⟨11859449798068013922933779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7906299865378675948622519 11859449798068013922933779)
        ·
          refine ⟨17789174697102020884400669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11859449798068013922933779 17789174697102020884400669)
          ·
            refine ⟨6670940511413257831650251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17789174697102020884400669 6670940511413257831650251)
            ·
              refine ⟨10006410767119886747475377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6670940511413257831650251 10006410767119886747475377)
              ·
                refine ⟨7504808075339915060606533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10006410767119886747475377 7504808075339915060606533)
                ·
                  refine ⟨1407151514126234073863725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7504808075339915060606533 1407151514126234073863725)
                  ·
                    refine ⟨527681817797337777698897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1407151514126234073863725 527681817797337777698897)
                    ·
                      rfl

theorem cell22_1541485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_1541485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541485 prefixEnd_1541485 := by exact prefixLift 1541485
  have htrace : WordTrace (prefixWord ++ tailWord_1541485) baseStart_1541485 baseEnd_1541485 := by
    simpa [prefixWord, tailWord_1541485, baseEnd_1541485] using wordTrace_append hprefix tailTrace_1541485
  have hstable : (prefixWord ++ tailWord_1541485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541485).length < 2 ^ (prefixWord ++ tailWord_1541485).sum := by decide
  have hdescent : baseEnd_1541485 < baseStart_1541485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541530 : List Nat := [3, 1, 1, 4, 1, 1, 2, 1, 5, 3]
def baseStart_1541530 : Nat := 118140960795 + 1541530 * 2 ^ 59
def prefixEnd_1541530 : Nat := 4983230072969 + 3 ^ 40 * 1541530 * 2
def baseEnd_1541530 : Nat := 527697222216972660323759

theorem tailTrace_1541530 : CollatzResearch.WordTrace tailWord_1541530 prefixEnd_1541530 527697222216972660323759 := by
  unfold tailWord_1541530
  simp only [CollatzResearch.WordTrace]
  refine ⟨14056054526326889302231511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37482812070205038139284029 14056054526326889302231511)
  ·
    refine ⟨21084081789490333953347267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14056054526326889302231511 21084081789490333953347267)
    ·
      refine ⟨31626122684235500930020901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21084081789490333953347267 31626122684235500930020901)
      ·
        refine ⟨5929898003294156424378919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31626122684235500930020901 5929898003294156424378919)
        ·
          refine ⟨8894847004941234636568379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5929898003294156424378919 8894847004941234636568379)
          ·
            refine ⟨13342270507411851954852569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8894847004941234636568379 13342270507411851954852569)
            ·
              refine ⟨10006702880558888966139427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13342270507411851954852569 10006702880558888966139427)
              ·
                refine ⟨15010054320838333449209141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10006702880558888966139427 15010054320838333449209141)
                ·
                  refine ⟨1407192592578593760863357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15010054320838333449209141 1407192592578593760863357)
                  ·
                    refine ⟨527697222216972660323759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1407192592578593760863357 527697222216972660323759)
                    ·
                      rfl

theorem cell22_1541530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 5, 3].length) (baseStart_1541530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541530 prefixEnd_1541530 := by exact prefixLift 1541530
  have htrace : WordTrace (prefixWord ++ tailWord_1541530) baseStart_1541530 baseEnd_1541530 := by
    simpa [prefixWord, tailWord_1541530, baseEnd_1541530] using wordTrace_append hprefix tailTrace_1541530
  have hstable : (prefixWord ++ tailWord_1541530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541530).length < 2 ^ (prefixWord ++ tailWord_1541530).sum := by decide
  have hdescent : baseEnd_1541530 < baseStart_1541530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541534 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_1541534 : Nat := 118140960795 + 1541534 * 2 ^ 59
def prefixEnd_1541534 : Nat := 4983230072969 + 3 ^ 40 * 1541534 * 2
def baseEnd_1541534 : Nat := 527698591498717983223747

theorem tailTrace_1541534 : CollatzResearch.WordTrace tailWord_1541534 prefixEnd_1541534 527698591498717983223747 := by
  unfold tailWord_1541534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7028045499661633236508957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37482909331528710594714437 7028045499661633236508957)
  ·
    refine ⟨2635517062373112463690859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7028045499661633236508957 2635517062373112463690859)
    ·
      refine ⟨3953275593559668695536289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2635517062373112463690859 3953275593559668695536289)
      ·
        refine ⟨2964956695169751521652217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3953275593559668695536289 2964956695169751521652217)
        ·
          refine ⟨2223717521377313641239163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2964956695169751521652217 2223717521377313641239163)
          ·
            refine ⟨3335576282065970461858745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2223717521377313641239163 3335576282065970461858745)
            ·
              refine ⟨2501682211549477846394059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3335576282065970461858745 2501682211549477846394059)
              ·
                refine ⟨3752523317324216769591089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2501682211549477846394059 3752523317324216769591089)
                ·
                  refine ⟨2814392487993162577193317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3752523317324216769591089 2814392487993162577193317)
                  ·
                    refine ⟨527698591498717983223747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2814392487993162577193317 527698591498717983223747)
                    ·
                      rfl

theorem cell22_1541534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_1541534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541534 prefixEnd_1541534 := by exact prefixLift 1541534
  have htrace : WordTrace (prefixWord ++ tailWord_1541534) baseStart_1541534 baseEnd_1541534 := by
    simpa [prefixWord, tailWord_1541534, baseEnd_1541534] using wordTrace_append hprefix tailTrace_1541534
  have hstable : (prefixWord ++ tailWord_1541534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541534).length < 2 ^ (prefixWord ++ tailWord_1541534).sum := by decide
  have hdescent : baseEnd_1541534 < baseStart_1541534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541607 : List Nat := [1, 1, 5, 2, 1, 3, 1, 3, 1, 4]
def baseStart_1541607 : Nat := 118140960795 + 1541607 * 2 ^ 59
def prefixEnd_1541607 : Nat := 4983230072969 + 3 ^ 40 * 1541607 * 2
def baseEnd_1541607 : Nat := 527723580890570126148523

theorem tailTrace_1541607 : CollatzResearch.WordTrace tailWord_1541607 prefixEnd_1541607 527723580890570126148523 := by
  unfold tailWord_1541607
  simp only [CollatzResearch.WordTrace]
  refine ⟨56227026526028599359479075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37484684350685732906319383 56227026526028599359479075)
  ·
    refine ⟨84340539789042899039218613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56227026526028599359479075 84340539789042899039218613)
    ·
      refine ⟨7906925605222771784926745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84340539789042899039218613 7906925605222771784926745)
      ·
        refine ⟨5930194203917078838695059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7906925605222771784926745 5930194203917078838695059)
        ·
          refine ⟨8895291305875618258042589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5930194203917078838695059 8895291305875618258042589)
          ·
            refine ⟨3335734239703356846765971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8895291305875618258042589 3335734239703356846765971)
            ·
              refine ⟨5003601359555035270148957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3335734239703356846765971 5003601359555035270148957)
              ·
                refine ⟨1876350509833138226305859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5003601359555035270148957 1876350509833138226305859)
                ·
                  refine ⟨2814525764749707339458789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876350509833138226305859 2814525764749707339458789)
                  ·
                    refine ⟨527723580890570126148523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2814525764749707339458789 527723580890570126148523)
                    ·
                      rfl

theorem cell22_1541607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_1541607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541607 prefixEnd_1541607 := by exact prefixLift 1541607
  have htrace : WordTrace (prefixWord ++ tailWord_1541607) baseStart_1541607 baseEnd_1541607 := by
    simpa [prefixWord, tailWord_1541607, baseEnd_1541607] using wordTrace_append hprefix tailTrace_1541607
  have hstable : (prefixWord ++ tailWord_1541607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541607).length < 2 ^ (prefixWord ++ tailWord_1541607).sum := by decide
  have hdescent : baseEnd_1541607 < baseStart_1541607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541622 : List Nat := [5, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_1541622 : Nat := 118140960795 + 1541622 * 2 ^ 59
def prefixEnd_1541622 : Nat := 4983230072969 + 3 ^ 40 * 1541622 * 2
def baseEnd_1541622 : Nat := 175909571899038362341159

theorem tailTrace_1541622 : CollatzResearch.WordTrace tailWord_1541622 prefixEnd_1541622 175909571899038362341159 := by
  unfold tailWord_1541622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3514223351310891057579695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37485049080649504614183413 3514223351310891057579695)
  ·
    refine ⟨5271335026966336586369543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3514223351310891057579695 5271335026966336586369543)
    ·
      refine ⟨7907002540449504879554315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5271335026966336586369543 7907002540449504879554315)
      ·
        refine ⟨11860503810674257319331473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7907002540449504879554315 11860503810674257319331473)
        ·
          refine ⟨8895377858005692989498605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11860503810674257319331473 8895377858005692989498605)
          ·
            refine ⟨3335766696752134871061977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8895377858005692989498605 3335766696752134871061977)
            ·
              refine ⟨2501825022564101153296483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3335766696752134871061977 2501825022564101153296483)
              ·
                refine ⟨3752737533846151729944725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2501825022564101153296483 3752737533846151729944725)
                ·
                  refine ⟨175909571899038362341159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3752737533846151729944725 175909571899038362341159)
                  ·
                    rfl

theorem cell22_1541622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_1541622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541622 prefixEnd_1541622 := by exact prefixLift 1541622
  have htrace : WordTrace (prefixWord ++ tailWord_1541622) baseStart_1541622 baseEnd_1541622 := by
    simpa [prefixWord, tailWord_1541622, baseEnd_1541622] using wordTrace_append hprefix tailTrace_1541622
  have hstable : (prefixWord ++ tailWord_1541622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541622).length < 2 ^ (prefixWord ++ tailWord_1541622).sum := by decide
  have hdescent : baseEnd_1541622 < baseStart_1541622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541656 : List Nat := [2, 1, 2, 3, 5, 1, 1, 3, 4]
def baseStart_1541656 : Nat := 118140960795 + 1541656 * 2 ^ 59
def prefixEnd_1541656 : Nat := 4983230072969 + 3 ^ 40 * 1541656 * 2
def baseEnd_1541656 : Nat := 175913451530650110557791

theorem tailTrace_1541656 : CollatzResearch.WordTrace tailWord_1541656 prefixEnd_1541656 175913451530650110557791 := by
  unfold tailWord_1541656
  simp only [CollatzResearch.WordTrace]
  refine ⟨28114406851425540364006411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37485875801900720485341881 28114406851425540364006411)
  ·
    refine ⟨42171610277138310546009617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28114406851425540364006411 42171610277138310546009617)
    ·
      refine ⟨31628707707853732909507213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42171610277138310546009617 31628707707853732909507213)
      ·
        refine ⟨11860765390445149841065205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31628707707853732909507213 11860765390445149841065205)
        ·
          refine ⟨1111946755354232797599863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11860765390445149841065205 1111946755354232797599863)
          ·
            refine ⟨1667920133031349196399795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111946755354232797599863 1667920133031349196399795)
            ·
              refine ⟨2501880199547023794599693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1667920133031349196399795 2501880199547023794599693)
              ·
                refine ⟨938205074830133922974885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2501880199547023794599693 938205074830133922974885)
                ·
                  refine ⟨175913451530650110557791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 938205074830133922974885 175913451530650110557791)
                  ·
                    rfl

theorem cell22_1541656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 3, 4].length) (baseStart_1541656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541656 prefixEnd_1541656 := by exact prefixLift 1541656
  have htrace : WordTrace (prefixWord ++ tailWord_1541656) baseStart_1541656 baseEnd_1541656 := by
    simpa [prefixWord, tailWord_1541656, baseEnd_1541656] using wordTrace_append hprefix tailTrace_1541656
  have hstable : (prefixWord ++ tailWord_1541656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541656).length < 2 ^ (prefixWord ++ tailWord_1541656).sum := by decide
  have hdescent : baseEnd_1541656 < baseStart_1541656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541667 : List Nat := [1, 1, 1, 4, 6, 1, 8]
def baseStart_1541667 : Nat := 118140960795 + 1541667 * 2 ^ 59
def prefixEnd_1541667 : Nat := 4983230072969 + 3 ^ 40 * 1541667 * 2
def baseEnd_1541667 : Nat := 19546078522842591468457

theorem tailTrace_1541667 : CollatzResearch.WordTrace tailWord_1541667 prefixEnd_1541667 19546078522842591468457 := by
  unfold tailWord_1541667
  simp only [CollatzResearch.WordTrace]
  refine ⟨56229214905811229606663255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37486143270540819737775503 56229214905811229606663255)
  ·
    refine ⟨84343822358716844409994883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56229214905811229606663255 84343822358716844409994883)
    ·
      refine ⟨126515733538075266614992325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84343822358716844409994883 126515733538075266614992325)
      ·
        refine ⟨23721700038389112490311061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126515733538075266614992325 23721700038389112490311061)
        ·
          refine ⟨1111954689299489647983331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23721700038389112490311061 1111954689299489647983331)
          ·
            refine ⟨1667932033949234471974997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1111954689299489647983331 1667932033949234471974997)
            ·
              refine ⟨19546078522842591468457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1667932033949234471974997 19546078522842591468457)
              ·
                rfl

theorem cell22_1541667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 8].length) (baseStart_1541667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541667 prefixEnd_1541667 := by exact prefixLift 1541667
  have htrace : WordTrace (prefixWord ++ tailWord_1541667) baseStart_1541667 baseEnd_1541667 := by
    simpa [prefixWord, tailWord_1541667, baseEnd_1541667] using wordTrace_append hprefix tailTrace_1541667
  have hstable : (prefixWord ++ tailWord_1541667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541667).length < 2 ^ (prefixWord ++ tailWord_1541667).sum := by decide
  have hdescent : baseEnd_1541667 < baseStart_1541667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541710 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_1541710 : Nat := 118140960795 + 1541710 * 2 ^ 59
def prefixEnd_1541710 : Nat := 4983230072969 + 3 ^ 40 * 1541710 * 2
def baseEnd_1541710 : Nat := 527758839895512190823207

theorem tailTrace_1541710 : CollatzResearch.WordTrace tailWord_1541710 prefixEnd_1541710 527758839895512190823207 := by
  unfold tailWord_1541710
  simp only [CollatzResearch.WordTrace]
  refine ⟨7028847905581930993809823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37487188829770298633652389 7028847905581930993809823)
  ·
    refine ⟨10543271858372896490714735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7028847905581930993809823 10543271858372896490714735)
    ·
      refine ⟨15814907787559344736072103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10543271858372896490714735 15814907787559344736072103)
      ·
        refine ⟨23722361681339017104108155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15814907787559344736072103 23722361681339017104108155)
        ·
          refine ⟨35583542522008525656162233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23722361681339017104108155 35583542522008525656162233)
          ·
            refine ⟨26687656891506394242121675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35583542522008525656162233 26687656891506394242121675)
            ·
              refine ⟨40031485337259591363182513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26687656891506394242121675 40031485337259591363182513)
              ·
                refine ⟨30023614002944693522386885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40031485337259591363182513 30023614002944693522386885)
                ·
                  refine ⟨5629427625552130035447541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30023614002944693522386885 5629427625552130035447541)
                  ·
                    refine ⟨527758839895512190823207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5629427625552130035447541 527758839895512190823207)
                    ·
                      rfl

theorem cell22_1541710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_1541710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541710 prefixEnd_1541710 := by exact prefixLift 1541710
  have htrace : WordTrace (prefixWord ++ tailWord_1541710) baseStart_1541710 baseEnd_1541710 := by
    simpa [prefixWord, tailWord_1541710, baseEnd_1541710] using wordTrace_append hprefix tailTrace_1541710
  have hstable : (prefixWord ++ tailWord_1541710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541710).length < 2 ^ (prefixWord ++ tailWord_1541710).sum := by decide
  have hdescent : baseEnd_1541710 < baseStart_1541710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541733 : List Nat := [1, 3, 1, 3, 3, 3, 2, 2, 1, 3]
def baseStart_1541733 : Nat := 118140960795 + 1541733 * 2 ^ 59
def prefixEnd_1541733 : Nat := 4983230072969 + 3 ^ 40 * 1541733 * 2
def baseEnd_1541733 : Nat := 527766713265547797498137

theorem tailTrace_1541733 : CollatzResearch.WordTrace tailWord_1541733 prefixEnd_1541733 527766713265547797498137 := by
  unfold tailWord_1541733
  simp only [CollatzResearch.WordTrace]
  refine ⟨56231622123572122878565853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37487748082381415252377235 56231622123572122878565853)
  ·
    refine ⟨21086858296339546079462195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56231622123572122878565853 21086858296339546079462195)
    ·
      refine ⟨31630287444509319119193293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21086858296339546079462195 31630287444509319119193293)
      ·
        refine ⟨11861357791690994669697485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31630287444509319119193293 11861357791690994669697485)
        ·
          refine ⟨4448009171884123001136557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11861357791690994669697485 4448009171884123001136557)
          ·
            refine ⟨1668003439456546125426209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4448009171884123001136557 1668003439456546125426209)
            ·
              refine ⟨1251002579592409594069657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1668003439456546125426209 1251002579592409594069657)
              ·
                refine ⟨938251934694307195552243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1251002579592409594069657 938251934694307195552243)
                ·
                  refine ⟨1407377902041460793328365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 938251934694307195552243 1407377902041460793328365)
                  ·
                    refine ⟨527766713265547797498137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1407377902041460793328365 527766713265547797498137)
                    ·
                      rfl

theorem cell22_1541733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_1541733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541733 prefixEnd_1541733 := by exact prefixLift 1541733
  have htrace : WordTrace (prefixWord ++ tailWord_1541733) baseStart_1541733 baseEnd_1541733 := by
    simpa [prefixWord, tailWord_1541733, baseEnd_1541733] using wordTrace_append hprefix tailTrace_1541733
  have hstable : (prefixWord ++ tailWord_1541733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541733).length < 2 ^ (prefixWord ++ tailWord_1541733).sum := by decide
  have hdescent : baseEnd_1541733 < baseStart_1541733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541740 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 6]
def baseStart_1541740 : Nat := 118140960795 + 1541740 * 2 ^ 59
def prefixEnd_1541740 : Nat := 4983230072969 + 3 ^ 40 * 1541740 * 2
def baseEnd_1541740 : Nat := 175923036502867370857705

theorem tailTrace_1541740 : CollatzResearch.WordTrace tailWord_1541740 prefixEnd_1541740 175923036502867370857705 := by
  unfold tailWord_1541740
  simp only [CollatzResearch.WordTrace]
  refine ⟨28115938717273381537035337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37487918289697842049380449 28115938717273381537035337)
  ·
    refine ⟨21086954037955036152776503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28115938717273381537035337 21086954037955036152776503)
    ·
      refine ⟨31630431056932554229164755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21086954037955036152776503 31630431056932554229164755)
      ·
        refine ⟨47445646585398831343747133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31630431056932554229164755 47445646585398831343747133)
        ·
          refine ⟨17792117469524561753905175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 47445646585398831343747133 17792117469524561753905175)
          ·
            refine ⟨26688176204286842630857763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17792117469524561753905175 26688176204286842630857763)
            ·
              refine ⟨40032264306430263946286645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26688176204286842630857763 40032264306430263946286645)
              ·
                refine ⟨3753024778727837244964373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40032264306430263946286645 3753024778727837244964373)
                ·
                  refine ⟨175923036502867370857705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3753024778727837244964373 175923036502867370857705)
                  ·
                    rfl

theorem cell22_1541740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 6].length) (baseStart_1541740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541740 prefixEnd_1541740 := by exact prefixLift 1541740
  have htrace : WordTrace (prefixWord ++ tailWord_1541740) baseStart_1541740 baseEnd_1541740 := by
    simpa [prefixWord, tailWord_1541740, baseEnd_1541740] using wordTrace_append hprefix tailTrace_1541740
  have hstable : (prefixWord ++ tailWord_1541740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541740).length < 2 ^ (prefixWord ++ tailWord_1541740).sum := by decide
  have hdescent : baseEnd_1541740 < baseStart_1541740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541757 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 6]
def baseStart_1541757 : Nat := 118140960795 + 1541757 * 2 ^ 59
def prefixEnd_1541757 : Nat := 4983230072969 + 3 ^ 40 * 1541757 * 2
def baseEnd_1541757 : Nat := 175924976318673244966021

theorem tailTrace_1541757 : CollatzResearch.WordTrace tailWord_1541757 prefixEnd_1541757 175924976318673244966021 := by
  unfold tailWord_1541757
  simp only [CollatzResearch.WordTrace]
  refine ⟨56232497475485174977439525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37488331650323449984959683 56232497475485174977439525)
  ·
    refine ⟨10543593276653470308269911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56232497475485174977439525 10543593276653470308269911)
    ·
      refine ⟨15815389914980205462404867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10543593276653470308269911 15815389914980205462404867)
      ·
        refine ⟨23723084872470308193607301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15815389914980205462404867 23723084872470308193607301)
        ·
          refine ⟨4448078413588182786301369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23723084872470308193607301 4448078413588182786301369)
          ·
            refine ⟨3336058810191137089726027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4448078413588182786301369 3336058810191137089726027)
            ·
              refine ⟨5004088215286705634589041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336058810191137089726027 5004088215286705634589041)
              ·
                refine ⟨3753066161465029225941781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5004088215286705634589041 3753066161465029225941781)
                ·
                  refine ⟨175924976318673244966021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3753066161465029225941781 175924976318673244966021)
                  ·
                    rfl

theorem cell22_1541757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_1541757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541757 prefixEnd_1541757 := by exact prefixLift 1541757
  have htrace : WordTrace (prefixWord ++ tailWord_1541757) baseStart_1541757 baseEnd_1541757 := by
    simpa [prefixWord, tailWord_1541757, baseEnd_1541757] using wordTrace_append hprefix tailTrace_1541757
  have hstable : (prefixWord ++ tailWord_1541757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541757).length < 2 ^ (prefixWord ++ tailWord_1541757).sum := by decide
  have hdescent : baseEnd_1541757 < baseStart_1541757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541772 : List Nat := [2, 2, 1, 2, 1, 1, 4, 2, 4, 3]
def baseStart_1541772 : Nat := 118140960795 + 1541772 * 2 ^ 59
def prefixEnd_1541772 : Nat := 4983230072969 + 3 ^ 40 * 1541772 * 2
def baseEnd_1541772 : Nat := 527780063762564695773017

theorem tailTrace_1541772 : CollatzResearch.WordTrace tailWord_1541772 prefixEnd_1541772 527780063762564695773017 := by
  unfold tailWord_1541772
  simp only [CollatzResearch.WordTrace]
  refine ⟨28116522285215416269617785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37488696380287221692823713 28116522285215416269617785)
  ·
    refine ⟨21087391713911562202213339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28116522285215416269617785 21087391713911562202213339)
    ·
      refine ⟨31631087570867343303320009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21087391713911562202213339 31631087570867343303320009)
      ·
        refine ⟨23723315678150507477490007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31631087570867343303320009 23723315678150507477490007)
        ·
          refine ⟨35584973517225761216235011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23723315678150507477490007 35584973517225761216235011)
          ·
            refine ⟨53377460275838641824352517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35584973517225761216235011 53377460275838641824352517)
            ·
              refine ⟨10008273801719745342066097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53377460275838641824352517 10008273801719745342066097)
              ·
                refine ⟨7506205351289809006549573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10008273801719745342066097 7506205351289809006549573)
                ·
                  refine ⟨1407413503366839188728045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7506205351289809006549573 1407413503366839188728045)
                  ·
                    refine ⟨527780063762564695773017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1407413503366839188728045 527780063762564695773017)
                    ·
                      rfl

theorem cell22_1541772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_1541772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541772 prefixEnd_1541772 := by exact prefixLift 1541772
  have htrace : WordTrace (prefixWord ++ tailWord_1541772) baseStart_1541772 baseEnd_1541772 := by
    simpa [prefixWord, tailWord_1541772, baseEnd_1541772] using wordTrace_append hprefix tailTrace_1541772
  have hstable : (prefixWord ++ tailWord_1541772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541772).length < 2 ^ (prefixWord ++ tailWord_1541772).sum := by decide
  have hdescent : baseEnd_1541772 < baseStart_1541772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541774 : List Nat := [4, 1, 1, 3, 1, 2, 1, 5, 4]
def baseStart_1541774 : Nat := 118140960795 + 1541774 * 2 ^ 59
def prefixEnd_1541774 : Nat := 4983230072969 + 3 ^ 40 * 1541774 * 2
def baseEnd_1541774 : Nat := 175926916134479119074337

theorem tailTrace_1541774 : CollatzResearch.WordTrace tailWord_1541774 prefixEnd_1541774 175926916134479119074337 := by
  unfold tailWord_1541774
  simp only [CollatzResearch.WordTrace]
  refine ⟨7029139689552948360101047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37488745010949057920538917 7029139689552948360101047)
  ·
    refine ⟨10543709534329422540151571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7029139689552948360101047 10543709534329422540151571)
    ·
      refine ⟨15815564301494133810227357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10543709534329422540151571 15815564301494133810227357)
      ·
        refine ⟨5930836613060300178835259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15815564301494133810227357 5930836613060300178835259)
        ·
          refine ⟨8896254919590450268252889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5930836613060300178835259 8896254919590450268252889)
          ·
            refine ⟨6672191189692837701189667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8896254919590450268252889 6672191189692837701189667)
            ·
              refine ⟨10008286784539256551784501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6672191189692837701189667 10008286784539256551784501)
              ·
                refine ⟨938276886050555301729797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10008286784539256551784501 938276886050555301729797)
                ·
                  refine ⟨175926916134479119074337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 938276886050555301729797 175926916134479119074337)
                  ·
                    rfl

theorem cell22_1541774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_1541774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541774 prefixEnd_1541774 := by exact prefixLift 1541774
  have htrace : WordTrace (prefixWord ++ tailWord_1541774) baseStart_1541774 baseEnd_1541774 := by
    simpa [prefixWord, tailWord_1541774, baseEnd_1541774] using wordTrace_append hprefix tailTrace_1541774
  have hstable : (prefixWord ++ tailWord_1541774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541774).length < 2 ^ (prefixWord ++ tailWord_1541774).sum := by decide
  have hdescent : baseEnd_1541774 < baseStart_1541774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541847 : List Nat := [1, 1, 3, 2, 1, 3, 2, 4, 5]
def baseStart_1541847 : Nat := 118140960795 + 1541847 * 2 ^ 59
def prefixEnd_1541847 : Nat := 4983230072969 + 3 ^ 40 * 1541847 * 2
def baseEnd_1541847 : Nat := 175935245931763166715929

theorem tailTrace_1541847 : CollatzResearch.WordTrace tailWord_1541847 prefixEnd_1541847 175935245931763166715929 := by
  unfold tailWord_1541847
  simp only [CollatzResearch.WordTrace]
  refine ⟨56235780045159120348215795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37490520030106080232143863 56235780045159120348215795)
  ·
    refine ⟨84353670067738680522323693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56235780045159120348215795 84353670067738680522323693)
    ·
      refine ⟨31632626275402005195871385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84353670067738680522323693 31632626275402005195871385)
      ·
        refine ⟨23724469706551503896903539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31632626275402005195871385 23724469706551503896903539)
        ·
          refine ⟨35586704559827255845355309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23724469706551503896903539 35586704559827255845355309)
          ·
            refine ⟨13345014209935220942008241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35586704559827255845355309 13345014209935220942008241)
            ·
              refine ⟨10008760657451415706506181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13345014209935220942008241 10008760657451415706506181)
              ·
                refine ⟨1876642623272140444969909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10008760657451415706506181 1876642623272140444969909)
                ·
                  refine ⟨175935245931763166715929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1876642623272140444969909 175935245931763166715929)
                  ·
                    rfl

theorem cell22_1541847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 4, 5].length) (baseStart_1541847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541847 prefixEnd_1541847 := by exact prefixLift 1541847
  have htrace : WordTrace (prefixWord ++ tailWord_1541847) baseStart_1541847 baseEnd_1541847 := by
    simpa [prefixWord, tailWord_1541847, baseEnd_1541847] using wordTrace_append hprefix tailTrace_1541847
  have hstable : (prefixWord ++ tailWord_1541847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541847).length < 2 ^ (prefixWord ++ tailWord_1541847).sum := by decide
  have hdescent : baseEnd_1541847 < baseStart_1541847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541864 : List Nat := [2, 1, 4, 1, 3, 2, 1, 3, 5]
def baseStart_1541864 : Nat := 118140960795 + 1541864 * 2 ^ 59
def prefixEnd_1541864 : Nat := 4983230072969 + 3 ^ 40 * 1541864 * 2
def baseEnd_1541864 : Nat := 175937185747569040824245

theorem tailTrace_1541864 : CollatzResearch.WordTrace tailWord_1541864 prefixEnd_1541864 175937185747569040824245 := by
  unfold tailWord_1541864
  simp only [CollatzResearch.WordTrace]
  refine ⟨28118200043048766125792323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37490933390731688167723097 28118200043048766125792323)
  ·
    refine ⟨42177300064573149188688485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28118200043048766125792323 42177300064573149188688485)
    ·
      refine ⟨7908243762107465472879091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42177300064573149188688485 7908243762107465472879091)
      ·
        refine ⟨11862365643161198209318637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7908243762107465472879091 11862365643161198209318637)
        ·
          refine ⟨4448387116185449328494489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11862365643161198209318637 4448387116185449328494489)
          ·
            refine ⟨3336290337139086996370867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4448387116185449328494489 3336290337139086996370867)
            ·
              refine ⟨5004435505708630494556301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336290337139086996370867 5004435505708630494556301)
              ·
                refine ⟨1876663314640736435458613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5004435505708630494556301 1876663314640736435458613)
                ·
                  refine ⟨175937185747569040824245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1876663314640736435458613 175937185747569040824245)
                  ·
                    rfl

theorem cell22_1541864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 5].length) (baseStart_1541864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541864 prefixEnd_1541864 := by exact prefixLift 1541864
  have htrace : WordTrace (prefixWord ++ tailWord_1541864) baseStart_1541864 baseEnd_1541864 := by
    simpa [prefixWord, tailWord_1541864, baseEnd_1541864] using wordTrace_append hprefix tailTrace_1541864
  have hstable : (prefixWord ++ tailWord_1541864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541864).length < 2 ^ (prefixWord ++ tailWord_1541864).sum := by decide
  have hdescent : baseEnd_1541864 < baseStart_1541864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541924 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_1541924 : Nat := 118140960795 + 1541924 * 2 ^ 59
def prefixEnd_1541924 : Nat := 4983230072969 + 3 ^ 40 * 1541924 * 2
def baseEnd_1541924 : Nat := 527832096468886965972551

theorem tailTrace_1541924 : CollatzResearch.WordTrace tailWord_1541924 prefixEnd_1541924 527832096468886965972551 := by
  unfold tailWord_1541924
  simp only [CollatzResearch.WordTrace]
  refine ⟨28119294232940081249384413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37492392310586774999179217 28119294232940081249384413)
  ·
    refine ⟨10544735337352530468519155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28119294232940081249384413 10544735337352530468519155)
    ·
      refine ⟨15817103006028795702778733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10544735337352530468519155 15817103006028795702778733)
      ·
        refine ⟨5931413627260798388542025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15817103006028795702778733 5931413627260798388542025)
        ·
          refine ⟨4448560220445598791406519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5931413627260798388542025 4448560220445598791406519)
          ·
            refine ⟨6672840330668398187109779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4448560220445598791406519 6672840330668398187109779)
            ·
              refine ⟨10009260496002597280664669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6672840330668398187109779 10009260496002597280664669)
              ·
                refine ⟨3753472686000973980249251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10009260496002597280664669 3753472686000973980249251)
                ·
                  refine ⟨5630209029001460970373877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3753472686000973980249251 5630209029001460970373877)
                  ·
                    refine ⟨527832096468886965972551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5630209029001460970373877 527832096468886965972551)
                    ·
                      rfl

theorem cell22_1541924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_1541924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541924 prefixEnd_1541924 := by exact prefixLift 1541924
  have htrace : WordTrace (prefixWord ++ tailWord_1541924) baseStart_1541924 baseEnd_1541924 := by
    simpa [prefixWord, tailWord_1541924, baseEnd_1541924] using wordTrace_append hprefix tailTrace_1541924
  have hstable : (prefixWord ++ tailWord_1541924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541924).length < 2 ^ (prefixWord ++ tailWord_1541924).sum := by decide
  have hdescent : baseEnd_1541924 < baseStart_1541924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541939 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 1, 6]
def baseStart_1541939 : Nat := 118140960795 + 1541939 * 2 ^ 59
def prefixEnd_1541939 : Nat := 4983230072969 + 3 ^ 40 * 1541939 * 2
def baseEnd_1541939 : Nat := 527837231275431926847505

theorem tailTrace_1541939 : CollatzResearch.WordTrace tailWord_1541939 prefixEnd_1541939 527837231275431926847505 := by
  unfold tailWord_1541939
  simp only [CollatzResearch.WordTrace]
  refine ⟨56239135560825820060564871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37492757040550546707043247 56239135560825820060564871)
  ·
    refine ⟨84358703341238730090847307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56239135560825820060564871 84358703341238730090847307)
    ·
      refine ⟨126538055011858095136270961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84358703341238730090847307 126538055011858095136270961)
      ·
        refine ⟨94903541258893571352203221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 126538055011858095136270961 94903541258893571352203221)
        ·
          refine ⟨2224301748255318078567263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 94903541258893571352203221 2224301748255318078567263)
          ·
            refine ⟨3336452622382977117850895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2224301748255318078567263 3336452622382977117850895)
            ·
              refine ⟨5004678933574465676776343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336452622382977117850895 5004678933574465676776343)
              ·
                refine ⟨7507018400361698515164515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5004678933574465676776343 7507018400361698515164515)
                ·
                  refine ⟨11260527600542547772746773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7507018400361698515164515 11260527600542547772746773)
                  ·
                    refine ⟨527837231275431926847505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11260527600542547772746773 527837231275431926847505)
                    ·
                      rfl

theorem cell22_1541939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 1, 6].length) (baseStart_1541939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541939 prefixEnd_1541939 := by exact prefixLift 1541939
  have htrace : WordTrace (prefixWord ++ tailWord_1541939) baseStart_1541939 baseEnd_1541939 := by
    simpa [prefixWord, tailWord_1541939, baseEnd_1541939] using wordTrace_append hprefix tailTrace_1541939
  have hstable : (prefixWord ++ tailWord_1541939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541939).length < 2 ^ (prefixWord ++ tailWord_1541939).sum := by decide
  have hdescent : baseEnd_1541939 < baseStart_1541939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541945 : List Nat := [1, 2, 1, 7, 1, 2, 2, 1, 1, 4]
def baseStart_1541945 : Nat := 118140960795 + 1541945 * 2 ^ 59
def prefixEnd_1541945 : Nat := 4983230072969 + 3 ^ 40 * 1541945 * 2
def baseEnd_1541945 : Nat := 527839285198049911197487

theorem tailTrace_1541945 : CollatzResearch.WordTrace tailWord_1541945 prefixEnd_1541945 527839285198049911197487 := by
  unfold tailWord_1541945
  simp only [CollatzResearch.WordTrace]
  refine ⟨56239354398804083085283289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37492902932536055390188859 56239354398804083085283289)
  ·
    refine ⟨42179515799103062313962467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56239354398804083085283289 42179515799103062313962467)
    ·
      refine ⟨63269273698654593470943701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42179515799103062313962467 63269273698654593470943701)
      ·
        refine ⟨1482873602312217034475243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 63269273698654593470943701 1482873602312217034475243)
        ·
          refine ⟨2224310403468325551712865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1482873602312217034475243 2224310403468325551712865)
          ·
            refine ⟨1668232802601244163784649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2224310403468325551712865 1668232802601244163784649)
            ·
              refine ⟨1251174601950933122838487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1668232802601244163784649 1251174601950933122838487)
              ·
                refine ⟨1876761902926399684257731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251174601950933122838487 1876761902926399684257731)
                ·
                  refine ⟨2815142854389599526386597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876761902926399684257731 2815142854389599526386597)
                  ·
                    refine ⟨527839285198049911197487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2815142854389599526386597 527839285198049911197487)
                    ·
                      rfl

theorem cell22_1541945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 1, 4].length) (baseStart_1541945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541945 prefixEnd_1541945 := by exact prefixLift 1541945
  have htrace : WordTrace (prefixWord ++ tailWord_1541945) baseStart_1541945 baseEnd_1541945 := by
    simpa [prefixWord, tailWord_1541945, baseEnd_1541945] using wordTrace_append hprefix tailTrace_1541945
  have hstable : (prefixWord ++ tailWord_1541945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541945).length < 2 ^ (prefixWord ++ tailWord_1541945).sum := by decide
  have hdescent : baseEnd_1541945 < baseStart_1541945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1541988 : List Nat := [2, 3, 1, 1, 6, 1, 2, 6]
def baseStart_1541988 : Nat := 118140960795 + 1541988 * 2 ^ 59
def prefixEnd_1541988 : Nat := 4983230072969 + 3 ^ 40 * 1541988 * 2
def baseEnd_1541988 : Nat := 58650444997423570263595

theorem tailTrace_1541988 : CollatzResearch.WordTrace tailWord_1541988 prefixEnd_1541988 58650444997423570263595 := by
  unfold tailWord_1541988
  simp only [CollatzResearch.WordTrace]
  refine ⟨28120461368824150714549309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37493948491765534286065745 28120461368824150714549309)
  ·
    refine ⟨10545173013309056517955991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28120461368824150714549309 10545173013309056517955991)
    ·
      refine ⟨15817759519963584776933987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10545173013309056517955991 15817759519963584776933987)
      ·
        refine ⟨23726639279945377165400981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15817759519963584776933987 23726639279945377165400981)
        ·
          refine ⟨1112186216247439554628171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23726639279945377165400981 1112186216247439554628171)
          ·
            refine ⟨1668279324371159331942257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112186216247439554628171 1668279324371159331942257)
            ·
              refine ⟨1251209493278369498956693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1668279324371159331942257 1251209493278369498956693)
              ·
                refine ⟨58650444997423570263595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1251209493278369498956693 58650444997423570263595)
                ·
                  rfl

theorem cell22_1541988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 6].length) (baseStart_1541988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1541988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1541988 prefixEnd_1541988 := by exact prefixLift 1541988
  have htrace : WordTrace (prefixWord ++ tailWord_1541988) baseStart_1541988 baseEnd_1541988 := by
    simpa [prefixWord, tailWord_1541988, baseEnd_1541988] using wordTrace_append hprefix tailTrace_1541988
  have hstable : (prefixWord ++ tailWord_1541988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1541988).length < 2 ^ (prefixWord ++ tailWord_1541988).sum := by decide
  have hdescent : baseEnd_1541988 < baseStart_1541988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1541988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542074 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 4, 4]
def baseStart_1542074 : Nat := 118140960795 + 1542074 * 2 ^ 59
def prefixEnd_1542074 : Nat := 4983230072969 + 3 ^ 40 * 1542074 * 2
def baseEnd_1542074 : Nat := 527883444534336574722091

theorem tailTrace_1542074 : CollatzResearch.WordTrace tailWord_1542074 prefixEnd_1542074 527883444534336574722091 := by
  unfold tailWord_1542074
  simp only [CollatzResearch.WordTrace]
  refine ⟨14061014853834184529182319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37496039610224492077819517 14061014853834184529182319)
  ·
    refine ⟨21091522280751276793773479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14061014853834184529182319 21091522280751276793773479)
    ·
      refine ⟨31637283421126915190660219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21091522280751276793773479 31637283421126915190660219)
      ·
        refine ⟨47455925131690372785990329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31637283421126915190660219 47455925131690372785990329)
        ·
          refine ⟨35591943848767779589492747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47455925131690372785990329 35591943848767779589492747)
          ·
            refine ⟨53387915773151669384239121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35591943848767779589492747 53387915773151669384239121)
            ·
              refine ⟨40040936829863752038179341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53387915773151669384239121 40040936829863752038179341)
              ·
                refine ⟨15015351311198907014317253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40040936829863752038179341 15015351311198907014317253)
                ·
                  refine ⟨2815378370849795065184485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15015351311198907014317253 2815378370849795065184485)
                  ·
                    refine ⟨527883444534336574722091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2815378370849795065184485 527883444534336574722091)
                    ·
                      rfl

theorem cell22_1542074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_1542074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542074 prefixEnd_1542074 := by exact prefixLift 1542074
  have htrace : WordTrace (prefixWord ++ tailWord_1542074) baseStart_1542074 baseEnd_1542074 := by
    simpa [prefixWord, tailWord_1542074, baseEnd_1542074] using wordTrace_append hprefix tailTrace_1542074
  have hstable : (prefixWord ++ tailWord_1542074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542074).length < 2 ^ (prefixWord ++ tailWord_1542074).sum := by decide
  have hdescent : baseEnd_1542074 < baseStart_1542074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542078 : List Nat := [4, 2, 1, 1, 1, 4, 1, 4, 4]
def baseStart_1542078 : Nat := 118140960795 + 1542078 * 2 ^ 59
def prefixEnd_1542078 : Nat := 4983230072969 + 3 ^ 40 * 1542078 * 2
def baseEnd_1542078 : Nat := 175961604605360632540693

theorem tailTrace_1542078 : CollatzResearch.WordTrace tailWord_1542078 prefixEnd_1542078 175961604605360632540693 := by
  unfold tailWord_1542078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7030525663415280849984361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37496136871548164533249925 7030525663415280849984361)
  ·
    refine ⟨5272894247561460637488271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7030525663415280849984361 5272894247561460637488271)
    ·
      refine ⟨7909341371342190956232407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5272894247561460637488271 7909341371342190956232407)
      ·
        refine ⟨11864012057013286434348611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7909341371342190956232407 11864012057013286434348611)
        ·
          refine ⟨17796018085519929651522917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11864012057013286434348611 17796018085519929651522917)
          ·
            refine ⟨3336753391034986809660547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17796018085519929651522917 3336753391034986809660547)
            ·
              refine ⟨5005130086552480214490821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3336753391034986809660547 5005130086552480214490821)
              ·
                refine ⟨938461891228590040217029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5005130086552480214490821 938461891228590040217029)
                ·
                  refine ⟨175961604605360632540693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 938461891228590040217029 175961604605360632540693)
                  ·
                    rfl

theorem cell22_1542078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_1542078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542078 prefixEnd_1542078 := by exact prefixLift 1542078
  have htrace : WordTrace (prefixWord ++ tailWord_1542078) baseStart_1542078 baseEnd_1542078 := by
    simpa [prefixWord, tailWord_1542078, baseEnd_1542078] using wordTrace_append hprefix tailTrace_1542078
  have hstable : (prefixWord ++ tailWord_1542078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542078).length < 2 ^ (prefixWord ++ tailWord_1542078).sum := by decide
  have hdescent : baseEnd_1542078 < baseStart_1542078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542114 : List Nat := [3, 3, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1542114 : Nat := 118140960795 + 1542114 * 2 ^ 59
def prefixEnd_1542114 : Nat := 4983230072969 + 3 ^ 40 * 1542114 * 2
def baseEnd_1542114 : Nat := 527897137351789803721969

theorem tailTrace_1542114 : CollatzResearch.WordTrace tailWord_1542114 prefixEnd_1542114 527897137351789803721969 := by
  unfold tailWord_1542114
  simp only [CollatzResearch.WordTrace]
  refine ⟨14061379583797956237046349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37497012223461216632123597 14061379583797956237046349)
  ·
    refine ⟨5273017343924233588892381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14061379583797956237046349 5273017343924233588892381)
    ·
      refine ⟨1977381503971587595834643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5273017343924233588892381 1977381503971587595834643)
      ·
        refine ⟨2966072255957381393751965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1977381503971587595834643 2966072255957381393751965)
        ·
          refine ⟨1112277095984018022656987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2966072255957381393751965 1112277095984018022656987)
          ·
            refine ⟨1668415643976027033985481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112277095984018022656987 1668415643976027033985481)
            ·
              refine ⟨1251311732982020275489111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1668415643976027033985481 1251311732982020275489111)
              ·
                refine ⟨1876967599473030413233667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1251311732982020275489111 1876967599473030413233667)
                ·
                  refine ⟨2815451399209545619850501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1876967599473030413233667 2815451399209545619850501)
                  ·
                    refine ⟨527897137351789803721969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2815451399209545619850501 527897137351789803721969)
                    ·
                      rfl

theorem cell22_1542114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1542114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542114 prefixEnd_1542114 := by exact prefixLift 1542114
  have htrace : WordTrace (prefixWord ++ tailWord_1542114) baseStart_1542114 baseEnd_1542114 := by
    simpa [prefixWord, tailWord_1542114, baseEnd_1542114] using wordTrace_append hprefix tailTrace_1542114
  have hstable : (prefixWord ++ tailWord_1542114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542114).length < 2 ^ (prefixWord ++ tailWord_1542114).sum := by decide
  have hdescent : baseEnd_1542114 < baseStart_1542114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542172 : List Nat := [2, 2, 3, 1, 3, 3, 1, 3, 1, 3]
def baseStart_1542172 : Nat := 118140960795 + 1542172 * 2 ^ 59
def prefixEnd_1542172 : Nat := 4983230072969 + 3 ^ 40 * 1542172 * 2
def baseEnd_1542172 : Nat := 527916991937096985771791

theorem tailTrace_1542172 : CollatzResearch.WordTrace tailWord_1542172 prefixEnd_1542172 527916991937096985771791 := by
  unfold tailWord_1542172
  simp only [CollatzResearch.WordTrace]
  refine ⟨28123816884490850426898385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37498422512654467235864513 28123816884490850426898385)
  ·
    refine ⟨21092862663368137820173789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28123816884490850426898385 21092862663368137820173789)
    ·
      refine ⟨7909823498763051682565171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21092862663368137820173789 7909823498763051682565171)
      ·
        refine ⟨11864735248144577523847757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7909823498763051682565171 11864735248144577523847757)
        ·
          refine ⟨4449275718054216571442909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11864735248144577523847757 4449275718054216571442909)
          ·
            refine ⟨1668478394270331214291091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4449275718054216571442909 1668478394270331214291091)
            ·
              refine ⟨2502717591405496821436637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668478394270331214291091 2502717591405496821436637)
              ·
                refine ⟨938519096777061308038739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2502717591405496821436637 938519096777061308038739)
                ·
                  refine ⟨1407778645165591962058109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 938519096777061308038739 1407778645165591962058109)
                  ·
                    refine ⟨527916991937096985771791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1407778645165591962058109 527916991937096985771791)
                    ·
                      rfl

theorem cell22_1542172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 1, 3].length) (baseStart_1542172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542172 prefixEnd_1542172 := by exact prefixLift 1542172
  have htrace : WordTrace (prefixWord ++ tailWord_1542172) baseStart_1542172 baseEnd_1542172 := by
    simpa [prefixWord, tailWord_1542172, baseEnd_1542172] using wordTrace_append hprefix tailTrace_1542172
  have hstable : (prefixWord ++ tailWord_1542172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542172).length < 2 ^ (prefixWord ++ tailWord_1542172).sum := by decide
  have hdescent : baseEnd_1542172 < baseStart_1542172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542198 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_1542198 : Nat := 118140960795 + 1542198 * 2 ^ 59
def prefixEnd_1542198 : Nat := 4983230072969 + 3 ^ 40 * 1542198 * 2
def baseEnd_1542198 : Nat := 527925892268441584621711

theorem tailTrace_1542198 : CollatzResearch.WordTrace tailWord_1542198 prefixEnd_1542198 527925892268441584621711 := by
  unfold tailWord_1542198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3515536379180469205890203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37499054711258338196162165 3515536379180469205890203)
  ·
    refine ⟨5273304568770703808835305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3515536379180469205890203 5273304568770703808835305)
    ·
      refine ⟨3954978426578027856626479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5273304568770703808835305 3954978426578027856626479)
      ·
        refine ⟨5932467639867041784939719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3954978426578027856626479 5932467639867041784939719)
        ·
          refine ⟨8898701459800562677409579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5932467639867041784939719 8898701459800562677409579)
          ·
            refine ⟨13348052189700844016114369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8898701459800562677409579 13348052189700844016114369)
            ·
              refine ⟨10011039142275633012085777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13348052189700844016114369 10011039142275633012085777)
              ·
                refine ⟨7508279356706724759064333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10011039142275633012085777 7508279356706724759064333)
                ·
                  refine ⟨2815604758765021784649125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7508279356706724759064333 2815604758765021784649125)
                  ·
                    refine ⟨527925892268441584621711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2815604758765021784649125 527925892268441584621711)
                    ·
                      rfl

theorem cell22_1542198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_1542198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542198 prefixEnd_1542198 := by exact prefixLift 1542198
  have htrace : WordTrace (prefixWord ++ tailWord_1542198) baseStart_1542198 baseEnd_1542198 := by
    simpa [prefixWord, tailWord_1542198, baseEnd_1542198] using wordTrace_append hprefix tailTrace_1542198
  have hstable : (prefixWord ++ tailWord_1542198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542198).length < 2 ^ (prefixWord ++ tailWord_1542198).sum := by decide
  have hdescent : baseEnd_1542198 < baseStart_1542198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542211 : List Nat := [1, 1, 1, 3, 1, 2, 2, 2, 6, 3]
def baseStart_1542211 : Nat := 118140960795 + 1542211 * 2 ^ 59
def prefixEnd_1542211 : Nat := 4983230072969 + 3 ^ 40 * 1542211 * 2
def baseEnd_1542211 : Nat := 527930342434113884046671

theorem tailTrace_1542211 : CollatzResearch.WordTrace tailWord_1542211 prefixEnd_1542211 527930342434113884046671 := by
  unfold tailWord_1542211
  simp only [CollatzResearch.WordTrace]
  refine ⟨56249056215840410514466487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37499370810560273676310991 56249056215840410514466487)
  ·
    refine ⟨84373584323760615771699731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56249056215840410514466487 84373584323760615771699731)
    ·
      refine ⟨126560376485640923657549597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84373584323760615771699731 126560376485640923657549597)
      ·
        refine ⟨47460141182115346371581099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126560376485640923657549597 47460141182115346371581099)
        ·
          refine ⟨71190211773173019557371649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47460141182115346371581099 71190211773173019557371649)
          ·
            refine ⟨53392658829879764668028737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 71190211773173019557371649 53392658829879764668028737)
            ·
              refine ⟨40044494122409823501021553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53392658829879764668028737 40044494122409823501021553)
              ·
                refine ⟨30033370591807367625766165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40044494122409823501021553 30033370591807367625766165)
                ·
                  refine ⟨1407814246490970357457789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30033370591807367625766165 1407814246490970357457789)
                  ·
                    refine ⟨527930342434113884046671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1407814246490970357457789 527930342434113884046671)
                    ·
                      rfl

theorem cell22_1542211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 6, 3].length) (baseStart_1542211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542211 prefixEnd_1542211 := by exact prefixLift 1542211
  have htrace : WordTrace (prefixWord ++ tailWord_1542211) baseStart_1542211 baseEnd_1542211 := by
    simpa [prefixWord, tailWord_1542211, baseEnd_1542211] using wordTrace_append hprefix tailTrace_1542211
  have hstable : (prefixWord ++ tailWord_1542211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542211).length < 2 ^ (prefixWord ++ tailWord_1542211).sum := by decide
  have hdescent : baseEnd_1542211 < baseStart_1542211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542245 : List Nat := [1, 3, 1, 3, 2, 3, 2, 2, 2, 3]
def baseStart_1542245 : Nat := 118140960795 + 1542245 * 2 ^ 59
def prefixEnd_1542245 : Nat := 4983230072969 + 3 ^ 40 * 1542245 * 2
def baseEnd_1542245 : Nat := 527941981328949128696567

theorem tailTrace_1542245 : CollatzResearch.WordTrace tailWord_1542245 prefixEnd_1542245 527941981328949128696567 := by
  unfold tailWord_1542245
  simp only [CollatzResearch.WordTrace]
  refine ⟨56250296297717234321204189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37500197531811489547469459 56250296297717234321204189)
  ·
    refine ⟨21093861111643962870451571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56250296297717234321204189 21093861111643962870451571)
    ·
      refine ⟨31640791667465944305677357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21093861111643962870451571 31640791667465944305677357)
      ·
        refine ⟨11865296875299729114629009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31640791667465944305677357 11865296875299729114629009)
        ·
          refine ⟨8898972656474796835971757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11865296875299729114629009 8898972656474796835971757)
          ·
            refine ⟨3337114746178048813489409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8898972656474796835971757 3337114746178048813489409)
            ·
              refine ⟨2502836059633536610117057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3337114746178048813489409 2502836059633536610117057)
              ·
                refine ⟨1877127044725152457587793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2502836059633536610117057 1877127044725152457587793)
                ·
                  refine ⟨1407845283543864343190845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1877127044725152457587793 1407845283543864343190845)
                  ·
                    refine ⟨527941981328949128696567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1407845283543864343190845 527941981328949128696567)
                    ·
                      rfl

theorem cell22_1542245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_1542245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542245 prefixEnd_1542245 := by exact prefixLift 1542245
  have htrace : WordTrace (prefixWord ++ tailWord_1542245) baseStart_1542245 baseEnd_1542245 := by
    simpa [prefixWord, tailWord_1542245, baseEnd_1542245] using wordTrace_append hprefix tailTrace_1542245
  have hstable : (prefixWord ++ tailWord_1542245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542245).length < 2 ^ (prefixWord ++ tailWord_1542245).sum := by decide
  have hdescent : baseEnd_1542245 < baseStart_1542245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542258 : List Nat := [3, 2, 1, 2, 2, 4, 1, 7]
def baseStart_1542258 : Nat := 118140960795 + 1542258 * 2 ^ 59
def prefixEnd_1542258 : Nat := 4983230072969 + 3 ^ 40 * 1542258 * 2
def baseEnd_1542258 : Nat := 58660714610513492013503

theorem tailTrace_1542258 : CollatzResearch.WordTrace tailWord_1542258 prefixEnd_1542258 58660714610513492013503 := by
  unfold tailWord_1542258
  simp only [CollatzResearch.WordTrace]
  refine ⟨14062692611667534385356857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37500513631113425027618285 14062692611667534385356857)
  ·
    refine ⟨10547019458750650789017643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14062692611667534385356857 10547019458750650789017643)
    ·
      refine ⟨15820529188125976183526465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10547019458750650789017643 15820529188125976183526465)
      ·
        refine ⟨11865396891094482137644849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15820529188125976183526465 11865396891094482137644849)
        ·
          refine ⟨8899047668320861603233637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11865396891094482137644849 8899047668320861603233637)
          ·
            refine ⟨1668571437810161550606307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8899047668320861603233637 1668571437810161550606307)
            ·
              refine ⟨2502857156715242325909461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668571437810161550606307 2502857156715242325909461)
              ·
                refine ⟨58660714610513492013503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2502857156715242325909461 58660714610513492013503)
                ·
                  rfl

theorem cell22_1542258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 7].length) (baseStart_1542258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542258 prefixEnd_1542258 := by exact prefixLift 1542258
  have htrace : WordTrace (prefixWord ++ tailWord_1542258) baseStart_1542258 baseEnd_1542258 := by
    simpa [prefixWord, tailWord_1542258, baseEnd_1542258] using wordTrace_append hprefix tailTrace_1542258
  have hstable : (prefixWord ++ tailWord_1542258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542258).length < 2 ^ (prefixWord ++ tailWord_1542258).sum := by decide
  have hdescent : baseEnd_1542258 < baseStart_1542258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542303 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 7]
def baseStart_1542303 : Nat := 118140960795 + 1542303 * 2 ^ 59
def prefixEnd_1542303 : Nat := 4983230072969 + 3 ^ 40 * 1542303 * 2
def baseEnd_1542303 : Nat := 175987278638085436915463

theorem tailTrace_1542303 : CollatzResearch.WordTrace tailWord_1542303 prefixEnd_1542303 175987278638085436915463 := by
  unfold tailWord_1542303
  simp only [CollatzResearch.WordTrace]
  refine ⟨56252411731507110226815563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37501607821004740151210375 56252411731507110226815563)
  ·
    refine ⟨84378617597260665340223345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56252411731507110226815563 84378617597260665340223345)
    ·
      refine ⟨63283963197945499005167509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84378617597260665340223345 63283963197945499005167509)
      ·
        refine ⟨2966435774903695265867227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 63283963197945499005167509 2966435774903695265867227)
        ·
          refine ⟨4449653662355542898800841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2966435774903695265867227 4449653662355542898800841)
          ·
            refine ⟨3337240246766657174100631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4449653662355542898800841 3337240246766657174100631)
            ·
              refine ⟨5005860370149985761150947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3337240246766657174100631 5005860370149985761150947)
              ·
                refine ⟨7508790555224978641726421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5005860370149985761150947 7508790555224978641726421)
                ·
                  refine ⟨175987278638085436915463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7508790555224978641726421 175987278638085436915463)
                  ·
                    rfl

theorem cell22_1542303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 7].length) (baseStart_1542303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542303 prefixEnd_1542303 := by exact prefixLift 1542303
  have htrace : WordTrace (prefixWord ++ tailWord_1542303) baseStart_1542303 baseEnd_1542303 := by
    simpa [prefixWord, tailWord_1542303, baseEnd_1542303] using wordTrace_append hprefix tailTrace_1542303
  have hstable : (prefixWord ++ tailWord_1542303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542303).length < 2 ^ (prefixWord ++ tailWord_1542303).sum := by decide
  have hdescent : baseEnd_1542303 < baseStart_1542303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542331 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 6]
def baseStart_1542331 : Nat := 118140960795 + 1542331 * 2 ^ 59
def prefixEnd_1542331 : Nat := 4983230072969 + 3 ^ 40 * 1542331 * 2
def baseEnd_1542331 : Nat := 175990473628824523682101

theorem tailTrace_1542331 : CollatzResearch.WordTrace tailWord_1542331 prefixEnd_1542331 175990473628824523682101 := by
  unfold tailWord_1542331
  simp only [CollatzResearch.WordTrace]
  refine ⟨56253432975405671008834847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37502288650270447339223231 56253432975405671008834847)
  ·
    refine ⟨84380149463108506513252271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56253432975405671008834847 84380149463108506513252271)
    ·
      refine ⟨126570224194662759769878407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84380149463108506513252271 126570224194662759769878407)
      ·
        refine ⟨189855336291994139654817611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126570224194662759769878407 189855336291994139654817611)
        ·
          refine ⟨284783004437991209482226417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 189855336291994139654817611 284783004437991209482226417)
          ·
            refine ⟨213587253328493407111669813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 284783004437991209482226417 213587253328493407111669813)
            ·
              refine ⟨20023804999546256916719045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 213587253328493407111669813 20023804999546256916719045)
              ·
                refine ⟨3754463437414923171884821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20023804999546256916719045 3754463437414923171884821)
                ·
                  refine ⟨175990473628824523682101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3754463437414923171884821 175990473628824523682101)
                  ·
                    rfl

theorem cell22_1542331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 6].length) (baseStart_1542331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542331 prefixEnd_1542331 := by exact prefixLift 1542331
  have htrace : WordTrace (prefixWord ++ tailWord_1542331) baseStart_1542331 baseEnd_1542331 := by
    simpa [prefixWord, tailWord_1542331, baseEnd_1542331] using wordTrace_append hprefix tailTrace_1542331
  have hstable : (prefixWord ++ tailWord_1542331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542331).length < 2 ^ (prefixWord ++ tailWord_1542331).sum := by decide
  have hdescent : baseEnd_1542331 < baseStart_1542331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542350 : List Nat := [4, 1, 1, 1, 4, 1, 2, 3, 1, 4]
def baseStart_1542350 : Nat := 118140960795 + 1542350 * 2 ^ 59
def prefixEnd_1542350 : Nat := 4983230072969 + 3 ^ 40 * 1542350 * 2
def baseEnd_1542350 : Nat := 527977924974763854821245

theorem tailTrace_1542350 : CollatzResearch.WordTrace tailWord_1542350 prefixEnd_1542350 527977924974763854821245 := by
  unfold tailWord_1542350
  simp only [CollatzResearch.WordTrace]
  refine ⟨7031765745292104656722063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37502750641557891502517669 7031765745292104656722063)
  ·
    refine ⟨10547648617938156985083095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7031765745292104656722063 10547648617938156985083095)
    ·
      refine ⟨15821472926907235477624643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10547648617938156985083095 15821472926907235477624643)
      ·
        refine ⟨23732209390360853216436965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15821472926907235477624643 23732209390360853216436965)
        ·
          refine ⟨4449789260692659978081931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23732209390360853216436965 4449789260692659978081931)
          ·
            refine ⟨6674683891038989967122897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4449789260692659978081931 6674683891038989967122897)
            ·
              refine ⟨5006012918279242475342173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6674683891038989967122897 5006012918279242475342173)
              ·
                refine ⟨1877254844354715928253315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5006012918279242475342173 1877254844354715928253315)
                ·
                  refine ⟨2815882266532073892379973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1877254844354715928253315 2815882266532073892379973)
                  ·
                    refine ⟨527977924974763854821245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2815882266532073892379973 527977924974763854821245)
                    ·
                      rfl

theorem cell22_1542350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 1, 4].length) (baseStart_1542350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542350 prefixEnd_1542350 := by exact prefixLift 1542350
  have htrace : WordTrace (prefixWord ++ tailWord_1542350) baseStart_1542350 baseEnd_1542350 := by
    simpa [prefixWord, tailWord_1542350, baseEnd_1542350] using wordTrace_append hprefix tailTrace_1542350
  have hstable : (prefixWord ++ tailWord_1542350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542350).length < 2 ^ (prefixWord ++ tailWord_1542350).sum := by decide
  have hdescent : baseEnd_1542350 < baseStart_1542350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542365 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 6]
def baseStart_1542365 : Nat := 118140960795 + 1542365 * 2 ^ 59
def prefixEnd_1542365 : Nat := 4983230072969 + 3 ^ 40 * 1542365 * 2
def baseEnd_1542365 : Nat := 175994353260436271898733

theorem tailTrace_1542365 : CollatzResearch.WordTrace tailWord_1542365 prefixEnd_1542365 175994353260436271898733 := by
  unfold tailWord_1542365
  simp only [CollatzResearch.WordTrace]
  refine ⟨56254673057282494815572549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37503115371521663210381699 56254673057282494815572549)
  ·
    refine ⟨10547751198240467777919853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56254673057282494815572549 10547751198240467777919853)
    ·
      refine ⟨3955406699340175416719945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10547751198240467777919853 3955406699340175416719945)
      ·
        refine ⟨2966555024505131562539959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3955406699340175416719945 2966555024505131562539959)
        ·
          refine ⟨4449832536757697343809939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2966555024505131562539959 4449832536757697343809939)
          ·
            refine ⟨6674748805136546015714909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4449832536757697343809939 6674748805136546015714909)
            ·
              refine ⟨2503030801926204755893091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6674748805136546015714909 2503030801926204755893091)
              ·
                refine ⟨3754546202889307133839637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2503030801926204755893091 3754546202889307133839637)
                ·
                  refine ⟨175994353260436271898733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3754546202889307133839637 175994353260436271898733)
                  ·
                    rfl

theorem cell22_1542365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_1542365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542365 prefixEnd_1542365 := by exact prefixLift 1542365
  have htrace : WordTrace (prefixWord ++ tailWord_1542365) baseStart_1542365 baseEnd_1542365 := by
    simpa [prefixWord, tailWord_1542365, baseEnd_1542365] using wordTrace_append hprefix tailTrace_1542365
  have hstable : (prefixWord ++ tailWord_1542365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542365).length < 2 ^ (prefixWord ++ tailWord_1542365).sum := by decide
  have hdescent : baseEnd_1542365 < baseStart_1542365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542378 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 4, 4]
def baseStart_1542378 : Nat := 118140960795 + 1542378 * 2 ^ 59
def prefixEnd_1542378 : Nat := 4983230072969 + 3 ^ 40 * 1542378 * 2
def baseEnd_1542378 : Nat := 527987509946981115121159

theorem tailTrace_1542378 : CollatzResearch.WordTrace tailWord_1542378 prefixEnd_1542378 527987509946981115121159 := by
  unfold tailWord_1542378
  simp only [CollatzResearch.WordTrace]
  refine ⟨14063786801558849508948947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37503431470823598690530525 14063786801558849508948947)
  ·
    refine ⟨21095680202338274263423421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14063786801558849508948947 21095680202338274263423421)
    ·
      refine ⟨7910880075876852848783783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21095680202338274263423421 7910880075876852848783783)
      ·
        refine ⟨11866320113815279273175675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7910880075876852848783783 11866320113815279273175675)
        ·
          refine ⟨17799480170722918909763513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11866320113815279273175675 17799480170722918909763513)
          ·
            refine ⟨13349610128042189182322635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17799480170722918909763513 13349610128042189182322635)
            ·
              refine ⟨20024415192063283773483953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13349610128042189182322635 20024415192063283773483953)
              ·
                refine ⟨15018311394047462830112965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20024415192063283773483953 15018311394047462830112965)
                ·
                  refine ⟨2815933386383899280646181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15018311394047462830112965 2815933386383899280646181)
                  ·
                    refine ⟨527987509946981115121159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2815933386383899280646181 527987509946981115121159)
                    ·
                      rfl

theorem cell22_1542378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_1542378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542378 prefixEnd_1542378 := by exact prefixLift 1542378
  have htrace : WordTrace (prefixWord ++ tailWord_1542378) baseStart_1542378 baseEnd_1542378 := by
    simpa [prefixWord, tailWord_1542378, baseEnd_1542378] using wordTrace_append hprefix tailTrace_1542378
  have hstable : (prefixWord ++ tailWord_1542378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542378).length < 2 ^ (prefixWord ++ tailWord_1542378).sum := by decide
  have hdescent : baseEnd_1542378 < baseStart_1542378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542380 : List Nat := [2, 2, 1, 1, 2, 3, 3, 3, 2, 3]
def baseStart_1542380 : Nat := 118140960795 + 1542380 * 2 ^ 59
def prefixEnd_1542380 : Nat := 4983230072969 + 3 ^ 40 * 1542380 * 2
def baseEnd_1542380 : Nat := 527988194587853776571153

theorem tailTrace_1542380 : CollatzResearch.WordTrace tailWord_1542380 prefixEnd_1542380 527988194587853776571153 := by
  unfold tailWord_1542380
  simp only [CollatzResearch.WordTrace]
  refine ⟨28127610076114076188684297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37503480101485434918245729 28127610076114076188684297)
  ·
    refine ⟨21095707557085557141513223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28127610076114076188684297 21095707557085557141513223)
    ·
      refine ⟨31643561335628335712269835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21095707557085557141513223 31643561335628335712269835)
      ·
        refine ⟨47465342003442503568404753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31643561335628335712269835 47465342003442503568404753)
        ·
          refine ⟨35599006502581877676303565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47465342003442503568404753 35599006502581877676303565)
          ·
            refine ⟨13349627438468204128613837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35599006502581877676303565 13349627438468204128613837)
            ·
              refine ⟨5006110289425576548230189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13349627438468204128613837 5006110289425576548230189)
              ·
                refine ⟨1877291358534591205586321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5006110289425576548230189 1877291358534591205586321)
                ·
                  refine ⟨1407968518900943404189741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1877291358534591205586321 1407968518900943404189741)
                  ·
                    refine ⟨527988194587853776571153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1407968518900943404189741 527988194587853776571153)
                    ·
                      rfl

theorem cell22_1542380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 3].length) (baseStart_1542380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542380 prefixEnd_1542380 := by exact prefixLift 1542380
  have htrace : WordTrace (prefixWord ++ tailWord_1542380) baseStart_1542380 baseEnd_1542380 := by
    simpa [prefixWord, tailWord_1542380, baseEnd_1542380] using wordTrace_append hprefix tailTrace_1542380
  have hstable : (prefixWord ++ tailWord_1542380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542380).length < 2 ^ (prefixWord ++ tailWord_1542380).sum := by decide
  have hdescent : baseEnd_1542380 < baseStart_1542380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542423 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 2, 6]
def baseStart_1542423 : Nat := 118140960795 + 1542423 * 2 ^ 59
def prefixEnd_1542423 : Nat := 4983230072969 + 3 ^ 40 * 1542423 * 2
def baseEnd_1542423 : Nat := 528002914366615997746021

theorem tailTrace_1542423 : CollatzResearch.WordTrace tailWord_1542423 prefixEnd_1542423 528002914366615997746021 := by
  unfold tailWord_1542423
  simp only [CollatzResearch.WordTrace]
  refine ⟨56256788491072370721183923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37504525660714913814122615 56256788491072370721183923)
  ·
    refine ⟨84385182736608556081775885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56256788491072370721183923 84385182736608556081775885)
    ·
      refine ⟨31644443526228208530665957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84385182736608556081775885 31644443526228208530665957)
      ·
        refine ⟨5933333161167789099499867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31644443526228208530665957 5933333161167789099499867)
        ·
          refine ⟨8899999741751683649249801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5933333161167789099499867 8899999741751683649249801)
          ·
            refine ⟨6674999806313762736937351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8899999741751683649249801 6674999806313762736937351)
            ·
              refine ⟨10012499709470644105406027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6674999806313762736937351 10012499709470644105406027)
              ·
                refine ⟨15018749564205966158109041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10012499709470644105406027 15018749564205966158109041)
                ·
                  refine ⟨11264062173154474618581781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15018749564205966158109041 11264062173154474618581781)
                  ·
                    refine ⟨528002914366615997746021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11264062173154474618581781 528002914366615997746021)
                    ·
                      rfl

theorem cell22_1542423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_1542423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542423 prefixEnd_1542423 := by exact prefixLift 1542423
  have htrace : WordTrace (prefixWord ++ tailWord_1542423) baseStart_1542423 baseEnd_1542423 := by
    simpa [prefixWord, tailWord_1542423, baseEnd_1542423] using wordTrace_append hprefix tailTrace_1542423
  have hstable : (prefixWord ++ tailWord_1542423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542423).length < 2 ^ (prefixWord ++ tailWord_1542423).sum := by decide
  have hdescent : baseEnd_1542423 < baseStart_1542423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542446 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 2, 4]
def baseStart_1542446 : Nat := 118140960795 + 1542446 * 2 ^ 59
def prefixEnd_1542446 : Nat := 4983230072969 + 3 ^ 40 * 1542446 * 2
def baseEnd_1542446 : Nat := 528010787736651604420951

theorem tailTrace_1542446 : CollatzResearch.WordTrace tailWord_1542446 prefixEnd_1542446 528010787736651604420951 := by
  unfold tailWord_1542446
  simp only [CollatzResearch.WordTrace]
  refine ⟨7032203421248630706158899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37505084913326030432847461 7032203421248630706158899)
  ·
    refine ⟨10548305131872946059238349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7032203421248630706158899 10548305131872946059238349)
    ·
      refine ⟨3955614424452354772214381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10548305131872946059238349 3955614424452354772214381)
      ·
        refine ⟨1483355409169633039580393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3955614424452354772214381 1483355409169633039580393)
        ·
          refine ⟨1112516556877224779685295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1483355409169633039580393 1112516556877224779685295)
          ·
            refine ⟨1668774835315837169527943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112516556877224779685295 1668774835315837169527943)
            ·
              refine ⟨2503162252973755754291915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1668774835315837169527943 2503162252973755754291915)
              ·
                refine ⟨3754743379460633631437873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2503162252973755754291915 3754743379460633631437873)
                ·
                  refine ⟨2816057534595475223578405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3754743379460633631437873 2816057534595475223578405)
                  ·
                    refine ⟨528010787736651604420951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2816057534595475223578405 528010787736651604420951)
                    ·
                      rfl

theorem cell22_1542446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_1542446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542446 prefixEnd_1542446 := by exact prefixLift 1542446
  have htrace : WordTrace (prefixWord ++ tailWord_1542446) baseStart_1542446 baseEnd_1542446 := by
    simpa [prefixWord, tailWord_1542446, baseEnd_1542446] using wordTrace_append hprefix tailTrace_1542446
  have hstable : (prefixWord ++ tailWord_1542446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542446).length < 2 ^ (prefixWord ++ tailWord_1542446).sum := by decide
  have hdescent : baseEnd_1542446 < baseStart_1542446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542453 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 1, 7]
def baseStart_1542453 : Nat := 118140960795 + 1542453 * 2 ^ 59
def prefixEnd_1542453 : Nat := 4983230072969 + 3 ^ 40 * 1542453 * 2
def baseEnd_1542453 : Nat := 528013183979705919495929

theorem tailTrace_1542453 : CollatzResearch.WordTrace tailWord_1542453 prefixEnd_1542453 528013183979705919495929 := by
  unfold tailWord_1542453
  simp only [CollatzResearch.WordTrace]
  refine ⟨56257882680963685844776013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37505255120642457229850675 56257882680963685844776013)
  ·
    refine ⟨21096706005361382191791005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56257882680963685844776013 21096706005361382191791005)
    ·
      refine ⟨7911264752010518321921627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21096706005361382191791005 7911264752010518321921627)
      ·
        refine ⟨11866897128015777482882441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7911264752010518321921627 11866897128015777482882441)
        ·
          refine ⟨8900172846011833112161831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11866897128015777482882441 8900172846011833112161831)
          ·
            refine ⟨13350259269017749668242747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8900172846011833112161831 13350259269017749668242747)
            ·
              refine ⟨20025388903526624502364121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13350259269017749668242747 20025388903526624502364121)
              ·
                refine ⟨15019041677644968376773091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20025388903526624502364121 15019041677644968376773091)
                ·
                  refine ⟨22528562516467452565159637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15019041677644968376773091 22528562516467452565159637)
                  ·
                    refine ⟨528013183979705919495929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22528562516467452565159637 528013183979705919495929)
                    ·
                      rfl

theorem cell22_1542453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_1542453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542453 prefixEnd_1542453 := by exact prefixLift 1542453
  have htrace : WordTrace (prefixWord ++ tailWord_1542453) baseStart_1542453 baseEnd_1542453 := by
    simpa [prefixWord, tailWord_1542453, baseEnd_1542453] using wordTrace_append hprefix tailTrace_1542453
  have hstable : (prefixWord ++ tailWord_1542453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542453).length < 2 ^ (prefixWord ++ tailWord_1542453).sum := by decide
  have hdescent : baseEnd_1542453 < baseStart_1542453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542532 : List Nat := [2, 3, 2, 1, 1, 2, 2, 4, 2, 3]
def baseStart_1542532 : Nat := 118140960795 + 1542532 * 2 ^ 59
def prefixEnd_1542532 : Nat := 4983230072969 + 3 ^ 40 * 1542532 * 2
def baseEnd_1542532 : Nat := 528040227294176046770687

theorem tailTrace_1542532 : CollatzResearch.WordTrace tailWord_1542532 prefixEnd_1542532 528040227294176046770687 := by
  unfold tailWord_1542532
  simp only [CollatzResearch.WordTrace]
  refine ⟨28130382023838741168450925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37507176031784988224601233 28130382023838741168450925)
  ·
    refine ⟨10548893258939527938169097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28130382023838741168450925 10548893258939527938169097)
    ·
      refine ⟨7911669944204645953626823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10548893258939527938169097 7911669944204645953626823)
      ·
        refine ⟨11867504916306968930440235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7911669944204645953626823 11867504916306968930440235)
        ·
          refine ⟨17801257374460453395660353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11867504916306968930440235 17801257374460453395660353)
          ·
            refine ⟨13350943030845340046745265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17801257374460453395660353 13350943030845340046745265)
            ·
              refine ⟨10013207273134005035058949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13350943030845340046745265 10013207273134005035058949)
              ·
                refine ⟨1877476363712625944073553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10013207273134005035058949 1877476363712625944073553)
                ·
                  refine ⟨1408107272784469458055165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1877476363712625944073553 1408107272784469458055165)
                  ·
                    refine ⟨528040227294176046770687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1408107272784469458055165 528040227294176046770687)
                    ·
                      rfl

theorem cell22_1542532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_1542532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542532 prefixEnd_1542532 := by exact prefixLift 1542532
  have htrace : WordTrace (prefixWord ++ tailWord_1542532) baseStart_1542532 baseEnd_1542532 := by
    simpa [prefixWord, tailWord_1542532, baseEnd_1542532] using wordTrace_append hprefix tailTrace_1542532
  have hstable : (prefixWord ++ tailWord_1542532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542532).length < 2 ^ (prefixWord ++ tailWord_1542532).sum := by decide
  have hdescent : baseEnd_1542532 < baseStart_1542532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542590 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 7]
def baseStart_1542590 : Nat := 118140960795 + 1542590 * 2 ^ 59
def prefixEnd_1542590 : Nat := 4983230072969 + 3 ^ 40 * 1542590 * 2
def baseEnd_1542590 : Nat := 176020027293161076273503

theorem tailTrace_1542590 : CollatzResearch.WordTrace tailWord_1542590 prefixEnd_1542590 176020027293161076273503 := by
  unfold tailWord_1542590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7032859935183419780314153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37508586320978238828342149 7032859935183419780314153)
  ·
    refine ⟨5274644951387564835235615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7032859935183419780314153 5274644951387564835235615)
    ·
      refine ⟨7911967427081347252853423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5274644951387564835235615 7911967427081347252853423)
      ·
        refine ⟨11867951140622020879280135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7911967427081347252853423 11867951140622020879280135)
        ·
          refine ⟨17801926710933031318920203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11867951140622020879280135 17801926710933031318920203)
          ·
            refine ⟨26702890066399546978380305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17801926710933031318920203 26702890066399546978380305)
            ·
              refine ⟨20027167549799660233785229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26702890066399546978380305 20027167549799660233785229)
              ·
                refine ⟨7510187831174872587669461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20027167549799660233785229 7510187831174872587669461)
                ·
                  refine ⟨176020027293161076273503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7510187831174872587669461 176020027293161076273503)
                  ·
                    rfl

theorem cell22_1542590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_1542590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542590 prefixEnd_1542590 := by exact prefixLift 1542590
  have htrace : WordTrace (prefixWord ++ tailWord_1542590) baseStart_1542590 baseEnd_1542590 := by
    simpa [prefixWord, tailWord_1542590, baseEnd_1542590] using wordTrace_append hprefix tailTrace_1542590
  have hstable : (prefixWord ++ tailWord_1542590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542590).length < 2 ^ (prefixWord ++ tailWord_1542590).sum := by decide
  have hdescent : baseEnd_1542590 < baseStart_1542590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542665 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 6, 4]
def baseStart_1542665 : Nat := 118140960795 + 1542665 * 2 ^ 59
def prefixEnd_1542665 : Nat := 4983230072969 + 3 ^ 40 * 1542665 * 2
def baseEnd_1542665 : Nat := 528085755912208033195279

theorem tailTrace_1542665 : CollatzResearch.WordTrace tailWord_1542665 prefixEnd_1542665 528085755912208033195279 := by
  unfold tailWord_1542665
  simp only [CollatzResearch.WordTrace]
  refine ⟨56265614956195646051493449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37510409970797097367662299 56265614956195646051493449)
  ·
    refine ⟨42199211217146734538620087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56265614956195646051493449 42199211217146734538620087)
    ·
      refine ⟨63298816825720101807930131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42199211217146734538620087 63298816825720101807930131)
      ·
        refine ⟨94948225238580152711895197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63298816825720101807930131 94948225238580152711895197)
        ·
          refine ⟨35605584464467557266960699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 94948225238580152711895197 35605584464467557266960699)
          ·
            refine ⟨53408376696701335900441049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35605584464467557266960699 53408376696701335900441049)
            ·
              refine ⟨40056282522526001925330787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53408376696701335900441049 40056282522526001925330787)
              ·
                refine ⟨60084423783789002887996181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40056282522526001925330787 60084423783789002887996181)
                ·
                  refine ⟨2816457364865109510374821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 60084423783789002887996181 2816457364865109510374821)
                  ·
                    refine ⟨528085755912208033195279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2816457364865109510374821 528085755912208033195279)
                    ·
                      rfl

theorem cell22_1542665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_1542665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542665 prefixEnd_1542665 := by exact prefixLift 1542665
  have htrace : WordTrace (prefixWord ++ tailWord_1542665) baseStart_1542665 baseEnd_1542665 := by
    simpa [prefixWord, tailWord_1542665, baseEnd_1542665] using wordTrace_append hprefix tailTrace_1542665
  have hstable : (prefixWord ++ tailWord_1542665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542665).length < 2 ^ (prefixWord ++ tailWord_1542665).sum := by decide
  have hdescent : baseEnd_1542665 < baseStart_1542665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542667 : List Nat := [1, 1, 1, 1, 7, 1, 3, 1, 1, 5]
def baseStart_1542667 : Nat := 118140960795 + 1542667 * 2 ^ 59
def prefixEnd_1542667 : Nat := 4983230072969 + 3 ^ 40 * 1542667 * 2
def baseEnd_1542667 : Nat := 528086440553080694645273

theorem tailTrace_1542667 : CollatzResearch.WordTrace tailWord_1542667 prefixEnd_1542667 528086440553080694645273 := by
  unfold tailWord_1542667
  simp only [CollatzResearch.WordTrace]
  refine ⟨56265687902188400393066255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37510458601458933595377503 56265687902188400393066255)
  ·
    refine ⟨84398531853282600589599383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56265687902188400393066255 84398531853282600589599383)
    ·
      refine ⟨126597797779923900884399075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84398531853282600589599383 126597797779923900884399075)
      ·
        refine ⟨189896696669885851326598613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126597797779923900884399075 189896696669885851326598613)
        ·
          refine ⟨4450703828200449640467155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 189896696669885851326598613 4450703828200449640467155)
          ·
            refine ⟨6676055742300674460700733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4450703828200449640467155 6676055742300674460700733)
            ·
              refine ⟨2503520903362752922762775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6676055742300674460700733 2503520903362752922762775)
              ·
                refine ⟨3755281355044129384144163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2503520903362752922762775 3755281355044129384144163)
                ·
                  refine ⟨5632922032566194076216245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3755281355044129384144163 5632922032566194076216245)
                  ·
                    refine ⟨528086440553080694645273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5632922032566194076216245 528086440553080694645273)
                    ·
                      rfl

theorem cell22_1542667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 1, 1, 5].length) (baseStart_1542667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542667 prefixEnd_1542667 := by exact prefixLift 1542667
  have htrace : WordTrace (prefixWord ++ tailWord_1542667) baseStart_1542667 baseEnd_1542667 := by
    simpa [prefixWord, tailWord_1542667, baseEnd_1542667] using wordTrace_append hprefix tailTrace_1542667
  have hstable : (prefixWord ++ tailWord_1542667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542667).length < 2 ^ (prefixWord ++ tailWord_1542667).sum := by decide
  have hdescent : baseEnd_1542667 < baseStart_1542667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542718 : List Nat := [4, 2, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_1542718 : Nat := 118140960795 + 1542718 * 2 ^ 59
def prefixEnd_1542718 : Nat := 4983230072969 + 3 ^ 40 * 1542718 * 2
def baseEnd_1542718 : Nat := 528103898895333561620117

theorem tailTrace_1542718 : CollatzResearch.WordTrace tailWord_1542718 prefixEnd_1542718 528103898895333561620117 := by
  unfold tailWord_1542718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7033443503125454512896601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37511698683335757402115205 7033443503125454512896601)
  ·
    refine ⟨5275082627344090884672451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7033443503125454512896601 5275082627344090884672451)
    ·
      refine ⟨7912623941016136327008677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5275082627344090884672451 7912623941016136327008677)
      ·
        refine ⟨1483616988940525561314127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7912623941016136327008677 1483616988940525561314127)
        ·
          refine ⟨2225425483410788341971191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1483616988940525561314127 2225425483410788341971191)
          ·
            refine ⟨3338138225116182512956787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2225425483410788341971191 3338138225116182512956787)
            ·
              refine ⟨5007207337674273769435181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3338138225116182512956787 5007207337674273769435181)
              ·
                refine ⟨1877702751627852663538193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5007207337674273769435181 1877702751627852663538193)
                ·
                  refine ⟨1408277063720889497653645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1877702751627852663538193 1408277063720889497653645)
                  ·
                    refine ⟨528103898895333561620117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1408277063720889497653645 528103898895333561620117)
                    ·
                      rfl

theorem cell22_1542718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_1542718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542718 prefixEnd_1542718 := by exact prefixLift 1542718
  have htrace : WordTrace (prefixWord ++ tailWord_1542718) baseStart_1542718 baseEnd_1542718 := by
    simpa [prefixWord, tailWord_1542718, baseEnd_1542718] using wordTrace_append hprefix tailTrace_1542718
  have hstable : (prefixWord ++ tailWord_1542718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542718).length < 2 ^ (prefixWord ++ tailWord_1542718).sum := by decide
  have hdescent : baseEnd_1542718 < baseStart_1542718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542819 : List Nat := [1, 1, 1, 4, 1, 1, 2, 6, 2, 3]
def baseStart_1542819 : Nat := 118140960795 + 1542819 * 2 ^ 59
def prefixEnd_1542819 : Nat := 4983230072969 + 3 ^ 40 * 1542819 * 2
def baseEnd_1542819 : Nat := 528138473259402964844807

theorem tailTrace_1542819 : CollatzResearch.WordTrace tailWord_1542819 prefixEnd_1542819 528138473259402964844807 := by
  unfold tailWord_1542819
  simp only [CollatzResearch.WordTrace]
  refine ⟨56271231797637730352599511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37514154531758486901733007 56271231797637730352599511)
  ·
    refine ⟨84406847696456595528899267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56271231797637730352599511 84406847696456595528899267)
    ·
      refine ⟨126610271544684893293348901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84406847696456595528899267 126610271544684893293348901)
      ·
        refine ⟨23739425914628417492502919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 126610271544684893293348901 23739425914628417492502919)
        ·
          refine ⟨35609138871942626238754379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23739425914628417492502919 35609138871942626238754379)
          ·
            refine ⟨53413708307913939358131569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35609138871942626238754379 53413708307913939358131569)
            ·
              refine ⟨40060281230935454518598677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53413708307913939358131569 40060281230935454518598677)
              ·
                refine ⟨1877825682700099430559313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40060281230935454518598677 1877825682700099430559313)
                ·
                  refine ⟨1408369262025074572919485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1877825682700099430559313 1408369262025074572919485)
                  ·
                    refine ⟨528138473259402964844807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1408369262025074572919485 528138473259402964844807)
                    ·
                      rfl

theorem cell22_1542819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 6, 2, 3].length) (baseStart_1542819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542819 prefixEnd_1542819 := by exact prefixLift 1542819
  have htrace : WordTrace (prefixWord ++ tailWord_1542819) baseStart_1542819 baseEnd_1542819 := by
    simpa [prefixWord, tailWord_1542819, baseEnd_1542819] using wordTrace_append hprefix tailTrace_1542819
  have hstable : (prefixWord ++ tailWord_1542819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542819).length < 2 ^ (prefixWord ++ tailWord_1542819).sum := by decide
  have hdescent : baseEnd_1542819 < baseStart_1542819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542866 : List Nat := [3, 2, 2, 2, 4, 1, 8]
def baseStart_1542866 : Nat := 118140960795 + 1542866 * 2 ^ 59
def prefixEnd_1542866 : Nat := 4983230072969 + 3 ^ 40 * 1542866 * 2
def baseEnd_1542866 : Nat := 19561280085922611441469

theorem tailTrace_1542866 : CollatzResearch.WordTrace tailWord_1542866 prefixEnd_1542866 19561280085922611441469 := by
  unfold tailWord_1542866
  simp only [CollatzResearch.WordTrace]
  refine ⟨14068236507116864344890113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37515297352311638253040301 14068236507116864344890113)
  ·
    refine ⟨10551177380337648258667585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14068236507116864344890113 10551177380337648258667585)
    ·
      refine ⟨7913383035253236194000689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10551177380337648258667585 7913383035253236194000689)
      ·
        refine ⟨5935037276439927145500517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7913383035253236194000689 5935037276439927145500517)
        ·
          refine ⟨1112819489332486339781347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5935037276439927145500517 1112819489332486339781347)
          ·
            refine ⟨1669229233998729509672021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1112819489332486339781347 1669229233998729509672021)
            ·
              refine ⟨19561280085922611441469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1669229233998729509672021 19561280085922611441469)
              ·
                rfl

theorem cell22_1542866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 8].length) (baseStart_1542866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542866 prefixEnd_1542866 := by exact prefixLift 1542866
  have htrace : WordTrace (prefixWord ++ tailWord_1542866) baseStart_1542866 baseEnd_1542866 := by
    simpa [prefixWord, tailWord_1542866, baseEnd_1542866] using wordTrace_append hprefix tailTrace_1542866
  have hstable : (prefixWord ++ tailWord_1542866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542866).length < 2 ^ (prefixWord ++ tailWord_1542866).sum := by decide
  have hdescent : baseEnd_1542866 < baseStart_1542866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542881 : List Nat := [1, 2, 3, 1, 4, 1, 3, 1, 3, 3]
def baseStart_1542881 : Nat := 118140960795 + 1542881 * 2 ^ 59
def prefixEnd_1542881 : Nat := 4983230072969 + 3 ^ 40 * 1542881 * 2
def baseEnd_1542881 : Nat := 528159697126455469794617

theorem tailTrace_1542881 : CollatzResearch.WordTrace tailWord_1542881 prefixEnd_1542881 528159697126455469794617 := by
  unfold tailWord_1542881
  simp only [CollatzResearch.WordTrace]
  refine ⟨56273493123413114941356497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37515662082275409960904331 56273493123413114941356497)
  ·
    refine ⟨42205119842559836206017373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56273493123413114941356497 42205119842559836206017373)
    ·
      refine ⟨15826919940959938577256515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42205119842559836206017373 15826919940959938577256515)
      ·
        refine ⟨23740379911439907865884773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15826919940959938577256515 23740379911439907865884773)
        ·
          refine ⟨4451321233394982724853395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23740379911439907865884773 4451321233394982724853395)
          ·
            refine ⟨6676981850092474087280093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4451321233394982724853395 6676981850092474087280093)
            ·
              refine ⟨2503868193784677782730035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6676981850092474087280093 2503868193784677782730035)
              ·
                refine ⟨3755802290677016674095053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2503868193784677782730035 3755802290677016674095053)
                ·
                  refine ⟨1408425859003881252785645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3755802290677016674095053 1408425859003881252785645)
                  ·
                    refine ⟨528159697126455469794617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1408425859003881252785645 528159697126455469794617)
                    ·
                      rfl

theorem cell22_1542881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_1542881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542881 prefixEnd_1542881 := by exact prefixLift 1542881
  have htrace : WordTrace (prefixWord ++ tailWord_1542881) baseStart_1542881 baseEnd_1542881 := by
    simpa [prefixWord, tailWord_1542881, baseEnd_1542881] using wordTrace_append hprefix tailTrace_1542881
  have hstable : (prefixWord ++ tailWord_1542881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542881).length < 2 ^ (prefixWord ++ tailWord_1542881).sum := by decide
  have hdescent : baseEnd_1542881 < baseStart_1542881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542892 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 1, 7]
def baseStart_1542892 : Nat := 118140960795 + 1542892 * 2 ^ 59
def prefixEnd_1542892 : Nat := 4983230072969 + 3 ^ 40 * 1542892 * 2
def baseEnd_1542892 : Nat := 528163462651255107769583

theorem tailTrace_1542892 : CollatzResearch.WordTrace tailWord_1542892 prefixEnd_1542892 528163462651255107769583 := by
  unfold tailWord_1542892
  simp only [CollatzResearch.WordTrace]
  refine ⟨28136947163186631910003465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37515929550915509213337953 28136947163186631910003465)
  ·
    refine ⟨21102710372389973932502599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28136947163186631910003465 21102710372389973932502599)
    ·
      refine ⟨31654065558584960898753899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21102710372389973932502599 31654065558584960898753899)
      ·
        refine ⟨47481098337877441348130849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31654065558584960898753899 47481098337877441348130849)
        ·
          refine ⟨35610823753408081011098137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47481098337877441348130849 35610823753408081011098137)
          ·
            refine ⟨26708117815056060758323603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35610823753408081011098137 26708117815056060758323603)
            ·
              refine ⟨40062176722584091137485405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26708117815056060758323603 40062176722584091137485405)
              ·
                refine ⟨15023316270969034176557027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40062176722584091137485405 15023316270969034176557027)
                ·
                  refine ⟨22534974406453551264835541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15023316270969034176557027 22534974406453551264835541)
                  ·
                    refine ⟨528163462651255107769583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22534974406453551264835541 528163462651255107769583)
                    ·
                      rfl

theorem cell22_1542892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_1542892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542892 prefixEnd_1542892 := by exact prefixLift 1542892
  have htrace : WordTrace (prefixWord ++ tailWord_1542892) baseStart_1542892 baseEnd_1542892 := by
    simpa [prefixWord, tailWord_1542892, baseEnd_1542892] using wordTrace_append hprefix tailTrace_1542892
  have hstable : (prefixWord ++ tailWord_1542892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542892).length < 2 ^ (prefixWord ++ tailWord_1542892).sum := by decide
  have hdescent : baseEnd_1542892 < baseStart_1542892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1542988 : List Nat := [2, 2, 1, 3, 3, 1, 3, 2, 2, 3]
def baseStart_1542988 : Nat := 118140960795 + 1542988 * 2 ^ 59
def prefixEnd_1542988 : Nat := 4983230072969 + 3 ^ 40 * 1542988 * 2
def baseEnd_1542988 : Nat := 528196325413142857369289

theorem tailTrace_1542988 : CollatzResearch.WordTrace tailWord_1542988 prefixEnd_1542988 528196325413142857369289 := by
  unfold tailWord_1542988
  simp only [CollatzResearch.WordTrace]
  refine ⟨28138697867012736107750809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37518263822683648143667745 28138697867012736107750809)
  ·
    refine ⟨21104023400259552080813107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28138697867012736107750809 21104023400259552080813107)
    ·
      refine ⟨31656035100389328121219661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21104023400259552080813107 31656035100389328121219661)
      ·
        refine ⟨11871013162645998045457373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31656035100389328121219661 11871013162645998045457373)
        ·
          refine ⟨4451629935992249267046515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11871013162645998045457373 4451629935992249267046515)
          ·
            refine ⟨6677444903988373900569773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4451629935992249267046515 6677444903988373900569773)
            ·
              refine ⟨2504041838995640212713665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6677444903988373900569773 2504041838995640212713665)
              ·
                refine ⟨1878031379246730159535249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2504041838995640212713665 1878031379246730159535249)
                ·
                  refine ⟨1408523534435047619651437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1878031379246730159535249 1408523534435047619651437)
                  ·
                    refine ⟨528196325413142857369289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1408523534435047619651437 528196325413142857369289)
                    ·
                      rfl

theorem cell22_1542988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 2, 3].length) (baseStart_1542988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1542988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1542988 prefixEnd_1542988 := by exact prefixLift 1542988
  have htrace : WordTrace (prefixWord ++ tailWord_1542988) baseStart_1542988 baseEnd_1542988 := by
    simpa [prefixWord, tailWord_1542988, baseEnd_1542988] using wordTrace_append hprefix tailTrace_1542988
  have hstable : (prefixWord ++ tailWord_1542988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1542988).length < 2 ^ (prefixWord ++ tailWord_1542988).sum := by decide
  have hdescent : baseEnd_1542988 < baseStart_1542988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1542988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543050 : List Nat := [3, 1, 2, 4, 1, 3, 1, 1, 3, 3]
def baseStart_1543050 : Nat := 118140960795 + 1543050 * 2 ^ 59
def prefixEnd_1543050 : Nat := 4983230072969 + 3 ^ 40 * 1543050 * 2
def baseEnd_1543050 : Nat := 528217549280195362319099

theorem tailTrace_1543050 : CollatzResearch.WordTrace tailWord_1543050 prefixEnd_1543050 528217549280195362319099 := by
  unfold tailWord_1543050
  simp only [CollatzResearch.WordTrace]
  refine ⟨14069914264950214201064651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37519771373200571202839069 14069914264950214201064651)
  ·
    refine ⟨21104871397425321301596977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14069914264950214201064651 21104871397425321301596977)
    ·
      refine ⟨15828653548068990976197733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21104871397425321301596977 15828653548068990976197733)
      ·
        refine ⟨2967872540262935808037075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15828653548068990976197733 2967872540262935808037075)
        ·
          refine ⟨4451808810394403712055613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2967872540262935808037075 4451808810394403712055613)
          ·
            refine ⟨1669428303897901392020855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4451808810394403712055613 1669428303897901392020855)
            ·
              refine ⟨2504142455846852088031283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1669428303897901392020855 2504142455846852088031283)
              ·
                refine ⟨3756213683770278132046925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2504142455846852088031283 3756213683770278132046925)
                ·
                  refine ⟨1408580131413854299517597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3756213683770278132046925 1408580131413854299517597)
                  ·
                    refine ⟨528217549280195362319099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1408580131413854299517597 528217549280195362319099)
                    ·
                      rfl

theorem cell22_1543050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_1543050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543050 prefixEnd_1543050 := by exact prefixLift 1543050
  have htrace : WordTrace (prefixWord ++ tailWord_1543050) baseStart_1543050 baseEnd_1543050 := by
    simpa [prefixWord, tailWord_1543050, baseEnd_1543050] using wordTrace_append hprefix tailTrace_1543050
  have hstable : (prefixWord ++ tailWord_1543050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543050).length < 2 ^ (prefixWord ++ tailWord_1543050).sum := by decide
  have hdescent : baseEnd_1543050 < baseStart_1543050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543076 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_1543076 : Nat := 118140960795 + 1543076 * 2 ^ 59
def prefixEnd_1543076 : Nat := 4983230072969 + 3 ^ 40 * 1543076 * 2
def baseEnd_1543076 : Nat := 528226449611539961169019

theorem tailTrace_1543076 : CollatzResearch.WordTrace tailWord_1543076 prefixEnd_1543076 528226449611539961169019 := by
  unfold tailWord_1543076
  simp only [CollatzResearch.WordTrace]
  refine ⟨28140302678853331622352541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37520403571804442163136721 28140302678853331622352541)
  ·
    refine ⟨10552613504569999358382203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28140302678853331622352541 10552613504569999358382203)
    ·
      refine ⟨15828920256854999037573305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10552613504569999358382203 15828920256854999037573305)
      ·
        refine ⟨11871690192641249278179979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15828920256854999037573305 11871690192641249278179979)
        ·
          refine ⟨17807535288961873917269969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11871690192641249278179979 17807535288961873917269969)
          ·
            refine ⟨13355651466721405437952477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17807535288961873917269969 13355651466721405437952477)
            ·
              refine ⟨5008369300020527039232179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13355651466721405437952477 5008369300020527039232179)
              ·
                refine ⟨7512553950030790558848269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5008369300020527039232179 7512553950030790558848269)
                ·
                  refine ⟨2817207731261546459568101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7512553950030790558848269 2817207731261546459568101)
                  ·
                    refine ⟨528226449611539961169019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2817207731261546459568101 528226449611539961169019)
                    ·
                      rfl

theorem cell22_1543076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_1543076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543076 prefixEnd_1543076 := by exact prefixLift 1543076
  have htrace : WordTrace (prefixWord ++ tailWord_1543076) baseStart_1543076 baseEnd_1543076 := by
    simpa [prefixWord, tailWord_1543076, baseEnd_1543076] using wordTrace_append hprefix tailTrace_1543076
  have hstable : (prefixWord ++ tailWord_1543076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543076).length < 2 ^ (prefixWord ++ tailWord_1543076).sum := by decide
  have hdescent : baseEnd_1543076 < baseStart_1543076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543157 : List Nat := [1, 3, 5, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1543157 : Nat := 118140960795 + 1543157 * 2 ^ 59
def prefixEnd_1543157 : Nat := 4983230072969 + 3 ^ 40 * 1543157 * 2
def baseEnd_1543157 : Nat := 528254177566882749893771

theorem tailTrace_1543157 : CollatzResearch.WordTrace tailWord_1543157 prefixEnd_1543157 528254177566882749893771 := by
  unfold tailWord_1543157
  simp only [CollatzResearch.WordTrace]
  refine ⟨56283559670413214078403725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37522373113608809385602483 56283559670413214078403725)
  ·
    refine ⟨21106334876404955279401397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56283559670413214078403725 21106334876404955279401397)
    ·
      refine ⟨1978718894662964557443881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21106334876404955279401397 1978718894662964557443881)
      ·
        refine ⟨1484039170997223418082911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1978718894662964557443881 1484039170997223418082911)
        ·
          refine ⟨2226058756495835127124367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1484039170997223418082911 2226058756495835127124367)
          ·
            refine ⟨3339088134743752690686551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2226058756495835127124367 3339088134743752690686551)
            ·
              refine ⟨5008632202115629036029827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339088134743752690686551 5008632202115629036029827)
              ·
                refine ⟨7512948303173443554044741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5008632202115629036029827 7512948303173443554044741)
                ·
                  refine ⟨1408677806845020666383389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7512948303173443554044741 1408677806845020666383389)
                  ·
                    refine ⟨528254177566882749893771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1408677806845020666383389 528254177566882749893771)
                    ·
                      rfl

theorem cell22_1543157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1543157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543157 prefixEnd_1543157 := by exact prefixLift 1543157
  have htrace : WordTrace (prefixWord ++ tailWord_1543157) baseStart_1543157 baseEnd_1543157 := by
    simpa [prefixWord, tailWord_1543157, baseEnd_1543157] using wordTrace_append hprefix tailTrace_1543157
  have hstable : (prefixWord ++ tailWord_1543157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543157).length < 2 ^ (prefixWord ++ tailWord_1543157).sum := by decide
  have hdescent : baseEnd_1543157 < baseStart_1543157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543202 : List Nat := [3, 3, 1, 1, 1, 3, 3, 3, 1, 3]
def baseStart_1543202 : Nat := 118140960795 + 1543202 * 2 ^ 59
def prefixEnd_1543202 : Nat := 4983230072969 + 3 ^ 40 * 1543202 * 2
def baseEnd_1543202 : Nat := 528269581986517632518633

theorem tailTrace_1543202 : CollatzResearch.WordTrace tailWord_1543202 prefixEnd_1543202 528269581986517632518633 := by
  unfold tailWord_1543202
  simp only [CollatzResearch.WordTrace]
  refine ⟨14071300238812546690947965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37523467303500124509194573 14071300238812546690947965)
  ·
    refine ⟨5276737589554705009105487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14071300238812546690947965 5276737589554705009105487)
    ·
      refine ⟨7915106384332057513658231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5276737589554705009105487 7915106384332057513658231)
      ·
        refine ⟨11872659576498086270487347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7915106384332057513658231 11872659576498086270487347)
        ·
          refine ⟨17808989364747129405731021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11872659576498086270487347 17808989364747129405731021)
          ·
            refine ⟨6678371011780173527149133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17808989364747129405731021 6678371011780173527149133)
            ·
              refine ⟨2504389129417565072680925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6678371011780173527149133 2504389129417565072680925)
              ·
                refine ⟨939145923531586902255347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2504389129417565072680925 939145923531586902255347)
                ·
                  refine ⟨1408718885297380353383021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 939145923531586902255347 1408718885297380353383021)
                  ·
                    refine ⟨528269581986517632518633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1408718885297380353383021 528269581986517632518633)
                    ·
                      rfl

theorem cell22_1543202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_1543202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543202 prefixEnd_1543202 := by exact prefixLift 1543202
  have htrace : WordTrace (prefixWord ++ tailWord_1543202) baseStart_1543202 baseEnd_1543202 := by
    simpa [prefixWord, tailWord_1543202, baseEnd_1543202] using wordTrace_append hprefix tailTrace_1543202
  have hstable : (prefixWord ++ tailWord_1543202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543202).length < 2 ^ (prefixWord ++ tailWord_1543202).sum := by decide
  have hdescent : baseEnd_1543202 < baseStart_1543202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543245 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_1543245 : Nat := 118140960795 + 1543245 * 2 ^ 59
def prefixEnd_1543245 : Nat := 4983230072969 + 3 ^ 40 * 1543245 * 2
def baseEnd_1543245 : Nat := 528284301765279853693501

theorem tailTrace_1543245 : CollatzResearch.WordTrace tailWord_1543245 prefixEnd_1543245 528284301765279853693501 := by
  unfold tailWord_1543245
  simp only [CollatzResearch.WordTrace]
  refine ⟨56286769294094405107607189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37524512862729603405071459 56286769294094405107607189)
  ·
    refine ⟨2638442310660675239419087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56286769294094405107607189 2638442310660675239419087)
    ·
      refine ⟨3957663465991012859128631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2638442310660675239419087 3957663465991012859128631)
      ·
        refine ⟨5936495198986519288692947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3957663465991012859128631 5936495198986519288692947)
        ·
          refine ⟨8904742798479778933039421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5936495198986519288692947 8904742798479778933039421)
          ·
            refine ⟨3339278549429917099889783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8904742798479778933039421 3339278549429917099889783)
            ·
              refine ⟨5008917824144875649834675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339278549429917099889783 5008917824144875649834675)
              ·
                refine ⟨7513376736217313474752013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5008917824144875649834675 7513376736217313474752013)
                ·
                  refine ⟨2817516276081492553032005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7513376736217313474752013 2817516276081492553032005)
                  ·
                    refine ⟨528284301765279853693501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2817516276081492553032005 528284301765279853693501)
                    ·
                      rfl

theorem cell22_1543245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_1543245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543245 prefixEnd_1543245 := by exact prefixLift 1543245
  have htrace : WordTrace (prefixWord ++ tailWord_1543245) baseStart_1543245 baseEnd_1543245 := by
    simpa [prefixWord, tailWord_1543245, baseEnd_1543245] using wordTrace_append hprefix tailTrace_1543245
  have hstable : (prefixWord ++ tailWord_1543245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543245).length < 2 ^ (prefixWord ++ tailWord_1543245).sum := by decide
  have hdescent : baseEnd_1543245 < baseStart_1543245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543258 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 4, 3]
def baseStart_1543258 : Nat := 118140960795 + 1543258 * 2 ^ 59
def prefixEnd_1543258 : Nat := 4983230072969 + 3 ^ 40 * 1543258 * 2
def baseEnd_1543258 : Nat := 528288751930952153118461

theorem tailTrace_1543258 : CollatzResearch.WordTrace tailWord_1543258 prefixEnd_1543258 528288751930952153118461 := by
  unfold tailWord_1543258
  simp only [CollatzResearch.WordTrace]
  refine ⟨14071810860761827081957607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37524828962031538885220285 14071810860761827081957607)
  ·
    refine ⟨21107716291142740622936411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14071810860761827081957607 21107716291142740622936411)
    ·
      refine ⟨31661574436714110934404617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21107716291142740622936411 31661574436714110934404617)
      ·
        refine ⟨23746180827535583200803463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31661574436714110934404617 23746180827535583200803463)
        ·
          refine ⟨35619271241303374801205195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23746180827535583200803463 35619271241303374801205195)
          ·
            refine ⟨53428906861955062201807793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35619271241303374801205195 53428906861955062201807793)
            ·
              refine ⟨40071680146466296651355845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 53428906861955062201807793 40071680146466296651355845)
              ·
                refine ⟨7513440027462430622129221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40071680146466296651355845 7513440027462430622129221)
                ·
                  refine ⟨1408770005149205741649229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7513440027462430622129221 1408770005149205741649229)
                  ·
                    refine ⟨528288751930952153118461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1408770005149205741649229 528288751930952153118461)
                    ·
                      rfl

theorem cell22_1543258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_1543258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543258 prefixEnd_1543258 := by exact prefixLift 1543258
  have htrace : WordTrace (prefixWord ++ tailWord_1543258) baseStart_1543258 baseEnd_1543258 := by
    simpa [prefixWord, tailWord_1543258, baseEnd_1543258] using wordTrace_append hprefix tailTrace_1543258
  have hstable : (prefixWord ++ tailWord_1543258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543258).length < 2 ^ (prefixWord ++ tailWord_1543258).sum := by decide
  have hdescent : baseEnd_1543258 < baseStart_1543258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543260 : List Nat := [2, 2, 4, 1, 1, 1, 2, 5, 4]
def baseStart_1543260 : Nat := 118140960795 + 1543260 * 2 ^ 59
def prefixEnd_1543260 : Nat := 4983230072969 + 3 ^ 40 * 1543260 * 2
def baseEnd_1543260 : Nat := 176096478857274938189485

theorem tailTrace_1543260 : CollatzResearch.WordTrace tailWord_1543260 prefixEnd_1543260 176096478857274938189485 := by
  unfold tailWord_1543260
  simp only [CollatzResearch.WordTrace]
  refine ⟨28143658194520031334701617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37524877592693375112935489 28143658194520031334701617)
  ·
    refine ⟨21107743645890023501026213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28143658194520031334701617 21107743645890023501026213)
    ·
      refine ⟨3957701933604379406442415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21107743645890023501026213 3957701933604379406442415)
      ·
        refine ⟨5936552900406569109663623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3957701933604379406442415 5936552900406569109663623)
        ·
          refine ⟨8904829350609853664495435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5936552900406569109663623 8904829350609853664495435)
          ·
            refine ⟨13357244025914780496743153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8904829350609853664495435 13357244025914780496743153)
            ·
              refine ⟨10017933019436085372557365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13357244025914780496743153 10017933019436085372557365)
              ·
                refine ⟨939181220572133003677253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10017933019436085372557365 939181220572133003677253)
                ·
                  refine ⟨176096478857274938189485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939181220572133003677253 176096478857274938189485)
                  ·
                    rfl

theorem cell22_1543260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 5, 4].length) (baseStart_1543260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543260 prefixEnd_1543260 := by exact prefixLift 1543260
  have htrace : WordTrace (prefixWord ++ tailWord_1543260) baseStart_1543260 baseEnd_1543260 := by
    simpa [prefixWord, tailWord_1543260, baseEnd_1543260] using wordTrace_append hprefix tailTrace_1543260
  have hstable : (prefixWord ++ tailWord_1543260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543260).length < 2 ^ (prefixWord ++ tailWord_1543260).sum := by decide
  have hdescent : baseEnd_1543260 < baseStart_1543260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543271 : List Nat := [1, 1, 5, 1, 1, 13]
def baseStart_1543271 : Nat := 118140960795 + 1543271 * 2 ^ 59
def prefixEnd_1543271 : Nat := 4983230072969 + 3 ^ 40 * 1543271 * 2
def baseEnd_1543271 : Nat := 6522138297489190772141

theorem tailTrace_1543271 : CollatzResearch.WordTrace tailWord_1543271 prefixEnd_1543271 6522138297489190772141 := by
  unfold tailWord_1543271
  simp only [CollatzResearch.WordTrace]
  refine ⟨56287717592000211548053667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37525145061333474365369111 56287717592000211548053667)
  ·
    refine ⟨84431576388000317322080501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56287717592000211548053667 84431576388000317322080501)
    ·
      refine ⟨7915460286375029748945047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 84431576388000317322080501 7915460286375029748945047)
      ·
        refine ⟨11873190429562544623417571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7915460286375029748945047 11873190429562544623417571)
        ·
          refine ⟨17809785644343816935126357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11873190429562544623417571 17809785644343816935126357)
          ·
            refine ⟨6522138297489190772141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 17809785644343816935126357 6522138297489190772141)
            ·
              rfl

theorem cell22_1543271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 13].length) (baseStart_1543271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543271 prefixEnd_1543271 := by exact prefixLift 1543271
  have htrace : WordTrace (prefixWord ++ tailWord_1543271) baseStart_1543271 baseEnd_1543271 := by
    simpa [prefixWord, tailWord_1543271, baseEnd_1543271] using wordTrace_append hprefix tailTrace_1543271
  have hstable : (prefixWord ++ tailWord_1543271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543271).length < 2 ^ (prefixWord ++ tailWord_1543271).sum := by decide
  have hdescent : baseEnd_1543271 < baseStart_1543271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543273 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 2, 4]
def baseStart_1543273 : Nat := 118140960795 + 1543273 * 2 ^ 59
def prefixEnd_1543273 : Nat := 4983230072969 + 3 ^ 40 * 1543273 * 2
def baseEnd_1543273 : Nat := 528293886737497113993415

theorem tailTrace_1543273 : CollatzResearch.WordTrace tailWord_1543273 prefixEnd_1543273 528293886737497113993415 := by
  unfold tailWord_1543273
  simp only [CollatzResearch.WordTrace]
  refine ⟨56287790537992965889626473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37525193691995310593084315 56287790537992965889626473)
  ·
    refine ⟨42215842903494724417219855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56287790537992965889626473 42215842903494724417219855)
    ·
      refine ⟨63323764355242086625829783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42215842903494724417219855 63323764355242086625829783)
      ·
        refine ⟨94985646532863129938744675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63323764355242086625829783 94985646532863129938744675)
        ·
          refine ⟨142478469799294694908117013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 94985646532863129938744675 142478469799294694908117013)
          ·
            refine ⟨6678678271841938823817985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 142478469799294694908117013 6678678271841938823817985)
            ·
              refine ⟨5009008703881454117863489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6678678271841938823817985 5009008703881454117863489)
              ·
                refine ⟨3756756527911090588397617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5009008703881454117863489 3756756527911090588397617)
                ·
                  refine ⟨2817567395933317941298213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3756756527911090588397617 2817567395933317941298213)
                  ·
                    refine ⟨528293886737497113993415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2817567395933317941298213 528293886737497113993415)
                    ·
                      rfl

theorem cell22_1543273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2, 4].length) (baseStart_1543273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543273 prefixEnd_1543273 := by exact prefixLift 1543273
  have htrace : WordTrace (prefixWord ++ tailWord_1543273) baseStart_1543273 baseEnd_1543273 := by
    simpa [prefixWord, tailWord_1543273, baseEnd_1543273] using wordTrace_append hprefix tailTrace_1543273
  have hstable : (prefixWord ++ tailWord_1543273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543273).length < 2 ^ (prefixWord ++ tailWord_1543273).sum := by decide
  have hdescent : baseEnd_1543273 < baseStart_1543273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543277 : List Nat := [1, 5, 1, 1, 2, 2, 4, 2, 4]
def baseStart_1543277 : Nat := 118140960795 + 1543277 * 2 ^ 59
def prefixEnd_1543277 : Nat := 4983230072969 + 3 ^ 40 * 1543277 * 2
def baseEnd_1543277 : Nat := 176098418673080812297801

theorem tailTrace_1543277 : CollatzResearch.WordTrace tailWord_1543277 prefixEnd_1543277 176098418673080812297801 := by
  unfold tailWord_1543277
  simp only [CollatzResearch.WordTrace]
  refine ⟨56287936429978474572772085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37525290953318983048514723 56287936429978474572772085)
  ·
    refine ⟨5276994040310481991197383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 56287936429978474572772085 5276994040310481991197383)
    ·
      refine ⟨7915491060465722986796075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5276994040310481991197383 7915491060465722986796075)
      ·
        refine ⟨11873236590698584480194113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7915491060465722986796075 11873236590698584480194113)
        ·
          refine ⟨8904927443023938360145585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11873236590698584480194113 8904927443023938360145585)
          ·
            refine ⟨6678695582267953770109189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8904927443023938360145585 6678695582267953770109189)
            ·
              refine ⟨1252255421675241331895473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6678695582267953770109189 1252255421675241331895473)
              ·
                refine ⟨939191566256430998921605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252255421675241331895473 939191566256430998921605)
                ·
                  refine ⟨176098418673080812297801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939191566256430998921605 176098418673080812297801)
                  ·
                    rfl

theorem cell22_1543277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_1543277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543277 prefixEnd_1543277 := by exact prefixLift 1543277
  have htrace : WordTrace (prefixWord ++ tailWord_1543277) baseStart_1543277 baseEnd_1543277 := by
    simpa [prefixWord, tailWord_1543277, baseEnd_1543277] using wordTrace_append hprefix tailTrace_1543277
  have hstable : (prefixWord ++ tailWord_1543277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543277).length < 2 ^ (prefixWord ++ tailWord_1543277).sum := by decide
  have hdescent : baseEnd_1543277 < baseStart_1543277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543294 : List Nat := [4, 2, 4, 1, 1, 1, 1, 2, 6]
def baseStart_1543294 : Nat := 118140960795 + 1543294 * 2 ^ 59
def prefixEnd_1543294 : Nat := 4983230072969 + 3 ^ 40 * 1543294 * 2
def baseEnd_1543294 : Nat := 176100358488886686406117

theorem tailTrace_1543294 : CollatzResearch.WordTrace tailWord_1543294 prefixEnd_1543294 176100358488886686406117 := by
  unfold tailWord_1543294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7036069558864610809517617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37525704313944590984093957 7036069558864610809517617)
  ·
    refine ⟨5277052169148458107138213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7036069558864610809517617 5277052169148458107138213)
    ·
      refine ⟨989447281715335895088415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5277052169148458107138213 989447281715335895088415)
      ·
        refine ⟨1484170922573003842632623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 989447281715335895088415 1484170922573003842632623)
        ·
          refine ⟨2226256383859505763948935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1484170922573003842632623 2226256383859505763948935)
          ·
            refine ⟨3339384575789258645923403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2226256383859505763948935 3339384575789258645923403)
            ·
              refine ⟨5009076863683887968885105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339384575789258645923403 5009076863683887968885105)
              ·
                refine ⟨3756807647762915976663829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5009076863683887968885105 3756807647762915976663829)
                ·
                  refine ⟨176100358488886686406117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3756807647762915976663829 176100358488886686406117)
                  ·
                    rfl

theorem cell22_1543294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_1543294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543294 prefixEnd_1543294 := by exact prefixLift 1543294
  have htrace : WordTrace (prefixWord ++ tailWord_1543294) baseStart_1543294 baseEnd_1543294 := by
    simpa [prefixWord, tailWord_1543294, baseEnd_1543294] using wordTrace_append hprefix tailTrace_1543294
  have hstable : (prefixWord ++ tailWord_1543294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543294).length < 2 ^ (prefixWord ++ tailWord_1543294).sum := by decide
  have hdescent : baseEnd_1543294 < baseStart_1543294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543333 : List Nat := [1, 3, 1, 2, 1, 5, 1, 1, 7]
def baseStart_1543333 : Nat := 118140960795 + 1543333 * 2 ^ 59
def prefixEnd_1543333 : Nat := 4983230072969 + 3 ^ 40 * 1543333 * 2
def baseEnd_1543333 : Nat := 176104808654558985831077

theorem tailTrace_1543333 : CollatzResearch.WordTrace tailWord_1543333 prefixEnd_1543333 176104808654558985831077 := by
  unfold tailWord_1543333
  simp only [CollatzResearch.WordTrace]
  refine ⟨56289978917775596136810653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37526652611850397424540435 56289978917775596136810653)
  ·
    refine ⟨21108742094165848551303995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56289978917775596136810653 21108742094165848551303995)
    ·
      refine ⟨31663113141248772826955993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21108742094165848551303995 31663113141248772826955993)
      ·
        refine ⟨23747334855936579620216995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31663113141248772826955993 23747334855936579620216995)
        ·
          refine ⟨35621002283904869430325493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23747334855936579620216995 35621002283904869430325493)
          ·
            refine ⟨3339468964116081509093015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 35621002283904869430325493 3339468964116081509093015)
            ·
              refine ⟨5009203446174122263639523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3339468964116081509093015 5009203446174122263639523)
              ·
                refine ⟨7513805169261183395459285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5009203446174122263639523 7513805169261183395459285)
                ·
                  refine ⟨176104808654558985831077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7513805169261183395459285 176104808654558985831077)
                  ·
                    rfl

theorem cell22_1543333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 1, 7].length) (baseStart_1543333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543333 prefixEnd_1543333 := by exact prefixLift 1543333
  have htrace : WordTrace (prefixWord ++ tailWord_1543333) baseStart_1543333 baseEnd_1543333 := by
    simpa [prefixWord, tailWord_1543333, baseEnd_1543333] using wordTrace_append hprefix tailTrace_1543333
  have hstable : (prefixWord ++ tailWord_1543333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543333).length < 2 ^ (prefixWord ++ tailWord_1543333).sum := by decide
  have hdescent : baseEnd_1543333 < baseStart_1543333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543423 : List Nat := [1, 1, 2, 2, 1, 5, 2, 8]
def baseStart_1543423 : Nat := 118140960795 + 1543423 * 2 ^ 59
def prefixEnd_1543423 : Nat := 4983230072969 + 3 ^ 40 * 1543423 * 2
def baseEnd_1543423 : Nat := 58705026089216302526995

theorem tailTrace_1543423 : CollatzResearch.WordTrace tailWord_1543423 prefixEnd_1543423 58705026089216302526995 := by
  unfold tailWord_1543423
  simp only [CollatzResearch.WordTrace]
  refine ⟨56293261487449541507586923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37528840991633027671724615 56293261487449541507586923)
  ·
    refine ⟨84439892231174312261380385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56293261487449541507586923 84439892231174312261380385)
    ·
      refine ⟨63329919173380734196035289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84439892231174312261380385 63329919173380734196035289)
      ·
        refine ⟨47497439380035550647026467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63329919173380734196035289 47497439380035550647026467)
        ·
          refine ⟨71246159070053325970539701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47497439380035550647026467 71246159070053325970539701)
          ·
            refine ⟨6679327412817499309738097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 71246159070053325970539701 6679327412817499309738097)
            ·
              refine ⟨5009495559613124482303573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6679327412817499309738097 5009495559613124482303573)
              ·
                refine ⟨58705026089216302526995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5009495559613124482303573 58705026089216302526995)
                ·
                  rfl

theorem cell22_1543423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 8].length) (baseStart_1543423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543423 prefixEnd_1543423 := by exact prefixLift 1543423
  have htrace : WordTrace (prefixWord ++ tailWord_1543423) baseStart_1543423 baseEnd_1543423 := by
    simpa [prefixWord, tailWord_1543423, baseEnd_1543423] using wordTrace_append hprefix tailTrace_1543423
  have hstable : (prefixWord ++ tailWord_1543423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543423).length < 2 ^ (prefixWord ++ tailWord_1543423).sum := by decide
  have hdescent : baseEnd_1543423 < baseStart_1543423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543425 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 2, 4]
def baseStart_1543425 : Nat := 118140960795 + 1543425 * 2 ^ 59
def prefixEnd_1543425 : Nat := 4983230072969 + 3 ^ 40 * 1543425 * 2
def baseEnd_1543425 : Nat := 528345919443819384192949

theorem tailTrace_1543425 : CollatzResearch.WordTrace tailWord_1543425 prefixEnd_1543425 528345919443819384192949 := by
  unfold tailWord_1543425
  simp only [CollatzResearch.WordTrace]
  refine ⟨56293334433442295849159729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37528889622294863899439819 56293334433442295849159729)
  ·
    refine ⟨42220000825081721886869797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56293334433442295849159729 42220000825081721886869797)
    ·
      refine ⟨7916250154702822853788087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42220000825081721886869797 7916250154702822853788087)
      ·
        refine ⟨11874375232054234280682131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7916250154702822853788087 11874375232054234280682131)
        ·
          refine ⟨17811562848081351421023197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11874375232054234280682131 17811562848081351421023197)
          ·
            refine ⟨6679336068030506782883699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17811562848081351421023197 6679336068030506782883699)
            ·
              refine ⟨10019004102045760174325549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6679336068030506782883699 10019004102045760174325549)
              ·
                refine ⟨3757126538267160065372081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10019004102045760174325549 3757126538267160065372081)
                ·
                  refine ⟨2817844903700370049029061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3757126538267160065372081 2817844903700370049029061)
                  ·
                    refine ⟨528345919443819384192949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2817844903700370049029061 528345919443819384192949)
                    ·
                      rfl

theorem cell22_1543425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_1543425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543425 prefixEnd_1543425 := by exact prefixLift 1543425
  have htrace : WordTrace (prefixWord ++ tailWord_1543425) baseStart_1543425 baseEnd_1543425 := by
    simpa [prefixWord, tailWord_1543425, baseEnd_1543425] using wordTrace_append hprefix tailTrace_1543425
  have hstable : (prefixWord ++ tailWord_1543425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543425).length < 2 ^ (prefixWord ++ tailWord_1543425).sum := by decide
  have hdescent : baseEnd_1543425 < baseStart_1543425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543468 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 9]
def baseStart_1543468 : Nat := 118140960795 + 1543468 * 2 ^ 59
def prefixEnd_1543468 : Nat := 4983230072969 + 3 ^ 40 * 1543468 * 2
def baseEnd_1543468 : Nat := 176120213074193868455939

theorem tailTrace_1543468 : CollatzResearch.WordTrace tailWord_1543468 prefixEnd_1543468 176120213074193868455939 := by
  unfold tailWord_1543468
  simp only [CollatzResearch.WordTrace]
  refine ⟨28147451386143257096487529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37529935181524342795316705 28147451386143257096487529)
  ·
    refine ⟨21110588539607442822365647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28147451386143257096487529 21110588539607442822365647)
    ·
      refine ⟨31665882809411164233548471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21110588539607442822365647 31665882809411164233548471)
      ·
        refine ⟨47498824214116746350322707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31665882809411164233548471 47498824214116746350322707)
        ·
          refine ⟨71248236321175119525484061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47498824214116746350322707 71248236321175119525484061)
          ·
            refine ⟨26718088620440669822056523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 71248236321175119525484061 26718088620440669822056523)
            ·
              refine ⟨40077132930661004733084785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26718088620440669822056523 40077132930661004733084785)
              ·
                refine ⟨30057849697995753549813589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40077132930661004733084785 30057849697995753549813589)
                ·
                  refine ⟨176120213074193868455939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30057849697995753549813589 176120213074193868455939)
                  ·
                    rfl

theorem cell22_1543468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_1543468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543468 prefixEnd_1543468 := by exact prefixLift 1543468
  have htrace : WordTrace (prefixWord ++ tailWord_1543468) baseStart_1543468 baseEnd_1543468 := by
    simpa [prefixWord, tailWord_1543468, baseEnd_1543468] using wordTrace_append hprefix tailTrace_1543468
  have hstable : (prefixWord ++ tailWord_1543468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543468).length < 2 ^ (prefixWord ++ tailWord_1543468).sum := by decide
  have hdescent : baseEnd_1543468 < baseStart_1543468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543500 : List Nat := [2, 2, 1, 3, 2, 2, 1, 2, 2, 5]
def baseStart_1543500 : Nat := 118140960795 + 1543500 * 2 ^ 59
def prefixEnd_1543500 : Nat := 4983230072969 + 3 ^ 40 * 1543500 * 2
def baseEnd_1543500 : Nat := 528371593476544188567719

theorem tailTrace_1543500 : CollatzResearch.WordTrace tailWord_1543500 prefixEnd_1543500 528371593476544188567719 := by
  unfold tailWord_1543500
  simp only [CollatzResearch.WordTrace]
  refine ⟨28148034954085291829069977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37530713272113722438759969 28148034954085291829069977)
  ·
    refine ⟨21111026215563968871802483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28148034954085291829069977 21111026215563968871802483)
    ·
      refine ⟨31666539323345953307703725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21111026215563968871802483 31666539323345953307703725)
      ·
        refine ⟨11874952246254732490388897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31666539323345953307703725 11874952246254732490388897)
        ·
          refine ⟨8906214184691049367791673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11874952246254732490388897 8906214184691049367791673)
          ·
            refine ⟨6679660638518287025843755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8906214184691049367791673 6679660638518287025843755)
            ·
              refine ⟨10019490957777430538765633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6679660638518287025843755 10019490957777430538765633)
              ·
                refine ⟨7514618218333072904074225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10019490957777430538765633 7514618218333072904074225)
                ·
                  refine ⟨5635963663749804678055669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7514618218333072904074225 5635963663749804678055669)
                  ·
                    refine ⟨528371593476544188567719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5635963663749804678055669 528371593476544188567719)
                    ·
                      rfl

theorem cell22_1543500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_1543500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543500 prefixEnd_1543500 := by exact prefixLift 1543500
  have htrace : WordTrace (prefixWord ++ tailWord_1543500) baseStart_1543500 baseEnd_1543500 := by
    simpa [prefixWord, tailWord_1543500, baseEnd_1543500] using wordTrace_append hprefix tailTrace_1543500
  have hstable : (prefixWord ++ tailWord_1543500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543500).length < 2 ^ (prefixWord ++ tailWord_1543500).sum := by decide
  have hdescent : baseEnd_1543500 < baseStart_1543500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543532 : List Nat := [2, 2, 1, 1, 5, 1, 1, 4, 1, 4]
def baseStart_1543532 : Nat := 118140960795 + 1543532 * 2 ^ 59
def prefixEnd_1543532 : Nat := 4983230072969 + 3 ^ 40 * 1543532 * 2
def baseEnd_1543532 : Nat := 528382547730506771767621

theorem tailTrace_1543532 : CollatzResearch.WordTrace tailWord_1543532 prefixEnd_1543532 528382547730506771767621 := by
  unfold tailWord_1543532
  simp only [CollatzResearch.WordTrace]
  refine ⟨28148618522027326561652425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37531491362703102082203233 28148618522027326561652425)
  ·
    refine ⟨21111463891520494921239319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28148618522027326561652425 21111463891520494921239319)
    ·
      refine ⟨31667195837280742381858979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21111463891520494921239319 31667195837280742381858979)
      ·
        refine ⟨47500793755921113572788469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31667195837280742381858979 47500793755921113572788469)
        ·
          refine ⟨4453199414617604397448919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 47500793755921113572788469 4453199414617604397448919)
          ·
            refine ⟨6679799121926406596173379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4453199414617604397448919 6679799121926406596173379)
            ·
              refine ⟨10019698682889609894260069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6679799121926406596173379 10019698682889609894260069)
              ·
                refine ⟨1878693503041801855173763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10019698682889609894260069 1878693503041801855173763)
                ·
                  refine ⟨2818040254562702782760645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1878693503041801855173763 2818040254562702782760645)
                  ·
                    refine ⟨528382547730506771767621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2818040254562702782760645 528382547730506771767621)
                    ·
                      rfl

theorem cell22_1543532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_1543532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543532 prefixEnd_1543532 := by exact prefixLift 1543532
  have htrace : WordTrace (prefixWord ++ tailWord_1543532) baseStart_1543532 baseEnd_1543532 := by
    simpa [prefixWord, tailWord_1543532, baseEnd_1543532] using wordTrace_append hprefix tailTrace_1543532
  have hstable : (prefixWord ++ tailWord_1543532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543532).length < 2 ^ (prefixWord ++ tailWord_1543532).sum := by decide
  have hdescent : baseEnd_1543532 < baseStart_1543532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543545 : List Nat := [1, 2, 1, 3, 2, 1, 2, 4, 1, 5]
def baseStart_1543545 : Nat := 118140960795 + 1543545 * 2 ^ 59
def prefixEnd_1543545 : Nat := 4983230072969 + 3 ^ 40 * 1543545 * 2
def baseEnd_1543545 : Nat := 528386997896179071192581

theorem tailTrace_1543545 : CollatzResearch.WordTrace tailWord_1543545 prefixEnd_1543545 528386997896179071192581 := by
  unfold tailWord_1543545
  simp only [CollatzResearch.WordTrace]
  refine ⟨56297711193007556343528089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37531807462005037562352059 56297711193007556343528089)
  ·
    refine ⟨42223283394755667257646067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56297711193007556343528089 42223283394755667257646067)
    ·
      refine ⟨63334925092133500886469101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42223283394755667257646067 63334925092133500886469101)
      ·
        refine ⟨23750596909550062832425913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63334925092133500886469101 23750596909550062832425913)
        ·
          refine ⟨17812947682162547124319435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23750596909550062832425913 17812947682162547124319435)
          ·
            refine ⟨26719421523243820686479153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17812947682162547124319435 26719421523243820686479153)
            ·
              refine ⟨20039566142432865514859365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26719421523243820686479153 20039566142432865514859365)
              ·
                refine ⟨3757418651706162284036131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20039566142432865514859365 3757418651706162284036131)
                ·
                  refine ⟨5636127977559243426054197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3757418651706162284036131 5636127977559243426054197)
                  ·
                    refine ⟨528386997896179071192581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5636127977559243426054197 528386997896179071192581)
                    ·
                      rfl

theorem cell22_1543545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_1543545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543545 prefixEnd_1543545 := by exact prefixLift 1543545
  have htrace : WordTrace (prefixWord ++ tailWord_1543545) baseStart_1543545 baseEnd_1543545 := by
    simpa [prefixWord, tailWord_1543545, baseEnd_1543545] using wordTrace_append hprefix tailTrace_1543545
  have hstable : (prefixWord ++ tailWord_1543545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543545).length < 2 ^ (prefixWord ++ tailWord_1543545).sum := by decide
  have hdescent : baseEnd_1543545 < baseStart_1543545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543564 : List Nat := [2, 2, 1, 2, 1, 3, 5, 2, 4]
def baseStart_1543564 : Nat := 118140960795 + 1543564 * 2 ^ 59
def prefixEnd_1543564 : Nat := 4983230072969 + 3 ^ 40 * 1543564 * 2
def baseEnd_1543564 : Nat := 176131167328156451655841

theorem tailTrace_1543564 : CollatzResearch.WordTrace tailWord_1543564 prefixEnd_1543564 176131167328156451655841 := by
  unfold tailWord_1543564
  simp only [CollatzResearch.WordTrace]
  refine ⟨28149202089969361294234873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37532269453292481725646497 28149202089969361294234873)
  ·
    refine ⟨21111901567477020970676155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28149202089969361294234873 21111901567477020970676155)
    ·
      refine ⟨31667852351215531456014233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21111901567477020970676155 31667852351215531456014233)
      ·
        refine ⟨23750889263411648592010675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31667852351215531456014233 23750889263411648592010675)
        ·
          refine ⟨35626333895117472888016013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23750889263411648592010675 35626333895117472888016013)
          ·
            refine ⟨13359875210669052333006005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 35626333895117472888016013 13359875210669052333006005)
            ·
              refine ⟨1252488301000223656219313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13359875210669052333006005 1252488301000223656219313)
              ·
                refine ⟨939366225750167742164485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252488301000223656219313 939366225750167742164485)
                ·
                  refine ⟨176131167328156451655841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939366225750167742164485 176131167328156451655841)
                  ·
                    rfl

theorem cell22_1543564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 5, 2, 4].length) (baseStart_1543564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543564 prefixEnd_1543564 := by exact prefixLift 1543564
  have htrace : WordTrace (prefixWord ++ tailWord_1543564) baseStart_1543564 baseEnd_1543564 := by
    simpa [prefixWord, tailWord_1543564, baseEnd_1543564] using wordTrace_append hprefix tailTrace_1543564
  have hstable : (prefixWord ++ tailWord_1543564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543564).length < 2 ^ (prefixWord ++ tailWord_1543564).sum := by decide
  have hdescent : baseEnd_1543564 < baseStart_1543564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543637 : List Nat := [1, 3, 2, 3, 1, 1, 1, 5, 5]
def baseStart_1543637 : Nat := 118140960795 + 1543637 * 2 ^ 59
def prefixEnd_1543637 : Nat := 4983230072969 + 3 ^ 40 * 1543637 * 2
def baseEnd_1543637 : Nat := 176139497125440499297433

theorem tailTrace_1543637 : CollatzResearch.WordTrace tailWord_1543637 prefixEnd_1543637 176139497125440499297433 := by
  unfold tailWord_1543637
  simp only [CollatzResearch.WordTrace]
  refine ⟨56301066708674256055877165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37534044472449504037251443 56301066708674256055877165)
  ·
    refine ⟨21112900015752846020953937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56301066708674256055877165 21112900015752846020953937)
    ·
      refine ⟨15834675011814634515715453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21112900015752846020953937 15834675011814634515715453)
      ·
        refine ⟨5938003129430487943393295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15834675011814634515715453 5938003129430487943393295)
        ·
          refine ⟨8907004694145731915089943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5938003129430487943393295 8907004694145731915089943)
          ·
            refine ⟨13360507041218597872634915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8907004694145731915089943 13360507041218597872634915)
            ·
              refine ⟨20040760561827896808952373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13360507041218597872634915 20040760561827896808952373)
              ·
                refine ⟨1878821302671365325839285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20040760561827896808952373 1878821302671365325839285)
                ·
                  refine ⟨176139497125440499297433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1878821302671365325839285 176139497125440499297433)
                  ·
                    rfl

theorem cell22_1543637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_1543637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543637 prefixEnd_1543637 := by exact prefixLift 1543637
  have htrace : WordTrace (prefixWord ++ tailWord_1543637) baseStart_1543637 baseEnd_1543637 := by
    simpa [prefixWord, tailWord_1543637, baseEnd_1543637] using wordTrace_append hprefix tailTrace_1543637
  have hstable : (prefixWord ++ tailWord_1543637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543637).length < 2 ^ (prefixWord ++ tailWord_1543637).sum := by decide
  have hdescent : baseEnd_1543637 < baseStart_1543637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543658 : List Nat := [3, 1, 3, 1, 4, 1, 2, 3, 1, 3]
def baseStart_1543658 : Nat := 118140960795 + 1543658 * 2 ^ 59
def prefixEnd_1543658 : Nat := 4983230072969 + 3 ^ 40 * 1543658 * 2
def baseEnd_1543658 : Nat := 528425680105484443117235

theorem tailTrace_1543658 : CollatzResearch.WordTrace tailWord_1543658 prefixEnd_1543658 528425680105484443117235 := by
  unfold tailWord_1543658
  simp only [CollatzResearch.WordTrace]
  refine ⟨14075458160399544160597907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37534555094398784428261085 14075458160399544160597907)
  ·
    refine ⟨21113187240599316240896861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14075458160399544160597907 21113187240599316240896861)
    ·
      refine ⟨7917445215224743590336323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21113187240599316240896861 7917445215224743590336323)
      ·
        refine ⟨11876167822837115385504485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7917445215224743590336323 11876167822837115385504485)
        ·
          refine ⟨2226781466781959134782091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11876167822837115385504485 2226781466781959134782091)
          ·
            refine ⟨3340172200172938702173137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2226781466781959134782091 3340172200172938702173137)
            ·
              refine ⟨2505129150129704026629853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3340172200172938702173137 2505129150129704026629853)
              ·
                refine ⟨939423431298639009986195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2505129150129704026629853 939423431298639009986195)
                ·
                  refine ⟨1409135146947958514979293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 939423431298639009986195 1409135146947958514979293)
                  ·
                    refine ⟨528425680105484443117235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1409135146947958514979293 528425680105484443117235)
                    ·
                      rfl

theorem cell22_1543658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_1543658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543658 prefixEnd_1543658 := by exact prefixLift 1543658
  have htrace : WordTrace (prefixWord ++ tailWord_1543658) baseStart_1543658 baseEnd_1543658 := by
    simpa [prefixWord, tailWord_1543658, baseEnd_1543658] using wordTrace_append hprefix tailTrace_1543658
  have hstable : (prefixWord ++ tailWord_1543658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543658).length < 2 ^ (prefixWord ++ tailWord_1543658).sum := by decide
  have hdescent : baseEnd_1543658 < baseStart_1543658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543669 : List Nat := [1, 3, 5, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1543669 : Nat := 118140960795 + 1543669 * 2 ^ 59
def prefixEnd_1543669 : Nat := 4983230072969 + 3 ^ 40 * 1543669 * 2
def baseEnd_1543669 : Nat := 528429445630284081092201

theorem tailTrace_1543669 : CollatzResearch.WordTrace tailWord_1543669 prefixEnd_1543669 528429445630284081092201 := by
  unfold tailWord_1543669
  simp only [CollatzResearch.WordTrace]
  refine ⟨56302233844558325521042061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37534822563038883680694707 56302233844558325521042061)
  ·
    refine ⟨21113337691709372070390773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56302233844558325521042061 21113337691709372070390773)
    ·
      refine ⟨1979375408597753631599135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21113337691709372070390773 1979375408597753631599135)
      ·
        refine ⟨2969063112896630447398703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1979375408597753631599135 2969063112896630447398703)
        ·
          refine ⟨4453594669344945671098055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2969063112896630447398703 4453594669344945671098055)
          ·
            refine ⟨6680392004017418506647083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4453594669344945671098055 6680392004017418506647083)
            ·
              refine ⟨10020588006026127759970625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6680392004017418506647083 10020588006026127759970625)
              ·
                refine ⟨7515441004519595819977969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10020588006026127759970625 7515441004519595819977969)
                ·
                  refine ⟨5636580753389696864983477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7515441004519595819977969 5636580753389696864983477)
                  ·
                    refine ⟨528429445630284081092201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5636580753389696864983477 528429445630284081092201)
                    ·
                      rfl

theorem cell22_1543669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1543669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543669 prefixEnd_1543669 := by exact prefixLift 1543669
  have htrace : WordTrace (prefixWord ++ tailWord_1543669) baseStart_1543669 baseEnd_1543669 := by
    simpa [prefixWord, tailWord_1543669, baseEnd_1543669] using wordTrace_append hprefix tailTrace_1543669
  have hstable : (prefixWord ++ tailWord_1543669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543669).length < 2 ^ (prefixWord ++ tailWord_1543669).sum := by decide
  have hdescent : baseEnd_1543669 < baseStart_1543669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543680 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 1, 11]
def baseStart_1543680 : Nat := 118140960795 + 1543680 * 2 ^ 59
def prefixEnd_1543680 : Nat := 4983230072969 + 3 ^ 40 * 1543680 * 2
def baseEnd_1543680 : Nat := 528433211155083719067167

theorem tailTrace_1543680 : CollatzResearch.WordTrace tailWord_1543680 prefixEnd_1543680 528433211155083719067167 := by
  unfold tailWord_1543680
  simp only [CollatzResearch.WordTrace]
  refine ⟨28151317523759237199846247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37535090031678982933128329 28151317523759237199846247)
  ·
    refine ⟨42226976285638855799769371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28151317523759237199846247 42226976285638855799769371)
    ·
      refine ⟨63340464428458283699654057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42226976285638855799769371 63340464428458283699654057)
      ·
        refine ⟨47505348321343712774740543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 63340464428458283699654057 47505348321343712774740543)
        ·
          refine ⟨71258022482015569162110815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47505348321343712774740543 71258022482015569162110815)
          ·
            refine ⟨106887033723023353743166223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 71258022482015569162110815 106887033723023353743166223)
            ·
              refine ⟨160330550584535030614749335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 106887033723023353743166223 160330550584535030614749335)
              ·
                refine ⟨240495825876802545922124003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 160330550584535030614749335 240495825876802545922124003)
                ·
                  refine ⟨360743738815203818883186005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 240495825876802545922124003 360743738815203818883186005)
                  ·
                    refine ⟨528433211155083719067167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 360743738815203818883186005 528433211155083719067167)
                    ·
                      rfl

theorem cell22_1543680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 11].length) (baseStart_1543680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543680 prefixEnd_1543680 := by exact prefixLift 1543680
  have htrace : WordTrace (prefixWord ++ tailWord_1543680) baseStart_1543680 baseEnd_1543680 := by
    simpa [prefixWord, tailWord_1543680, baseEnd_1543680] using wordTrace_append hprefix tailTrace_1543680
  have hstable : (prefixWord ++ tailWord_1543680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543680).length < 2 ^ (prefixWord ++ tailWord_1543680).sum := by decide
  have hdescent : baseEnd_1543680 < baseStart_1543680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543714 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_1543714 : Nat := 118140960795 + 1543714 * 2 ^ 59
def prefixEnd_1543714 : Nat := 4983230072969 + 3 ^ 40 * 1543714 * 2
def baseEnd_1543714 : Nat := 528444850049918963717063

theorem tailTrace_1543714 : CollatzResearch.WordTrace tailWord_1543714 prefixEnd_1543714 528444850049918963717063 := by
  unfold tailWord_1543714
  simp only [CollatzResearch.WordTrace]
  refine ⟨14075968782348824551607549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37535916752930198804286797 14075968782348824551607549)
  ·
    refine ⟨5278488293380809206852831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14075968782348824551607549 5278488293380809206852831)
    ·
      refine ⟨7917732440071213810279247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5278488293380809206852831 7917732440071213810279247)
      ·
        refine ⟨11876598660106820715418871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7917732440071213810279247 11876598660106820715418871)
        ·
          refine ⟨17814897990160231073128307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11876598660106820715418871 17814897990160231073128307)
          ·
            refine ⟨26722346985240346609692461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17814897990160231073128307 26722346985240346609692461)
            ·
              refine ⟨10020880119465129978634673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26722346985240346609692461 10020880119465129978634673)
              ·
                refine ⟨7515660089598847483976005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10020880119465129978634673 7515660089598847483976005)
                ·
                  refine ⟨1409186266799783903245501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7515660089598847483976005 1409186266799783903245501)
                  ·
                    refine ⟨528444850049918963717063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1409186266799783903245501 528444850049918963717063)
                    ·
                      rfl

theorem cell22_1543714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_1543714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543714 prefixEnd_1543714 := by exact prefixLift 1543714
  have htrace : WordTrace (prefixWord ++ tailWord_1543714) baseStart_1543714 baseEnd_1543714 := by
    simpa [prefixWord, tailWord_1543714, baseEnd_1543714] using wordTrace_append hprefix tailTrace_1543714
  have hstable : (prefixWord ++ tailWord_1543714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543714).length < 2 ^ (prefixWord ++ tailWord_1543714).sum := by decide
  have hdescent : baseEnd_1543714 < baseStart_1543714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543776 : List Nat := [2, 1, 1, 3, 2, 1, 1, 7, 1, 3]
def baseStart_1543776 : Nat := 118140960795 + 1543776 * 2 ^ 59
def prefixEnd_1543776 : Nat := 4983230072969 + 3 ^ 40 * 1543776 * 2
def baseEnd_1543776 : Nat := 528466073916971468666873

theorem tailTrace_1543776 : CollatzResearch.WordTrace tailWord_1543776 prefixEnd_1543776 528466073916971468666873 := by
  unfold tailWord_1543776
  simp only [CollatzResearch.WordTrace]
  refine ⟨28153068227585341397593591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37537424303447121863458121 28153068227585341397593591)
  ·
    refine ⟨42229602341378012096390387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28153068227585341397593591 42229602341378012096390387)
    ·
      refine ⟨63344403512067018144585581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42229602341378012096390387 63344403512067018144585581)
      ·
        refine ⟨23754151317025131804219593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63344403512067018144585581 23754151317025131804219593)
        ·
          refine ⟨17815613487768848853164695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23754151317025131804219593 17815613487768848853164695)
          ·
            refine ⟨26723420231653273279747043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17815613487768848853164695 26723420231653273279747043)
            ·
              refine ⟨40085130347479909919620565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26723420231653273279747043 40085130347479909919620565)
              ·
                refine ⟨939495242519060388741107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 40085130347479909919620565 939495242519060388741107)
                ·
                  refine ⟨1409242863778590583111661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 939495242519060388741107 1409242863778590583111661)
                  ·
                    refine ⟨528466073916971468666873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1409242863778590583111661 528466073916971468666873)
                    ·
                      rfl

theorem cell22_1543776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 7, 1, 3].length) (baseStart_1543776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543776 prefixEnd_1543776 := by exact prefixLift 1543776
  have htrace : WordTrace (prefixWord ++ tailWord_1543776) baseStart_1543776 baseEnd_1543776 := by
    simpa [prefixWord, tailWord_1543776, baseEnd_1543776] using wordTrace_append hprefix tailTrace_1543776
  have hstable : (prefixWord ++ tailWord_1543776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543776).length < 2 ^ (prefixWord ++ tailWord_1543776).sum := by decide
  have hdescent : baseEnd_1543776 < baseStart_1543776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543817 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 8]
def baseStart_1543817 : Nat := 118140960795 + 1543817 * 2 ^ 59
def prefixEnd_1543817 : Nat := 4983230072969 + 3 ^ 40 * 1543817 * 2
def baseEnd_1543817 : Nat := 176160036351620342797249

theorem tailTrace_1543817 : CollatzResearch.WordTrace tailWord_1543817 prefixEnd_1543817 176160036351620342797249 := by
  unfold tailWord_1543817
  simp only [CollatzResearch.WordTrace]
  refine ⟨56307631848022146797429705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37538421232014764531619803 56307631848022146797429705)
  ·
    refine ⟨42230723886016610098072279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56307631848022146797429705 42230723886016610098072279)
    ·
      refine ⟨63346085829024915147108419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42230723886016610098072279 63346085829024915147108419)
      ·
        refine ⟨95019128743537372720662629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 63346085829024915147108419 95019128743537372720662629)
        ·
          refine ⟨17816086639413257385124243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 95019128743537372720662629 17816086639413257385124243)
          ·
            refine ⟨26724129959119886077686365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17816086639413257385124243 26724129959119886077686365)
            ·
              refine ⟨10021548734669957279132387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26724129959119886077686365 10021548734669957279132387)
              ·
                refine ⟨15032323102004935918698581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10021548734669957279132387 15032323102004935918698581)
                ·
                  refine ⟨176160036351620342797249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15032323102004935918698581 176160036351620342797249)
                  ·
                    rfl

theorem cell22_1543817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 8].length) (baseStart_1543817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543817 prefixEnd_1543817 := by exact prefixLift 1543817
  have htrace : WordTrace (prefixWord ++ tailWord_1543817) baseStart_1543817 baseEnd_1543817 := by
    simpa [prefixWord, tailWord_1543817, baseEnd_1543817] using wordTrace_append hprefix tailTrace_1543817
  have hstable : (prefixWord ++ tailWord_1543817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543817).length < 2 ^ (prefixWord ++ tailWord_1543817).sum := by decide
  have hdescent : baseEnd_1543817 < baseStart_1543817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543819 : List Nat := [1, 1, 1, 1, 4, 1, 4, 4, 1, 4]
def baseStart_1543819 : Nat := 118140960795 + 1543819 * 2 ^ 59
def prefixEnd_1543819 : Nat := 4983230072969 + 3 ^ 40 * 1543819 * 2
def baseEnd_1543819 : Nat := 528480793695733689841741

theorem tailTrace_1543819 : CollatzResearch.WordTrace tailWord_1543819 prefixEnd_1543819 528480793695733689841741 := by
  unfold tailWord_1543819
  simp only [CollatzResearch.WordTrace]
  refine ⟨56307704794014901139002511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37538469862676600759335007 56307704794014901139002511)
  ·
    refine ⟨84461557191022351708503767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56307704794014901139002511 84461557191022351708503767)
    ·
      refine ⟨126692335786533527562755651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84461557191022351708503767 126692335786533527562755651)
      ·
        refine ⟨190038503679800291344133477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 126692335786533527562755651 190038503679800291344133477)
        ·
          refine ⟨35632219439962554627025027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 190038503679800291344133477 35632219439962554627025027)
          ·
            refine ⟨53448329159943831940537541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35632219439962554627025027 53448329159943831940537541)
            ·
              refine ⟨10021561717489468488850789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53448329159943831940537541 10021561717489468488850789)
              ·
                refine ⟨1879042822029275341659523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10021561717489468488850789 1879042822029275341659523)
                ·
                  refine ⟨2818564233043913012489285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879042822029275341659523 2818564233043913012489285)
                  ·
                    refine ⟨528480793695733689841741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2818564233043913012489285 528480793695733689841741)
                    ·
                      rfl

theorem cell22_1543819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 1, 4].length) (baseStart_1543819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543819 prefixEnd_1543819 := by exact prefixLift 1543819
  have htrace : WordTrace (prefixWord ++ tailWord_1543819) baseStart_1543819 baseEnd_1543819 := by
    simpa [prefixWord, tailWord_1543819, baseEnd_1543819] using wordTrace_append hprefix tailTrace_1543819
  have hstable : (prefixWord ++ tailWord_1543819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543819).length < 2 ^ (prefixWord ++ tailWord_1543819).sum := by decide
  have hdescent : baseEnd_1543819 < baseStart_1543819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543866 : List Nat := [3, 1, 1, 1, 2, 6, 1, 1, 1, 5]
def baseStart_1543866 : Nat := 118140960795 + 1543866 * 2 ^ 59
def prefixEnd_1543866 : Nat := 4983230072969 + 3 ^ 40 * 1543866 * 2
def baseEnd_1543866 : Nat := 528496882756241233916597

theorem tailTrace_1543866 : CollatzResearch.WordTrace tailWord_1543866 prefixEnd_1543866 528496882756241233916597 := by
  unfold tailWord_1543866
  simp only [CollatzResearch.WordTrace]
  refine ⟨14077354756211157041490863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37539612683229752110642301 14077354756211157041490863)
  ·
    refine ⟨21116032134316735562236295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14077354756211157041490863 21116032134316735562236295)
    ·
      refine ⟨31674048201475103343354443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21116032134316735562236295 31674048201475103343354443)
      ·
        refine ⟨47511072302212655015031665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31674048201475103343354443 47511072302212655015031665)
        ·
          refine ⟨35633304226659491261273749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 47511072302212655015031665 35633304226659491261273749)
          ·
            refine ⟨1670311135624663652872207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 35633304226659491261273749 1670311135624663652872207)
            ·
              refine ⟨2505466703436995479308311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670311135624663652872207 2505466703436995479308311)
              ·
                refine ⟨3758200055155493218962467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2505466703436995479308311 3758200055155493218962467)
                ·
                  refine ⟨5637300082733239828443701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3758200055155493218962467 5637300082733239828443701)
                  ·
                    refine ⟨528496882756241233916597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5637300082733239828443701 528496882756241233916597)
                    ·
                      rfl

theorem cell22_1543866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_1543866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543866 prefixEnd_1543866 := by exact prefixLift 1543866
  have htrace : WordTrace (prefixWord ++ tailWord_1543866) baseStart_1543866 baseEnd_1543866 := by
    simpa [prefixWord, tailWord_1543866, baseEnd_1543866] using wordTrace_append hprefix tailTrace_1543866
  have hstable : (prefixWord ++ tailWord_1543866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543866).length < 2 ^ (prefixWord ++ tailWord_1543866).sum := by decide
  have hdescent : baseEnd_1543866 < baseStart_1543866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543885 : List Nat := [1, 6, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1543885 : Nat := 118140960795 + 1543885 * 2 ^ 59
def prefixEnd_1543885 : Nat := 4983230072969 + 3 ^ 40 * 1543885 * 2
def baseEnd_1543885 : Nat := 176167795614843839230513

theorem tailTrace_1543885 : CollatzResearch.WordTrace tailWord_1543885 prefixEnd_1543885 176167795614843839230513 := by
  unfold tailWord_1543885
  simp only [CollatzResearch.WordTrace]
  refine ⟨56310112011775794410905109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37540074674517196273936739 56310112011775794410905109)
  ·
    refine ⟨2639536500551990363011177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 56310112011775794410905109 2639536500551990363011177)
    ·
      refine ⟨1979652375413992772258383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2639536500551990363011177 1979652375413992772258383)
      ·
        refine ⟨2969478563120989158387575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1979652375413992772258383 2969478563120989158387575)
        ·
          refine ⟨4454217844681483737581363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2969478563120989158387575 4454217844681483737581363)
          ·
            refine ⟨6681326767022225606372045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4454217844681483737581363 6681326767022225606372045)
            ·
              refine ⟨2505497537633334602389517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6681326767022225606372045 2505497537633334602389517)
              ·
                refine ⟨939561576612500475896069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2505497537633334602389517 939561576612500475896069)
                ·
                  refine ⟨176167795614843839230513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939561576612500475896069 176167795614843839230513)
                  ·
                    rfl

theorem cell22_1543885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1543885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543885 prefixEnd_1543885 := by exact prefixLift 1543885
  have htrace : WordTrace (prefixWord ++ tailWord_1543885) baseStart_1543885 baseEnd_1543885 := by
    simpa [prefixWord, tailWord_1543885, baseEnd_1543885] using wordTrace_append hprefix tailTrace_1543885
  have hstable : (prefixWord ++ tailWord_1543885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543885).length < 2 ^ (prefixWord ++ tailWord_1543885).sum := by decide
  have hdescent : baseEnd_1543885 < baseStart_1543885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543909 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 2, 6]
def baseStart_1543909 : Nat := 118140960795 + 1543909 * 2 ^ 59
def prefixEnd_1543909 : Nat := 4983230072969 + 3 ^ 40 * 1543909 * 2
def baseEnd_1543909 : Nat := 528511602535003455091465

theorem tailTrace_1543909 : CollatzResearch.WordTrace tailWord_1543909 prefixEnd_1543909 528511602535003455091465 := by
  unfold tailWord_1543909
  simp only [CollatzResearch.WordTrace]
  refine ⟨56310987363688846509778781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37540658242459231006519187 56310987363688846509778781)
  ·
    refine ⟨21116620261383317441167043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56310987363688846509778781 21116620261383317441167043)
    ·
      refine ⟨31674930392074976161750565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21116620261383317441167043 31674930392074976161750565)
      ·
        refine ⟨5939049448514058030328231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31674930392074976161750565 5939049448514058030328231)
        ·
          refine ⟨8908574172771087045492347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5939049448514058030328231 8908574172771087045492347)
          ·
            refine ⟨13362861259156630568238521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8908574172771087045492347 13362861259156630568238521)
            ·
              refine ⟨10022145944367472926178891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13362861259156630568238521 10022145944367472926178891)
              ·
                refine ⟨15033218916551209389268337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10022145944367472926178891 15033218916551209389268337)
                ·
                  refine ⟨11274914187413407041951253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15033218916551209389268337 11274914187413407041951253)
                  ·
                    refine ⟨528511602535003455091465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11274914187413407041951253 528511602535003455091465)
                    ·
                      rfl

theorem cell22_1543909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_1543909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543909 prefixEnd_1543909 := by exact prefixLift 1543909
  have htrace : WordTrace (prefixWord ++ tailWord_1543909) baseStart_1543909 baseEnd_1543909 := by
    simpa [prefixWord, tailWord_1543909, baseEnd_1543909] using wordTrace_append hprefix tailTrace_1543909
  have hstable : (prefixWord ++ tailWord_1543909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543909).length < 2 ^ (prefixWord ++ tailWord_1543909).sum := by decide
  have hdescent : baseEnd_1543909 < baseStart_1543909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543962 : List Nat := [3, 1, 1, 3, 2, 4, 2, 2, 1, 3]
def baseStart_1543962 : Nat := 118140960795 + 1543962 * 2 ^ 59
def prefixEnd_1543962 : Nat := 4983230072969 + 3 ^ 40 * 1543962 * 2
def baseEnd_1543962 : Nat := 528529745518128983516303

theorem tailTrace_1543962 : CollatzResearch.WordTrace tailWord_1543962 prefixEnd_1543962 528529745518128983516303 := by
  unfold tailWord_1543962
  simp only [CollatzResearch.WordTrace]
  refine ⟨14078230108124209140364535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37541946954997891040972093 14078230108124209140364535)
  ·
    refine ⟨21117345162186313710546803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14078230108124209140364535 21117345162186313710546803)
    ·
      refine ⟨31676017743279470565820205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21117345162186313710546803 31676017743279470565820205)
      ·
        refine ⟨11878506653729801462182577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31676017743279470565820205 11878506653729801462182577)
        ·
          refine ⟨8908879990297351096636933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11878506653729801462182577 8908879990297351096636933)
          ·
            refine ⟨1670414998180753330619425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8908879990297351096636933 1670414998180753330619425)
            ·
              refine ⟨1252811248635564997964569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1670414998180753330619425 1252811248635564997964569)
              ·
                refine ⟨939608436476673748473427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1252811248635564997964569 939608436476673748473427)
                ·
                  refine ⟨1409412654715010622710141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 939608436476673748473427 1409412654715010622710141)
                  ·
                    refine ⟨528529745518128983516303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1409412654715010622710141 528529745518128983516303)
                    ·
                      rfl

theorem cell22_1543962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_1543962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543962 prefixEnd_1543962 := by exact prefixLift 1543962
  have htrace : WordTrace (prefixWord ++ tailWord_1543962) baseStart_1543962 baseEnd_1543962 := by
    simpa [prefixWord, tailWord_1543962, baseEnd_1543962] using wordTrace_append hprefix tailTrace_1543962
  have hstable : (prefixWord ++ tailWord_1543962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543962).length < 2 ^ (prefixWord ++ tailWord_1543962).sum := by decide
  have hdescent : baseEnd_1543962 < baseStart_1543962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543986 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 6]
def baseStart_1543986 : Nat := 118140960795 + 1543986 * 2 ^ 59
def prefixEnd_1543986 : Nat := 4983230072969 + 3 ^ 40 * 1543986 * 2
def baseEnd_1543986 : Nat := 176179320402866973638743

theorem tailTrace_1543986 : CollatzResearch.WordTrace tailWord_1543986 prefixEnd_1543986 176179320402866973638743 := by
  unfold tailWord_1543986
  simp only [CollatzResearch.WordTrace]
  refine ⟨14078448946102472165082953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37542530522939925773554541 14078448946102472165082953)
  ·
    refine ⟨10558836709576854123812215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14078448946102472165082953 10558836709576854123812215)
    ·
      refine ⟨15838255064365281185718323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10558836709576854123812215 15838255064365281185718323)
      ·
        refine ⟨23757382596547921778577485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15838255064365281185718323 23757382596547921778577485)
        ·
          refine ⟨8909018473705470666966557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23757382596547921778577485 8909018473705470666966557)
          ·
            refine ⟨3340881927639551500112459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8909018473705470666966557 3340881927639551500112459)
            ·
              refine ⟨5011322891459327250168689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3340881927639551500112459 5011322891459327250168689)
              ·
                refine ⟨3758492168594495437626517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5011322891459327250168689 3758492168594495437626517)
                ·
                  refine ⟨176179320402866973638743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3758492168594495437626517 176179320402866973638743)
                  ·
                    rfl

theorem cell22_1543986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_1543986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543986 prefixEnd_1543986 := by exact prefixLift 1543986
  have htrace : WordTrace (prefixWord ++ tailWord_1543986) baseStart_1543986 baseEnd_1543986 := by
    simpa [prefixWord, tailWord_1543986, baseEnd_1543986] using wordTrace_append hprefix tailTrace_1543986
  have hstable : (prefixWord ++ tailWord_1543986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543986).length < 2 ^ (prefixWord ++ tailWord_1543986).sum := by decide
  have hdescent : baseEnd_1543986 < baseStart_1543986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1543988 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_1543988 : Nat := 118140960795 + 1543988 * 2 ^ 59
def prefixEnd_1543988 : Nat := 4983230072969 + 3 ^ 40 * 1543988 * 2
def baseEnd_1543988 : Nat := 528538645849473582366223

theorem tailTrace_1543988 : CollatzResearch.WordTrace tailWord_1543988 prefixEnd_1543988 528538645849473582366223 := by
  unfold tailWord_1543988
  simp only [CollatzResearch.WordTrace]
  refine ⟨28156934365201321500952309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37542579153601762001269745 28156934365201321500952309)
  ·
    refine ⟨2639712596737623890714279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28156934365201321500952309 2639712596737623890714279)
    ·
      refine ⟨3959568895106435836071419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2639712596737623890714279 3959568895106435836071419)
      ·
        refine ⟨5939353342659653754107129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3959568895106435836071419 5939353342659653754107129)
        ·
          refine ⟨4454515006994740315580347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5939353342659653754107129 4454515006994740315580347)
          ·
            refine ⟨6681772510492110473370521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4454515006994740315580347 6681772510492110473370521)
            ·
              refine ⟨5011329382869082855027891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6681772510492110473370521 5011329382869082855027891)
              ·
                refine ⟨7516994074303624282541837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5011329382869082855027891 7516994074303624282541837)
                ·
                  refine ⟨2818872777863859105953189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7516994074303624282541837 2818872777863859105953189)
                  ·
                    refine ⟨528538645849473582366223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2818872777863859105953189 528538645849473582366223)
                    ·
                      rfl

theorem cell22_1543988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_1543988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1543988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1543988 prefixEnd_1543988 := by exact prefixLift 1543988
  have htrace : WordTrace (prefixWord ++ tailWord_1543988) baseStart_1543988 baseEnd_1543988 := by
    simpa [prefixWord, tailWord_1543988, baseEnd_1543988] using wordTrace_append hprefix tailTrace_1543988
  have hstable : (prefixWord ++ tailWord_1543988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1543988).length < 2 ^ (prefixWord ++ tailWord_1543988).sum := by decide
  have hdescent : baseEnd_1543988 < baseStart_1543988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1543988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544003 : List Nat := [1, 1, 1, 3, 1, 6, 2, 3, 4]
def baseStart_1544003 : Nat := 118140960795 + 1544003 * 2 ^ 59
def prefixEnd_1544003 : Nat := 4983230072969 + 3 ^ 40 * 1544003 * 2
def baseEnd_1544003 : Nat := 176181260218672847747059

theorem tailTrace_1544003 : CollatzResearch.WordTrace tailWord_1544003 prefixEnd_1544003 176181260218672847747059 := by
  unfold tailWord_1544003
  simp only [CollatzResearch.WordTrace]
  refine ⟨56314415825348300563700663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37542943883565533709133775 56314415825348300563700663)
  ·
    refine ⟨84471623738022450845550995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56314415825348300563700663 84471623738022450845550995)
    ·
      refine ⟨126707435607033676268326493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84471623738022450845550995 126707435607033676268326493)
      ·
        refine ⟨47515288352637628600622435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 126707435607033676268326493 47515288352637628600622435)
        ·
          refine ⟨71272932528956442900933653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 47515288352637628600622435 71272932528956442900933653)
          ·
            refine ⟨3340918712294833260981265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 71272932528956442900933653 3340918712294833260981265)
            ·
              refine ⟨2505689034221124945735949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3340918712294833260981265 2505689034221124945735949)
              ·
                refine ⟨939633387832921854650981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2505689034221124945735949 939633387832921854650981)
                ·
                  refine ⟨176181260218672847747059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939633387832921854650981 176181260218672847747059)
                  ·
                    rfl

theorem cell22_1544003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 4].length) (baseStart_1544003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544003 prefixEnd_1544003 := by exact prefixLift 1544003
  have htrace : WordTrace (prefixWord ++ tailWord_1544003) baseStart_1544003 baseEnd_1544003 := by
    simpa [prefixWord, tailWord_1544003, baseEnd_1544003] using wordTrace_append hprefix tailTrace_1544003
  have hstable : (prefixWord ++ tailWord_1544003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544003).length < 2 ^ (prefixWord ++ tailWord_1544003).sum := by decide
  have hdescent : baseEnd_1544003 < baseStart_1544003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544018 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 4, 3]
def baseStart_1544018 : Nat := 118140960795 + 1544018 * 2 ^ 59
def prefixEnd_1544018 : Nat := 4983230072969 + 3 ^ 40 * 1544018 * 2
def baseEnd_1544018 : Nat := 528548915462563504116131

theorem tailTrace_1544018 : CollatzResearch.WordTrace tailWord_1544018 prefixEnd_1544018 528548915462563504116131 := by
  unfold tailWord_1544018
  simp only [CollatzResearch.WordTrace]
  refine ⟨14078740730073489531374177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37543308613529305416997805 14078740730073489531374177)
  ·
    refine ⟨10559055547555117148530633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14078740730073489531374177 10559055547555117148530633)
    ·
      refine ⟨7919291660666337861397975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10559055547555117148530633 7919291660666337861397975)
      ·
        refine ⟨11878937490999506792096963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7919291660666337861397975 11878937490999506792096963)
        ·
          refine ⟨17818406236499260188145445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11878937490999506792096963 17818406236499260188145445)
          ·
            refine ⟨3340951169343611285277271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17818406236499260188145445 3340951169343611285277271)
            ·
              refine ⟨5011426754015416927915907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3340951169343611285277271 5011426754015416927915907)
              ·
                refine ⟨7517140131023125391873861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5011426754015416927915907 7517140131023125391873861)
                ·
                  refine ⟨1409463774566836010976349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7517140131023125391873861 1409463774566836010976349)
                  ·
                    refine ⟨528548915462563504116131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1409463774566836010976349 528548915462563504116131)
                    ·
                      rfl

theorem cell22_1544018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 4, 3].length) (baseStart_1544018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544018 prefixEnd_1544018 := by exact prefixLift 1544018
  have htrace : WordTrace (prefixWord ++ tailWord_1544018) baseStart_1544018 baseEnd_1544018 := by
    simpa [prefixWord, tailWord_1544018, baseEnd_1544018] using wordTrace_append hprefix tailTrace_1544018
  have hstable : (prefixWord ++ tailWord_1544018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544018).length < 2 ^ (prefixWord ++ tailWord_1544018).sum := by decide
  have hdescent : baseEnd_1544018 < baseStart_1544018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544035 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 1, 5]
def baseStart_1544035 : Nat := 118140960795 + 1544035 * 2 ^ 59
def prefixEnd_1544035 : Nat := 4983230072969 + 3 ^ 40 * 1544035 * 2
def baseEnd_1544035 : Nat := 528554734909981126441079

theorem tailTrace_1544035 : CollatzResearch.WordTrace tailWord_1544035 prefixEnd_1544035 528554734909981126441079 := by
  unfold tailWord_1544035
  simp only [CollatzResearch.WordTrace]
  refine ⟨56315582961232370028865559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37543721974154913352577039 56315582961232370028865559)
  ·
    refine ⟨84473374441848555043298339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56315582961232370028865559 84473374441848555043298339)
    ·
      refine ⟨126710061662772832564947509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 84473374441848555043298339 126710061662772832564947509)
      ·
        refine ⟨11879068280884953052963829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 126710061662772832564947509 11879068280884953052963829)
        ·
          refine ⟨1113662651332964348715359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11879068280884953052963829 1113662651332964348715359)
          ·
            refine ⟨1670493976999446523073039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113662651332964348715359 1670493976999446523073039)
            ·
              refine ⟨2505740965499169784609559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670493976999446523073039 2505740965499169784609559)
              ·
                refine ⟨3758611448248754676914339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2505740965499169784609559 3758611448248754676914339)
                ·
                  refine ⟨5637917172373132015371509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3758611448248754676914339 5637917172373132015371509)
                  ·
                    refine ⟨528554734909981126441079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5637917172373132015371509 528554734909981126441079)
                    ·
                      rfl

theorem cell22_1544035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 5].length) (baseStart_1544035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544035 prefixEnd_1544035 := by exact prefixLift 1544035
  have htrace : WordTrace (prefixWord ++ tailWord_1544035) baseStart_1544035 baseEnd_1544035 := by
    simpa [prefixWord, tailWord_1544035, baseEnd_1544035] using wordTrace_append hprefix tailTrace_1544035
  have hstable : (prefixWord ++ tailWord_1544035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544035).length < 2 ^ (prefixWord ++ tailWord_1544035).sum := by decide
  have hdescent : baseEnd_1544035 < baseStart_1544035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544054 : List Nat := [5, 1, 1, 3, 3, 1, 1, 3, 4]
def baseStart_1544054 : Nat := 118140960795 + 1544054 * 2 ^ 59
def prefixEnd_1544054 : Nat := 4983230072969 + 3 ^ 40 * 1544054 * 2
def baseEnd_1544054 : Nat := 176187079666090470072007

theorem tailTrace_1544054 : CollatzResearch.WordTrace tailWord_1544054 prefixEnd_1544054 176187079666090470072007 := by
  unfold tailWord_1544054
  simp only [CollatzResearch.WordTrace]
  refine ⟨3519767246760221017112951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 37544183965442357515871477 3519767246760221017112951)
  ·
    refine ⟨5279650870140331525669427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3519767246760221017112951 5279650870140331525669427)
    ·
      refine ⟨7919476305210497288504141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5279650870140331525669427 7919476305210497288504141)
      ·
        refine ⟨2969803614453936483189053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7919476305210497288504141 2969803614453936483189053)
        ·
          refine ⟨1113676355420226181195895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2969803614453936483189053 1113676355420226181195895)
          ·
            refine ⟨1670514533130339271793843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113676355420226181195895 1670514533130339271793843)
            ·
              refine ⟨2505771799695508907690765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670514533130339271793843 2505771799695508907690765)
              ·
                refine ⟨939664424885815840384037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2505771799695508907690765 939664424885815840384037)
                ·
                  refine ⟨176187079666090470072007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 939664424885815840384037 176187079666090470072007)
                  ·
                    rfl

theorem cell22_1544054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_1544054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544054 prefixEnd_1544054 := by exact prefixLift 1544054
  have htrace : WordTrace (prefixWord ++ tailWord_1544054) baseStart_1544054 baseEnd_1544054 := by
    simpa [prefixWord, tailWord_1544054, baseEnd_1544054] using wordTrace_append hprefix tailTrace_1544054
  have hstable : (prefixWord ++ tailWord_1544054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544054).length < 2 ^ (prefixWord ++ tailWord_1544054).sum := by decide
  have hdescent : baseEnd_1544054 < baseStart_1544054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544065 : List Nat := [1, 2, 4, 4, 2, 1, 8]
def baseStart_1544065 : Nat := 118140960795 + 1544065 * 2 ^ 59
def prefixEnd_1544065 : Nat := 4983230072969 + 3 ^ 40 * 1544065 * 2
def baseEnd_1544065 : Nat := 19576481649002631414481

theorem tailTrace_1544065 : CollatzResearch.WordTrace tailWord_1544065 prefixEnd_1544065 19576481649002631414481 := by
  unfold tailWord_1544065
  simp only [CollatzResearch.WordTrace]
  refine ⟨56316677151123685152457649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37544451434082456768305099 56316677151123685152457649)
  ·
    refine ⟨42237507863342763864343237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56316677151123685152457649 42237507863342763864343237)
    ·
      refine ⟨7919532724376768224564357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42237507863342763864343237 7919532724376768224564357)
      ·
        refine ⟨1484912385820644042105817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7919532724376768224564357 1484912385820644042105817)
        ·
          refine ⟨1113684289365483031579363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1484912385820644042105817 1113684289365483031579363)
          ·
            refine ⟨1670526434048224547369045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113684289365483031579363 1670526434048224547369045)
            ·
              refine ⟨19576481649002631414481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1670526434048224547369045 19576481649002631414481)
              ·
                rfl

theorem cell22_1544065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 8].length) (baseStart_1544065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544065 prefixEnd_1544065 := by exact prefixLift 1544065
  have htrace : WordTrace (prefixWord ++ tailWord_1544065) baseStart_1544065 baseEnd_1544065 := by
    simpa [prefixWord, tailWord_1544065, baseEnd_1544065] using wordTrace_append hprefix tailTrace_1544065
  have hstable : (prefixWord ++ tailWord_1544065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544065).length < 2 ^ (prefixWord ++ tailWord_1544065).sum := by decide
  have hdescent : baseEnd_1544065 < baseStart_1544065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544076 : List Nat := [2, 2, 1, 2, 1, 2, 1, 6, 5]
def baseStart_1544076 : Nat := 118140960795 + 1544076 * 2 ^ 59
def prefixEnd_1544076 : Nat := 4983230072969 + 3 ^ 40 * 1544076 * 2
def baseEnd_1544076 : Nat := 176189590015956895388651

theorem tailTrace_1544076 : CollatzResearch.WordTrace tailWord_1544076 prefixEnd_1544076 176189590015956895388651 := by
  unfold tailWord_1544076
  simp only [CollatzResearch.WordTrace]
  refine ⟨28158539177041917015554041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37544718902722556020738721 28158539177041917015554041)
  ·
    refine ⟨21118904382781437761665531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28158539177041917015554041 21118904382781437761665531)
    ·
      refine ⟨31678356574172156642498297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21118904382781437761665531 31678356574172156642498297)
      ·
        refine ⟨23758767430629117481873723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31678356574172156642498297 23758767430629117481873723)
        ·
          refine ⟨35638151145943676222810585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23758767430629117481873723 35638151145943676222810585)
          ·
            refine ⟨26728613359457757167107939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35638151145943676222810585 26728613359457757167107939)
            ·
              refine ⟨40092920039186635750661909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26728613359457757167107939 40092920039186635750661909)
              ·
                refine ⟨1879355626836873550812277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40092920039186635750661909 1879355626836873550812277)
                ·
                  refine ⟨176189590015956895388651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1879355626836873550812277 176189590015956895388651)
                  ·
                    rfl

theorem cell22_1544076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_1544076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544076 prefixEnd_1544076 := by exact prefixLift 1544076
  have htrace : WordTrace (prefixWord ++ tailWord_1544076) baseStart_1544076 baseEnd_1544076 := by
    simpa [prefixWord, tailWord_1544076, baseEnd_1544076] using wordTrace_append hprefix tailTrace_1544076
  have hstable : (prefixWord ++ tailWord_1544076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544076).length < 2 ^ (prefixWord ++ tailWord_1544076).sum := by decide
  have hdescent : baseEnd_1544076 < baseStart_1544076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544093 : List Nat := [1, 4, 2, 1, 2, 3, 1, 3, 5]
def baseStart_1544093 : Nat := 118140960795 + 1544093 * 2 ^ 59
def prefixEnd_1544093 : Nat := 4983230072969 + 3 ^ 40 * 1544093 * 2
def baseEnd_1544093 : Nat := 176191529831762769496967

theorem tailTrace_1544093 : CollatzResearch.WordTrace tailWord_1544093 prefixEnd_1544093 176191529831762769496967 := by
  unfold tailWord_1544093
  simp only [CollatzResearch.WordTrace]
  refine ⟨56317698395022245934476933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37545132263348163956317955 56317698395022245934476933)
  ·
    refine ⟨10559568449066671112714425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 56317698395022245934476933 10559568449066671112714425)
    ·
      refine ⟨7919676336800003334535819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10559568449066671112714425 7919676336800003334535819)
      ·
        refine ⟨11879514505200005001803729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7919676336800003334535819 11879514505200005001803729)
        ·
          refine ⟨8909635878900003751352797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11879514505200005001803729 8909635878900003751352797)
          ·
            refine ⟨3341113454587501406757299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8909635878900003751352797 3341113454587501406757299)
            ·
              refine ⟨5011670181881252110135949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3341113454587501406757299 5011670181881252110135949)
              ·
                refine ⟨1879376318205469541300981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5011670181881252110135949 1879376318205469541300981)
                ·
                  refine ⟨176191529831762769496967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1879376318205469541300981 176191529831762769496967)
                  ·
                    rfl

theorem cell22_1544093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_1544093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544093 prefixEnd_1544093 := by exact prefixLift 1544093
  have htrace : WordTrace (prefixWord ++ tailWord_1544093) baseStart_1544093 baseEnd_1544093 := by
    simpa [prefixWord, tailWord_1544093, baseEnd_1544093] using wordTrace_append hprefix tailTrace_1544093
  have hstable : (prefixWord ++ tailWord_1544093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544093).length < 2 ^ (prefixWord ++ tailWord_1544093).sum := by decide
  have hdescent : baseEnd_1544093 < baseStart_1544093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544151 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 1, 6]
def baseStart_1544151 : Nat := 118140960795 + 1544151 * 2 ^ 59
def prefixEnd_1544151 : Nat := 4983230072969 + 3 ^ 40 * 1544151 * 2
def baseEnd_1544151 : Nat := 528594444080595490540723

theorem tailTrace_1544151 : CollatzResearch.WordTrace tailWord_1544151 prefixEnd_1544151 528594444080595490540723 := by
  unfold tailWord_1544151
  simp only [CollatzResearch.WordTrace]
  refine ⟨56319813828812121840088307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37546542552541414560058871 56319813828812121840088307)
  ·
    refine ⟨84479720743218182760132461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56319813828812121840088307 84479720743218182760132461)
    ·
      refine ⟨31679895278706818535049673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 84479720743218182760132461 31679895278706818535049673)
      ·
        refine ⟨23759921459030113901287255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31679895278706818535049673 23759921459030113901287255)
        ·
          refine ⟨35639882188545170851930883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23759921459030113901287255 35639882188545170851930883)
          ·
            refine ⟨53459823282817756277896325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 35639882188545170851930883 53459823282817756277896325)
            ·
              refine ⟨10023716865528329302105561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 53459823282817756277896325 10023716865528329302105561)
              ·
                refine ⟨7517787649146246976579171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10023716865528329302105561 7517787649146246976579171)
                ·
                  refine ⟨11276681473719370464868757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7517787649146246976579171 11276681473719370464868757)
                  ·
                    refine ⟨528594444080595490540723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11276681473719370464868757 528594444080595490540723)
                    ·
                      rfl

theorem cell22_1544151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_1544151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544151 prefixEnd_1544151 := by exact prefixLift 1544151
  have htrace : WordTrace (prefixWord ++ tailWord_1544151) baseStart_1544151 baseEnd_1544151 := by
    simpa [prefixWord, tailWord_1544151, baseEnd_1544151] using wordTrace_append hprefix tailTrace_1544151
  have hstable : (prefixWord ++ tailWord_1544151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544151).length < 2 ^ (prefixWord ++ tailWord_1544151).sum := by decide
  have hdescent : baseEnd_1544151 < baseStart_1544151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544249 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 3, 3]
def baseStart_1544249 : Nat := 118140960795 + 1544249 * 2 ^ 59
def prefixEnd_1544249 : Nat := 4983230072969 + 3 ^ 40 * 1544249 * 2
def baseEnd_1544249 : Nat := 528627991483355901590423

theorem tailTrace_1544249 : CollatzResearch.WordTrace tailWord_1544249 prefixEnd_1544249 528627991483355901590423 := by
  unfold tailWord_1544249
  simp only [CollatzResearch.WordTrace]
  refine ⟨56323388182457084577155801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37548925454971389718103867 56323388182457084577155801)
  ·
    refine ⟨42242541136842813432866851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 56323388182457084577155801 42242541136842813432866851)
    ·
      refine ⟨63363811705264220149300277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42242541136842813432866851 63363811705264220149300277)
      ·
        refine ⟨5940357347368520638996901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63363811705264220149300277 5940357347368520638996901)
        ·
          refine ⟨1113817002631597619811919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5940357347368520638996901 1113817002631597619811919)
          ·
            refine ⟨1670725503947396429717879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113817002631597619811919 1670725503947396429717879)
            ·
              refine ⟨2506088255921094644576819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670725503947396429717879 2506088255921094644576819)
              ·
                refine ⟨3759132383881641966865229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2506088255921094644576819 3759132383881641966865229)
                ·
                  refine ⟨1409674643955615737574461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3759132383881641966865229 1409674643955615737574461)
                  ·
                    refine ⟨528627991483355901590423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1409674643955615737574461 528627991483355901590423)
                    ·
                      rfl

theorem cell22_1544249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 3, 3].length) (baseStart_1544249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544249 prefixEnd_1544249 := by exact prefixLift 1544249
  have htrace : WordTrace (prefixWord ++ tailWord_1544249) baseStart_1544249 baseEnd_1544249 := by
    simpa [prefixWord, tailWord_1544249, baseEnd_1544249] using wordTrace_append hprefix tailTrace_1544249
  have hstable : (prefixWord ++ tailWord_1544249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544249).length < 2 ^ (prefixWord ++ tailWord_1544249).sum := by decide
  have hdescent : baseEnd_1544249 < baseStart_1544249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544262 : List Nat := [6, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1544262 : Nat := 118140960795 + 1544262 * 2 ^ 59
def prefixEnd_1544262 : Nat := 4983230072969 + 3 ^ 40 * 1544262 * 2
def baseEnd_1544262 : Nat := 176210813883009400338461

theorem tailTrace_1544262 : CollatzResearch.WordTrace tailWord_1544262 prefixEnd_1544262 176210813883009400338461 := by
  unfold tailWord_1544262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1760120697856562118668095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 37549241554273325198252693 1760120697856562118668095)
  ·
    refine ⟨2640181046784843178002143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1760120697856562118668095 2640181046784843178002143)
    ·
      refine ⟨3960271570177264767003215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2640181046784843178002143 3960271570177264767003215)
      ·
        refine ⟨5940407355265897150504823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3960271570177264767003215 5940407355265897150504823)
        ·
          refine ⟨8910611032898845725757235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5940407355265897150504823 8910611032898845725757235)
          ·
            refine ⟨13365916549348268588635853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8910611032898845725757235 13365916549348268588635853)
            ·
              refine ⟨5012218706005600720738445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13365916549348268588635853 5012218706005600720738445)
              ·
                refine ⟨1879582014752100270276917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5012218706005600720738445 1879582014752100270276917)
                ·
                  refine ⟨176210813883009400338461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1879582014752100270276917 176210813883009400338461)
                  ·
                    rfl

theorem cell22_1544262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1544262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544262 prefixEnd_1544262 := by exact prefixLift 1544262
  have htrace : WordTrace (prefixWord ++ tailWord_1544262) baseStart_1544262 baseEnd_1544262 := by
    simpa [prefixWord, tailWord_1544262, baseEnd_1544262] using wordTrace_append hprefix tailTrace_1544262
  have hstable : (prefixWord ++ tailWord_1544262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544262).length < 2 ^ (prefixWord ++ tailWord_1544262).sum := by decide
  have hdescent : baseEnd_1544262 < baseStart_1544262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544288 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 3, 5]
def baseStart_1544288 : Nat := 118140960795 + 1544288 * 2 ^ 59
def prefixEnd_1544288 : Nat := 4983230072969 + 3 ^ 40 * 1544288 * 2
def baseEnd_1544288 : Nat := 528641341980372799865303

theorem tailTrace_1544288 : CollatzResearch.WordTrace tailWord_1544288 prefixEnd_1544288 528641341980372799865303 := by
  unfold tailWord_1544288
  simp only [CollatzResearch.WordTrace]
  refine ⟨28162405314657897118912759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37549873752877196158550345 28162405314657897118912759)
  ·
    refine ⟨42243607971986845678369139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28162405314657897118912759 42243607971986845678369139)
    ·
      refine ⟨63365411957980268517553709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42243607971986845678369139 63365411957980268517553709)
      ·
        refine ⟨23762029484242600694082641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 63365411957980268517553709 23762029484242600694082641)
        ·
          refine ⟨17821522113181950520561981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23762029484242600694082641 17821522113181950520561981)
          ·
            refine ⟨6683070792443231445210743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17821522113181950520561981 6683070792443231445210743)
            ·
              refine ⟨10024606188664847167816115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6683070792443231445210743 10024606188664847167816115)
              ·
                refine ⟨15036909282997270751724173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10024606188664847167816115 15036909282997270751724173)
                ·
                  refine ⟨5638840981123976531896565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15036909282997270751724173 5638840981123976531896565)
                  ·
                    refine ⟨528641341980372799865303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5638840981123976531896565 528641341980372799865303)
                    ·
                      rfl

theorem cell22_1544288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 3, 5].length) (baseStart_1544288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544288 prefixEnd_1544288 := by exact prefixLift 1544288
  have htrace : WordTrace (prefixWord ++ tailWord_1544288) baseStart_1544288 baseEnd_1544288 := by
    simpa [prefixWord, tailWord_1544288, baseEnd_1544288] using wordTrace_append hprefix tailTrace_1544288
  have hstable : (prefixWord ++ tailWord_1544288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544288).length < 2 ^ (prefixWord ++ tailWord_1544288).sum := by decide
  have hdescent : baseEnd_1544288 < baseStart_1544288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544356 : List Nat := [2, 3, 1, 2, 5, 1, 1, 2, 2, 3]
def baseStart_1544356 : Nat := 118140960795 + 1544356 * 2 ^ 59
def prefixEnd_1544356 : Nat := 4983230072969 + 3 ^ 40 * 1544356 * 2
def baseEnd_1544356 : Nat := 528664619770043289165095

theorem tailTrace_1544356 : CollatzResearch.WordTrace tailWord_1544356 prefixEnd_1544356 528664619770043289165095 := by
  unfold tailWord_1544356
  simp only [CollatzResearch.WordTrace]
  refine ⟨28163645396534720925650461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37551527195379627900867281 28163645396534720925650461)
  ·
    refine ⟨10561367023700520347118923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28163645396534720925650461 10561367023700520347118923)
    ·
      refine ⟨15842050535550780520678385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10561367023700520347118923 15842050535550780520678385)
      ·
        refine ⟨11881537901663085390508789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15842050535550780520678385 11881537901663085390508789)
        ·
          refine ⟨1113894178280914255360199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11881537901663085390508789 1113894178280914255360199)
          ·
            refine ⟨1670841267421371383040299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1113894178280914255360199 1670841267421371383040299)
            ·
              refine ⟨2506261901132057074560449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670841267421371383040299 2506261901132057074560449)
              ·
                refine ⟨1879696425849042805920337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2506261901132057074560449 1879696425849042805920337)
                ·
                  refine ⟨1409772319386782104440253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1879696425849042805920337 1409772319386782104440253)
                  ·
                    refine ⟨528664619770043289165095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1409772319386782104440253 528664619770043289165095)
                    ·
                      rfl

theorem cell22_1544356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_1544356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544356 prefixEnd_1544356 := by exact prefixLift 1544356
  have htrace : WordTrace (prefixWord ++ tailWord_1544356) baseStart_1544356 baseEnd_1544356 := by
    simpa [prefixWord, tailWord_1544356, baseEnd_1544356] using wordTrace_append hprefix tailTrace_1544356
  have hstable : (prefixWord ++ tailWord_1544356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544356).length < 2 ^ (prefixWord ++ tailWord_1544356).sum := by decide
  have hdescent : baseEnd_1544356 < baseStart_1544356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544386 : List Nat := [3, 5, 1, 1, 1, 3, 2, 6]
def baseStart_1544386 : Nat := 118140960795 + 1544386 * 2 ^ 59
def prefixEnd_1544386 : Nat := 4983230072969 + 3 ^ 40 * 1544386 * 2
def baseEnd_1544386 : Nat := 58741654375903690101667

theorem tailTrace_1544386 : CollatzResearch.WordTrace tailWord_1544386 prefixEnd_1544386 58741654375903690101667 := by
  unfold tailWord_1544386
  simp only [CollatzResearch.WordTrace]
  refine ⟨14082096245740189243723253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 37552256655307171316595341 14082096245740189243723253)
  ·
    refine ⟨1320196523038142741599055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14082096245740189243723253 1320196523038142741599055)
    ·
      refine ⟨1980294784557214112398583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1320196523038142741599055 1980294784557214112398583)
      ·
        refine ⟨2970442176835821168597875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1980294784557214112398583 2970442176835821168597875)
        ·
          refine ⟨4455663265253731752896813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2970442176835821168597875 4455663265253731752896813)
          ·
            refine ⟨1670873724470149407336305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4455663265253731752896813 1670873724470149407336305)
            ·
              refine ⟨1253155293352612055502229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1670873724470149407336305 1253155293352612055502229)
              ·
                refine ⟨58741654375903690101667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1253155293352612055502229 58741654375903690101667)
                ·
                  rfl

theorem cell22_1544386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 6].length) (baseStart_1544386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544386 prefixEnd_1544386 := by exact prefixLift 1544386
  have htrace : WordTrace (prefixWord ++ tailWord_1544386) baseStart_1544386 baseEnd_1544386 := by
    simpa [prefixWord, tailWord_1544386, baseEnd_1544386] using wordTrace_append hprefix tailTrace_1544386
  have hstable : (prefixWord ++ tailWord_1544386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544386).length < 2 ^ (prefixWord ++ tailWord_1544386).sum := by decide
  have hdescent : baseEnd_1544386 < baseStart_1544386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544444 : List Nat := [2, 2, 2, 1, 4, 3, 1, 2, 1, 4]
def baseStart_1544444 : Nat := 118140960795 + 1544444 * 2 ^ 59
def prefixEnd_1544444 : Nat := 4983230072969 + 3 ^ 40 * 1544444 * 2
def baseEnd_1544444 : Nat := 528694743968440392964825

theorem tailTrace_1544444 : CollatzResearch.WordTrace tailWord_1544444 prefixEnd_1544444 528694743968440392964825 := by
  unfold tailWord_1544444
  simp only [CollatzResearch.WordTrace]
  refine ⟨28165250208375316440252193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37553666944500421920336257 28165250208375316440252193)
  ·
    refine ⟨21123937656281487330189145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28165250208375316440252193 21123937656281487330189145)
    ·
      refine ⟨15842953242211115497641859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21123937656281487330189145 15842953242211115497641859)
      ·
        refine ⟨23764429863316673246462789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15842953242211115497641859 23764429863316673246462789)
        ·
          refine ⟨4455830599371876233711773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23764429863316673246462789 4455830599371876233711773)
          ·
            refine ⟨1670936474764453587641915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4455830599371876233711773 1670936474764453587641915)
            ·
              refine ⟨2506404712146680381462873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1670936474764453587641915 2506404712146680381462873)
              ·
                refine ⟨1879803534110010286097155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2506404712146680381462873 1879803534110010286097155)
                ·
                  refine ⟨2819705301165015429145733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1879803534110010286097155 2819705301165015429145733)
                  ·
                    refine ⟨528694743968440392964825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2819705301165015429145733 528694743968440392964825)
                    ·
                      rfl

theorem cell22_1544444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 1, 4].length) (baseStart_1544444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544444 prefixEnd_1544444 := by exact prefixLift 1544444
  have htrace : WordTrace (prefixWord ++ tailWord_1544444) baseStart_1544444 baseEnd_1544444 := by
    simpa [prefixWord, tailWord_1544444, baseEnd_1544444] using wordTrace_append hprefix tailTrace_1544444
  have hstable : (prefixWord ++ tailWord_1544444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544444).length < 2 ^ (prefixWord ++ tailWord_1544444).sum := by decide
  have hdescent : baseEnd_1544444 < baseStart_1544444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544532 : List Nat := [2, 4, 1, 1, 2, 3, 1, 1, 7]
def baseStart_1544532 : Nat := 118140960795 + 1544532 * 2 ^ 59
def prefixEnd_1544532 : Nat := 4983230072969 + 3 ^ 40 * 1544532 * 2
def baseEnd_1544532 : Nat := 176241622722279165588185

theorem tailTrace_1544532 : CollatzResearch.WordTrace tailWord_1544532 prefixEnd_1544532 176241622722279165588185 := by
  unfold tailWord_1544532
  simp only [CollatzResearch.WordTrace]
  refine ⟨28166855020215911954853925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 37555806693621215939805233 28166855020215911954853925)
  ·
    refine ⟨5281285316290483491535111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28166855020215911954853925 5281285316290483491535111)
    ·
      refine ⟨7921927974435725237302667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5281285316290483491535111 7921927974435725237302667)
      ·
        refine ⟨11882891961653587855954001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7921927974435725237302667 11882891961653587855954001)
        ·
          refine ⟨8912168971240190891965501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11882891961653587855954001 8912168971240190891965501)
          ·
            refine ⟨3342063364215071584487063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8912168971240190891965501 3342063364215071584487063)
            ·
              refine ⟨5013095046322607376730595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3342063364215071584487063 5013095046322607376730595)
              ·
                refine ⟨7519642569483911065095893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5013095046322607376730595 7519642569483911065095893)
                ·
                  refine ⟨176241622722279165588185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7519642569483911065095893 176241622722279165588185)
                  ·
                    rfl

theorem cell22_1544532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_1544532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544532 prefixEnd_1544532 := by exact prefixLift 1544532
  have htrace : WordTrace (prefixWord ++ tailWord_1544532) baseStart_1544532 baseEnd_1544532 := by
    simpa [prefixWord, tailWord_1544532, baseEnd_1544532] using wordTrace_append hprefix tailTrace_1544532
  have hstable : (prefixWord ++ tailWord_1544532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544532).length < 2 ^ (prefixWord ++ tailWord_1544532).sum := by decide
  have hdescent : baseEnd_1544532 < baseStart_1544532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544542 : List Nat := [4, 4, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_1544542 : Nat := 118140960795 + 1544542 * 2 ^ 59
def prefixEnd_1544542 : Nat := 4983230072969 + 3 ^ 40 * 1544542 * 2
def baseEnd_1544542 : Nat := 528728291371200804014525

theorem tailTrace_1544542 : CollatzResearch.WordTrace tailWord_1544542 prefixEnd_1544542 528728291371200804014525 := by
  unfold tailWord_1544542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7041759346299449452196485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 37556049846930397078381253 7041759346299449452196485)
  ·
    refine ⟨1320329877431146772286841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7041759346299449452196485 1320329877431146772286841)
    ·
      refine ⟨990247408073360079215131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1320329877431146772286841 990247408073360079215131)
      ·
        refine ⟨1485371112110040118822697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 990247408073360079215131 1485371112110040118822697)
        ·
          refine ⟨1114028334082530089117023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1485371112110040118822697 1114028334082530089117023)
          ·
            refine ⟨1671042501123795133675535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1114028334082530089117023 1671042501123795133675535)
            ·
              refine ⟨2506563751685692700513303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1671042501123795133675535 2506563751685692700513303)
              ·
                refine ⟨3759845627528539050769955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2506563751685692700513303 3759845627528539050769955)
                ·
                  refine ⟨5639768441292808576154933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3759845627528539050769955 5639768441292808576154933)
                  ·
                    refine ⟨528728291371200804014525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5639768441292808576154933 528728291371200804014525)
                    ·
                      rfl

theorem cell22_1544542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_1544542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544542 prefixEnd_1544542 := by exact prefixLift 1544542
  have htrace : WordTrace (prefixWord ++ tailWord_1544542) baseStart_1544542 baseEnd_1544542 := by
    simpa [prefixWord, tailWord_1544542, baseEnd_1544542] using wordTrace_append hprefix tailTrace_1544542
  have hstable : (prefixWord ++ tailWord_1544542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544542).length < 2 ^ (prefixWord ++ tailWord_1544542).sum := by decide
  have hdescent : baseEnd_1544542 < baseStart_1544542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544549 : List Nat := [1, 3, 1, 3, 1, 4, 3, 1, 5]
def baseStart_1544549 : Nat := 118140960795 + 1544549 * 2 ^ 59
def prefixEnd_1544549 : Nat := 4983230072969 + 3 ^ 40 * 1544549 * 2
def baseEnd_1544549 : Nat := 176243562538085039696501

theorem tailTrace_1544549 : CollatzResearch.WordTrace tailWord_1544549 prefixEnd_1544549 176243562538085039696501 := by
  unfold tailWord_1544549
  simp only [CollatzResearch.WordTrace]
  refine ⟨56334330081370235813076701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37556220054246823875384467 56334330081370235813076701)
  ·
    refine ⟨21125373780513838429903763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 56334330081370235813076701 21125373780513838429903763)
    ·
      refine ⟨31688060670770757644855645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21125373780513838429903763 31688060670770757644855645)
      ·
        refine ⟨11883022751539034116820867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31688060670770757644855645 11883022751539034116820867)
        ·
          refine ⟨17824534127308551175231301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11883022751539034116820867 17824534127308551175231301)
          ·
            refine ⟨3342100148870353345355869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17824534127308551175231301 3342100148870353345355869)
            ·
              refine ⟨1253287555826382504508451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3342100148870353345355869 1253287555826382504508451)
              ·
                refine ⟨1879931333739573756762677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1253287555826382504508451 1879931333739573756762677)
                ·
                  refine ⟨176243562538085039696501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1879931333739573756762677 176243562538085039696501)
                  ·
                    rfl

theorem cell22_1544549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_1544549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544549 prefixEnd_1544549 := by exact prefixLift 1544549
  have htrace : WordTrace (prefixWord ++ tailWord_1544549) baseStart_1544549 baseEnd_1544549 := by
    simpa [prefixWord, tailWord_1544549, baseEnd_1544549] using wordTrace_append hprefix tailTrace_1544549
  have hstable : (prefixWord ++ tailWord_1544549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544549).length < 2 ^ (prefixWord ++ tailWord_1544549).sum := by decide
  have hdescent : baseEnd_1544549 < baseStart_1544549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1544607 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 4, 4]
def baseStart_1544607 : Nat := 118140960795 + 1544607 * 2 ^ 59
def prefixEnd_1544607 : Nat := 4983230072969 + 3 ^ 40 * 1544607 * 2
def baseEnd_1544607 : Nat := 528750542199562301139325

theorem tailTrace_1544607 : CollatzResearch.WordTrace tailWord_1544607 prefixEnd_1544607 528750542199562301139325 := by
  unfold tailWord_1544607
  simp only [CollatzResearch.WordTrace]
  refine ⟨56336445515160111718688075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 37557630343440074479125383 56336445515160111718688075)
  ·
    refine ⟨84504668272740167578032113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 56336445515160111718688075 84504668272740167578032113)
    ·
      refine ⟨63378501204555125683524085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 84504668272740167578032113 63378501204555125683524085)
      ·
        refine ⟨5941734487927043032830383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 63378501204555125683524085 5941734487927043032830383)
        ·
          refine ⟨8912601731890564549245575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5941734487927043032830383 8912601731890564549245575)
          ·
            refine ⟨13368902597835846823868363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8912601731890564549245575 13368902597835846823868363)
            ·
              refine ⟨20053353896753770235802545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13368902597835846823868363 20053353896753770235802545)
              ·
                refine ⟨15040015422565327676851909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20053353896753770235802545 15040015422565327676851909)
                ·
                  refine ⟨2820002891730998939409733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15040015422565327676851909 2820002891730998939409733)
                  ·
                    refine ⟨528750542199562301139325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2820002891730998939409733 528750542199562301139325)
                    ·
                      rfl

theorem cell22_1544607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 4, 4].length) (baseStart_1544607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1544607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1544607 prefixEnd_1544607 := by exact prefixLift 1544607
  have htrace : WordTrace (prefixWord ++ tailWord_1544607) baseStart_1544607 baseEnd_1544607 := by
    simpa [prefixWord, tailWord_1544607, baseEnd_1544607] using wordTrace_append hprefix tailTrace_1544607
  have hstable : (prefixWord ++ tailWord_1544607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1544607).length < 2 ^ (prefixWord ++ tailWord_1544607).sum := by decide
  have hdescent : baseEnd_1544607 < baseStart_1544607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1544607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
