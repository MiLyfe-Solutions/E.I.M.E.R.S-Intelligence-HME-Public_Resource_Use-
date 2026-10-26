import V185TrunkScan21Chunk098

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1202088 : List Nat := [2, 1, 6, 2, 1, 1, 2, 2, 4]
def baseStart_1202088 : Nat := 118140960795 + 1202088 * 2 ^ 59
def prefixEnd_1202088 : Nat := 4983230072969 + 3 ^ 40 * 1202088 * 2
def baseEnd_1202088 : Nat := 274332859111999137276313

theorem tailTrace_1202088 : CollatzResearch.WordTrace tailWord_1202088 prefixEnd_1202088 274332859111999137276313 := by
  unfold tailWord_1202088
  simp only [CollatzResearch.WordTrace]
  refine ⟨21921875634523975565359459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29229167512698634087145945 21921875634523975565359459)
  ·
    refine ⟨32882813451785963348039189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21921875634523975565359459 32882813451785963348039189)
    ·
      refine ⟨1541381880552467031939337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 32882813451785963348039189 1541381880552467031939337)
      ·
        refine ⟨1156036410414350273954503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1541381880552467031939337 1156036410414350273954503)
        ·
          refine ⟨1734054615621525410931755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156036410414350273954503 1734054615621525410931755)
          ·
            refine ⟨2601081923432288116397633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734054615621525410931755 2601081923432288116397633)
            ·
              refine ⟨1950811442574216087298225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2601081923432288116397633 1950811442574216087298225)
              ·
                refine ⟨1463108581930662065473669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1950811442574216087298225 1463108581930662065473669)
                ·
                  refine ⟨274332859111999137276313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1463108581930662065473669 274332859111999137276313)
                  ·
                    rfl

theorem cell21_1202088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_1202088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202088 prefixEnd_1202088 := by exact prefixLift 1202088
  have htrace : WordTrace (prefixWord ++ tailWord_1202088) baseStart_1202088 baseEnd_1202088 := by
    simpa [prefixWord, tailWord_1202088, baseEnd_1202088] using wordTrace_append hprefix tailTrace_1202088
  have hstable : (prefixWord ++ tailWord_1202088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202088).length < 2 ^ (prefixWord ++ tailWord_1202088).sum := by decide
  have hdescent : baseEnd_1202088 < baseStart_1202088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202099 : List Nat := [1, 1, 1, 2, 3, 1, 5, 4, 3]
def baseStart_1202099 : Nat := 118140960795 + 1202099 * 2 ^ 59
def prefixEnd_1202099 : Nat := 4983230072969 + 3 ^ 40 * 1202099 * 2
def baseEnd_1202099 : Nat := 274335369461865562592957

theorem tailTrace_1202099 : CollatzResearch.WordTrace tailWord_1202099 prefixEnd_1202099 274335369461865562592957 := by
  unfold tailWord_1202099
  simp only [CollatzResearch.WordTrace]
  refine ⟨43844152472008100009369351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29229434981338733339579567 43844152472008100009369351)
  ·
    refine ⟨65766228708012150014054027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43844152472008100009369351 65766228708012150014054027)
    ·
      refine ⟨98649343062018225021081041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65766228708012150014054027 98649343062018225021081041)
      ·
        refine ⟨73987007296513668765810781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98649343062018225021081041 73987007296513668765810781)
        ·
          refine ⟨27745127736192625787179043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73987007296513668765810781 27745127736192625787179043)
          ·
            refine ⟨41617691604288938680768565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27745127736192625787179043 41617691604288938680768565)
            ·
              refine ⟨3901658587902088001322053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41617691604288938680768565 3901658587902088001322053)
              ·
                refine ⟨731560985231641500247885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3901658587902088001322053 731560985231641500247885)
                ·
                  refine ⟨274335369461865562592957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731560985231641500247885 274335369461865562592957)
                  ·
                    rfl

theorem cell21_1202099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 4, 3].length) (baseStart_1202099 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202099 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202099 prefixEnd_1202099 := by exact prefixLift 1202099
  have htrace : WordTrace (prefixWord ++ tailWord_1202099) baseStart_1202099 baseEnd_1202099 := by
    simpa [prefixWord, tailWord_1202099, baseEnd_1202099] using wordTrace_append hprefix tailTrace_1202099
  have hstable : (prefixWord ++ tailWord_1202099).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202099).length < 2 ^ (prefixWord ++ tailWord_1202099).sum := by decide
  have hdescent : baseEnd_1202099 < baseStart_1202099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202209 : List Nat := [1, 2, 3, 2, 4, 1, 3, 2, 3]
def baseStart_1202209 : Nat := 118140960795 + 1202209 * 2 ^ 59
def prefixEnd_1202209 : Nat := 4983230072969 + 3 ^ 40 * 1202209 * 2
def baseEnd_1202209 : Nat := 274360472960529815759399

theorem tailTrace_1202209 : CollatzResearch.WordTrace tailWord_1202209 prefixEnd_1202209 274360472960529815759399 := by
  unfold tailWord_1202209
  simp only [CollatzResearch.WordTrace]
  refine ⟨43848164501609588795873681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29232109667739725863915787 43848164501609588795873681)
  ·
    refine ⟨32886123376207191596905261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43848164501609588795873681 32886123376207191596905261)
    ·
      refine ⟨12332296266077696848839473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32886123376207191596905261 12332296266077696848839473)
      ·
        refine ⟨9249222199558272636629605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12332296266077696848839473 9249222199558272636629605)
        ·
          refine ⟨1734229162417176119368051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9249222199558272636629605 1734229162417176119368051)
          ·
            refine ⟨2601343743625764179052077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734229162417176119368051 2601343743625764179052077)
            ·
              refine ⟨975503903859661567144529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2601343743625764179052077 975503903859661567144529)
              ·
                refine ⟨731627927894746175358397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 975503903859661567144529 731627927894746175358397)
                ·
                  refine ⟨274360472960529815759399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731627927894746175358397 274360472960529815759399)
                  ·
                    rfl

theorem cell21_1202209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 3, 2, 3].length) (baseStart_1202209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202209 prefixEnd_1202209 := by exact prefixLift 1202209
  have htrace : WordTrace (prefixWord ++ tailWord_1202209) baseStart_1202209 baseEnd_1202209 := by
    simpa [prefixWord, tailWord_1202209, baseEnd_1202209] using wordTrace_append hprefix tailTrace_1202209
  have hstable : (prefixWord ++ tailWord_1202209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202209).length < 2 ^ (prefixWord ++ tailWord_1202209).sum := by decide
  have hdescent : baseEnd_1202209 < baseStart_1202209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202248 : List Nat := [2, 1, 3, 1, 1, 1, 2, 4, 6]
def baseStart_1202248 : Nat := 118140960795 + 1202248 * 2 ^ 59
def prefixEnd_1202248 : Nat := 4983230072969 + 3 ^ 40 * 1202248 * 2
def baseEnd_1202248 : Nat := 274369373291874414609319

theorem tailTrace_1202248 : CollatzResearch.WordTrace tailWord_1202248 prefixEnd_1202248 274369373291874414609319 := by
  unfold tailWord_1202248
  simp only [CollatzResearch.WordTrace]
  refine ⟨21924793474234149228271699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29233057965645532304362265 21924793474234149228271699)
  ·
    refine ⟨32887190211351223842407549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21924793474234149228271699 32887190211351223842407549)
    ·
      refine ⟨12332696329256708940902831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32887190211351223842407549 12332696329256708940902831)
      ·
        refine ⟨18499044493885063411354247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12332696329256708940902831 18499044493885063411354247)
        ·
          refine ⟨27748566740827595117031371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18499044493885063411354247 27748566740827595117031371)
          ·
            refine ⟨41622850111241392675547057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27748566740827595117031371 41622850111241392675547057)
            ·
              refine ⟨31217137583431044506660293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41622850111241392675547057 31217137583431044506660293)
              ·
                refine ⟨5853213296893320844998805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31217137583431044506660293 5853213296893320844998805)
                ·
                  refine ⟨274369373291874414609319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5853213296893320844998805 274369373291874414609319)
                  ·
                    rfl

theorem cell21_1202248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_1202248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202248 prefixEnd_1202248 := by exact prefixLift 1202248
  have htrace : WordTrace (prefixWord ++ tailWord_1202248) baseStart_1202248 baseEnd_1202248 := by
    simpa [prefixWord, tailWord_1202248, baseEnd_1202248] using wordTrace_append hprefix tailTrace_1202248
  have hstable : (prefixWord ++ tailWord_1202248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202248).length < 2 ^ (prefixWord ++ tailWord_1202248).sum := by decide
  have hdescent : baseEnd_1202248 < baseStart_1202248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202265 : List Nat := [1, 2, 1, 2, 2, 1, 6, 2, 4]
def baseStart_1202265 : Nat := 118140960795 + 1202265 * 2 ^ 59
def prefixEnd_1202265 : Nat := 4983230072969 + 3 ^ 40 * 1202265 * 2
def baseEnd_1202265 : Nat := 274373252923486162825951

theorem tailTrace_1202265 : CollatzResearch.WordTrace tailWord_1202265 prefixEnd_1202265 274373252923486162825951 := by
  unfold tailWord_1202265
  simp only [CollatzResearch.WordTrace]
  refine ⟨43850206989406710359912249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29233471326271140239941499 43850206989406710359912249)
  ·
    refine ⟨32887655242055032769934187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43850206989406710359912249 32887655242055032769934187)
    ·
      refine ⟨49331482863082549154901281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32887655242055032769934187 49331482863082549154901281)
      ·
        refine ⟨36998612147311911866175961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49331482863082549154901281 36998612147311911866175961)
        ·
          refine ⟨27748959110483933899631971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36998612147311911866175961 27748959110483933899631971)
          ·
            refine ⟨41623438665725900849447957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27748959110483933899631971 41623438665725900849447957)
            ·
              refine ⟨1951098687455901602317873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41623438665725900849447957 1951098687455901602317873)
              ·
                refine ⟨1463324015591926201738405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1951098687455901602317873 1463324015591926201738405)
                ·
                  refine ⟨274373252923486162825951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1463324015591926201738405 274373252923486162825951)
                  ·
                    rfl

theorem cell21_1202265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 2, 4].length) (baseStart_1202265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202265 prefixEnd_1202265 := by exact prefixLift 1202265
  have htrace : WordTrace (prefixWord ++ tailWord_1202265) baseStart_1202265 baseEnd_1202265 := by
    simpa [prefixWord, tailWord_1202265, baseEnd_1202265] using wordTrace_append hprefix tailTrace_1202265
  have hstable : (prefixWord ++ tailWord_1202265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202265).length < 2 ^ (prefixWord ++ tailWord_1202265).sum := by decide
  have hdescent : baseEnd_1202265 < baseStart_1202265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202268 : List Nat := [2, 2, 4, 1, 1, 3, 1, 4, 3]
def baseStart_1202268 : Nat := 118140960795 + 1202268 * 2 ^ 59
def prefixEnd_1202268 : Nat := 4983230072969 + 3 ^ 40 * 1202268 * 2
def baseEnd_1202268 : Nat := 274373937564358824275945

theorem tailTrace_1202268 : CollatzResearch.WordTrace tailWord_1202268 prefixEnd_1202268 274373937564358824275945 := by
  unfold tailWord_1202268
  simp only [CollatzResearch.WordTrace]
  refine ⟨21925158204197920936135729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29233544272263894581514305 21925158204197920936135729)
  ·
    refine ⟨16443868653148440702101797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21925158204197920936135729 16443868653148440702101797)
    ·
      refine ⟨3083225372465332631644087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16443868653148440702101797 3083225372465332631644087)
      ·
        refine ⟨4624838058697998947466131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3083225372465332631644087 4624838058697998947466131)
        ·
          refine ⟨6937257088046998421199197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4624838058697998947466131 6937257088046998421199197)
          ·
            refine ⟨2601471408017624407949699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6937257088046998421199197 2601471408017624407949699)
            ·
              refine ⟨3902207112026436611924549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2601471408017624407949699 3902207112026436611924549)
              ·
                refine ⟨731663833504956864735853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3902207112026436611924549 731663833504956864735853)
                ·
                  refine ⟨274373937564358824275945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 731663833504956864735853 274373937564358824275945)
                  ·
                    rfl

theorem cell21_1202268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_1202268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202268 prefixEnd_1202268 := by exact prefixLift 1202268
  have htrace : WordTrace (prefixWord ++ tailWord_1202268) baseStart_1202268 baseEnd_1202268 := by
    simpa [prefixWord, tailWord_1202268, baseEnd_1202268] using wordTrace_append hprefix tailTrace_1202268
  have hstable : (prefixWord ++ tailWord_1202268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202268).length < 2 ^ (prefixWord ++ tailWord_1202268).sum := by decide
  have hdescent : baseEnd_1202268 < baseStart_1202268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202327 : List Nat := [1, 1, 3, 3, 4, 1, 2, 1, 5]
def baseStart_1202327 : Nat := 118140960795 + 1202327 * 2 ^ 59
def prefixEnd_1202327 : Nat := 4983230072969 + 3 ^ 40 * 1202327 * 2
def baseEnd_1202327 : Nat := 274387402168187832792491

theorem tailTrace_1202327 : CollatzResearch.WordTrace tailWord_1202327 prefixEnd_1202327 274387402168187832792491 := by
  unfold tailWord_1202327
  simp only [CollatzResearch.WordTrace]
  refine ⟨43852468315182094948669235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29234978876788063299112823 43852468315182094948669235)
  ·
    refine ⟨65778702472773142423003853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43852468315182094948669235 65778702472773142423003853)
    ·
      refine ⟨24667013427289928408626445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65778702472773142423003853 24667013427289928408626445)
      ·
        refine ⟨9250130035233723153234917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24667013427289928408626445 9250130035233723153234917)
        ·
          refine ⟨1734399381606323091231547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9250130035233723153234917 1734399381606323091231547)
          ·
            refine ⟨2601599072409484636847321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734399381606323091231547 2601599072409484636847321)
            ·
              refine ⟨1951199304307113477635491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2601599072409484636847321 1951199304307113477635491)
              ·
                refine ⟨2926798956460670216453237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951199304307113477635491 2926798956460670216453237)
                ·
                  refine ⟨274387402168187832792491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2926798956460670216453237 274387402168187832792491)
                  ·
                    rfl

theorem cell21_1202327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 5].length) (baseStart_1202327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202327 prefixEnd_1202327 := by exact prefixLift 1202327
  have htrace : WordTrace (prefixWord ++ tailWord_1202327) baseStart_1202327 baseEnd_1202327 := by
    simpa [prefixWord, tailWord_1202327, baseEnd_1202327] using wordTrace_append hprefix tailTrace_1202327
  have hstable : (prefixWord ++ tailWord_1202327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202327).length < 2 ^ (prefixWord ++ tailWord_1202327).sum := by decide
  have hdescent : baseEnd_1202327 < baseStart_1202327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202372 : List Nat := [2, 3, 3, 1, 2, 3, 7]
def baseStart_1202372 : Nat := 118140960795 + 1202372 * 2 ^ 59
def prefixEnd_1202372 : Nat := 4983230072969 + 3 ^ 40 * 1202372 * 2
def baseEnd_1202372 : Nat := 30488630197919750504711

theorem tailTrace_1202372 : CollatzResearch.WordTrace tailWord_1202372 prefixEnd_1202372 30488630197919750504711 := by
  unfold tailWord_1202372
  simp only [CollatzResearch.WordTrace]
  refine ⟨21927054800009533817028685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29236073066679378422704913 21927054800009533817028685)
  ·
    refine ⟨8222645550003575181385757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21927054800009533817028685 8222645550003575181385757)
    ·
      refine ⟨3083492081251340693019659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8222645550003575181385757 3083492081251340693019659)
      ·
        refine ⟨4625238121877011039529489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3083492081251340693019659 4625238121877011039529489)
        ·
          refine ⟨3468928591407758279647117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4625238121877011039529489 3468928591407758279647117)
          ·
            refine ⟨1300848221777909354867669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3468928591407758279647117 1300848221777909354867669)
            ·
              refine ⟨30488630197919750504711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1300848221777909354867669 30488630197919750504711)
              ·
                rfl

theorem cell21_1202372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 7].length) (baseStart_1202372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202372 prefixEnd_1202372 := by exact prefixLift 1202372
  have htrace : WordTrace (prefixWord ++ tailWord_1202372) baseStart_1202372 baseEnd_1202372 := by
    simpa [prefixWord, tailWord_1202372, baseEnd_1202372] using wordTrace_append hprefix tailTrace_1202372
  have hstable : (prefixWord ++ tailWord_1202372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202372).length < 2 ^ (prefixWord ++ tailWord_1202372).sum := by decide
  have hdescent : baseEnd_1202372 < baseStart_1202372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202434 : List Nat := [3, 4, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1202434 : Nat := 118140960795 + 1202434 * 2 ^ 59
def prefixEnd_1202434 : Nat := 4983230072969 + 3 ^ 40 * 1202434 * 2
def baseEnd_1202434 : Nat := 274411821025979424508939

theorem tailTrace_1202434 : CollatzResearch.WordTrace tailWord_1202434 prefixEnd_1202434 274411821025979424508939 := by
  unfold tailWord_1202434
  simp only [CollatzResearch.WordTrace]
  refine ⟨10964092731448613055703589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29237580617196301481876237 10964092731448613055703589)
  ·
    refine ⟨2055767387146614947944423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10964092731448613055703589 2055767387146614947944423)
    ·
      refine ⟨3083651080719922421916635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2055767387146614947944423 3083651080719922421916635)
      ·
        refine ⟨4625476621079883632874953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3083651080719922421916635 4625476621079883632874953)
        ·
          refine ⟨3469107465809912724656215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4625476621079883632874953 3469107465809912724656215)
          ·
            refine ⟨5203661198714869086984323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3469107465809912724656215 5203661198714869086984323)
            ·
              refine ⟨7805491798072303630476485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5203661198714869086984323 7805491798072303630476485)
              ·
                refine ⟨1463529712138556930714341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7805491798072303630476485 1463529712138556930714341)
                ·
                  refine ⟨274411821025979424508939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1463529712138556930714341 274411821025979424508939)
                  ·
                    rfl

theorem cell21_1202434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1202434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202434 prefixEnd_1202434 := by exact prefixLift 1202434
  have htrace : WordTrace (prefixWord ++ tailWord_1202434) baseStart_1202434 baseEnd_1202434 := by
    simpa [prefixWord, tailWord_1202434, baseEnd_1202434] using wordTrace_append hprefix tailTrace_1202434
  have hstable : (prefixWord ++ tailWord_1202434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202434).length < 2 ^ (prefixWord ++ tailWord_1202434).sum := by decide
  have hdescent : baseEnd_1202434 < baseStart_1202434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202569 : List Nat := [1, 2, 1, 1, 6, 2, 1, 3, 4]
def baseStart_1202569 : Nat := 118140960795 + 1202569 * 2 ^ 59
def prefixEnd_1202569 : Nat := 4983230072969 + 3 ^ 40 * 1202569 * 2
def baseEnd_1202569 : Nat := 274442629865249189758663

theorem tailTrace_1202569 : CollatzResearch.WordTrace tailWord_1202569 prefixEnd_1202569 274442629865249189758663 := by
  unfold tailWord_1202569
  simp only [CollatzResearch.WordTrace]
  refine ⟨43861294780305370278978761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29240863186870246852652507 43861294780305370278978761)
  ·
    refine ⟨32895971085229027709234071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43861294780305370278978761 32895971085229027709234071)
    ·
      refine ⟨49343956627843541563851107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32895971085229027709234071 49343956627843541563851107)
      ·
        refine ⟨74015934941765312345776661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49343956627843541563851107 74015934941765312345776661)
        ·
          refine ⟨3469496950395249016208281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 74015934941765312345776661 3469496950395249016208281)
          ·
            refine ⟨2602122712796436762156211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3469496950395249016208281 2602122712796436762156211)
            ·
              refine ⟨3903184069194655143234317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2602122712796436762156211 3903184069194655143234317)
              ·
                refine ⟨1463694025947995678712869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3903184069194655143234317 1463694025947995678712869)
                ·
                  refine ⟨274442629865249189758663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1463694025947995678712869 274442629865249189758663)
                  ·
                    rfl

theorem cell21_1202569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 3, 4].length) (baseStart_1202569 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202569 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202569 prefixEnd_1202569 := by exact prefixLift 1202569
  have htrace : WordTrace (prefixWord ++ tailWord_1202569) baseStart_1202569 baseEnd_1202569 := by
    simpa [prefixWord, tailWord_1202569, baseEnd_1202569] using wordTrace_append hprefix tailTrace_1202569
  have hstable : (prefixWord ++ tailWord_1202569).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202569).length < 2 ^ (prefixWord ++ tailWord_1202569).sum := by decide
  have hdescent : baseEnd_1202569 < baseStart_1202569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202659 : List Nat := [1, 1, 1, 6, 3, 1, 8]
def baseStart_1202659 : Nat := 118140960795 + 1202659 * 2 ^ 59
def prefixEnd_1202659 : Nat := 4983230072969 + 3 ^ 40 * 1202659 * 2
def baseEnd_1202659 : Nat := 30495907676825448139831

theorem tailTrace_1202659 : CollatzResearch.WordTrace tailWord_1202659 prefixEnd_1202659 30495907676825448139831 := by
  unfold tailWord_1202659
  simp only [CollatzResearch.WordTrace]
  refine ⟨43864577349979315649755031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29243051566652877099836687 43864577349979315649755031)
  ·
    refine ⟨65796866024968973474632547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43864577349979315649755031 65796866024968973474632547)
    ·
      refine ⟨98695299037453460211948821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65796866024968973474632547 98695299037453460211948821)
      ·
        refine ⟨4626342142380630947435101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 98695299037453460211948821 4626342142380630947435101)
        ·
          refine ⟨1734878303392736605288163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4626342142380630947435101 1734878303392736605288163)
          ·
            refine ⟨2602317455089104907932245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1734878303392736605288163 2602317455089104907932245)
            ·
              refine ⟨30495907676825448139831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2602317455089104907932245 30495907676825448139831)
              ·
                rfl

theorem cell21_1202659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 8].length) (baseStart_1202659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202659 prefixEnd_1202659 := by exact prefixLift 1202659
  have htrace : WordTrace (prefixWord ++ tailWord_1202659) baseStart_1202659 baseEnd_1202659 := by
    simpa [prefixWord, tailWord_1202659, baseEnd_1202659] using wordTrace_append hprefix tailTrace_1202659
  have hstable : (prefixWord ++ tailWord_1202659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202659).length < 2 ^ (prefixWord ++ tailWord_1202659).sum := by decide
  have hdescent : baseEnd_1202659 < baseStart_1202659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202724 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 5]
def baseStart_1202724 : Nat := 118140960795 + 1202724 * 2 ^ 59
def prefixEnd_1202724 : Nat := 4983230072969 + 3 ^ 40 * 1202724 * 2
def baseEnd_1202724 : Nat := 274478002977003364675013

theorem tailTrace_1202724 : CollatzResearch.WordTrace tailWord_1202724 prefixEnd_1202724 274478002977003364675013 := by
  unfold tailWord_1202724
  simp only [CollatzResearch.WordTrace]
  refine ⟨21933474047371915875435613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29244632063162554500580817 21933474047371915875435613)
  ·
    refine ⟨8225052767764468453288355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21933474047371915875435613 8225052767764468453288355)
    ·
      refine ⟨12337579151646702679932533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8225052767764468453288355 12337579151646702679932533)
      ·
        refine ⟨1156648045466878376243675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12337579151646702679932533 1156648045466878376243675)
        ·
          refine ⟨1734972068200317564365513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1156648045466878376243675 1734972068200317564365513)
          ·
            refine ⟨1301229051150238173274135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1734972068200317564365513 1301229051150238173274135)
            ·
              refine ⟨1951843576725357259911203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301229051150238173274135 1951843576725357259911203)
              ·
                refine ⟨2927765365088035889866805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1951843576725357259911203 2927765365088035889866805)
                ·
                  refine ⟨274478002977003364675013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2927765365088035889866805 274478002977003364675013)
                  ·
                    rfl

theorem cell21_1202724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_1202724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202724 prefixEnd_1202724 := by exact prefixLift 1202724
  have htrace : WordTrace (prefixWord ++ tailWord_1202724) baseStart_1202724 baseEnd_1202724 := by
    simpa [prefixWord, tailWord_1202724, baseEnd_1202724] using wordTrace_append hprefix tailTrace_1202724
  have hstable : (prefixWord ++ tailWord_1202724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202724).length < 2 ^ (prefixWord ++ tailWord_1202724).sum := by decide
  have hdescent : baseEnd_1202724 < baseStart_1202724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202763 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 8]
def baseStart_1202763 : Nat := 118140960795 + 1202763 * 2 ^ 59
def prefixEnd_1202763 : Nat := 4983230072969 + 3 ^ 40 * 1202763 * 2
def baseEnd_1202763 : Nat := 274486903308347963524933

theorem tailTrace_1202763 : CollatzResearch.WordTrace tailWord_1202763 prefixEnd_1202763 274486903308347963524933 := by
  unfold tailWord_1202763
  simp only [CollatzResearch.WordTrace]
  refine ⟨43868370541602541411540943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29245580361068360941027295 43868370541602541411540943)
  ·
    refine ⟨65802555812403812117311415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43868370541602541411540943 65802555812403812117311415)
    ·
      refine ⟨98703833718605718175967123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65802555812403812117311415 98703833718605718175967123)
      ·
        refine ⟨148055750577908577263950685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98703833718605718175967123 148055750577908577263950685)
        ·
          refine ⟨55520906466715716473981507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 148055750577908577263950685 55520906466715716473981507)
          ·
            refine ⟨83281359700073574710972261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55520906466715716473981507 83281359700073574710972261)
            ·
              refine ⟨15615254943763795258307299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 83281359700073574710972261 15615254943763795258307299)
              ·
                refine ⟨23422882415645692887460949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15615254943763795258307299 23422882415645692887460949)
                ·
                  refine ⟨274486903308347963524933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23422882415645692887460949 274486903308347963524933)
                  ·
                    rfl

theorem cell21_1202763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 8].length) (baseStart_1202763 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202763 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202763 prefixEnd_1202763 := by exact prefixLift 1202763
  have htrace : WordTrace (prefixWord ++ tailWord_1202763) baseStart_1202763 baseEnd_1202763 := by
    simpa [prefixWord, tailWord_1202763, baseEnd_1202763] using wordTrace_append hprefix tailTrace_1202763
  have hstable : (prefixWord ++ tailWord_1202763).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202763).length < 2 ^ (prefixWord ++ tailWord_1202763).sum := by decide
  have hdescent : baseEnd_1202763 < baseStart_1202763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202786 : List Nat := [3, 3, 2, 3, 2, 1, 1, 6]
def baseStart_1202786 : Nat := 118140960795 + 1202786 * 2 ^ 59
def prefixEnd_1202786 : Nat := 4983230072969 + 3 ^ 40 * 1202786 * 2
def baseEnd_1202786 : Nat := 91497384073901678213851

theorem tailTrace_1202786 : CollatzResearch.WordTrace tailWord_1202786 prefixEnd_1202786 91497384073901678213851 := by
  unfold tailWord_1202786
  simp only [CollatzResearch.WordTrace]
  refine ⟨10967302355129804084907053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29246139613679477559752141 10967302355129804084907053)
  ·
    refine ⟨4112738383173676531840145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10967302355129804084907053 4112738383173676531840145)
    ·
      refine ⟨3084553787380257398880109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4112738383173676531840145 3084553787380257398880109)
      ·
        refine ⟨1156707670267596524580041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3084553787380257398880109 1156707670267596524580041)
        ·
          refine ⟨867530752700697393435031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1156707670267596524580041 867530752700697393435031)
          ·
            refine ⟨1301296129051046090152547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867530752700697393435031 1301296129051046090152547)
            ·
              refine ⟨1951944193576569135228821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301296129051046090152547 1951944193576569135228821)
              ·
                refine ⟨91497384073901678213851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1951944193576569135228821 91497384073901678213851)
                ·
                  rfl

theorem cell21_1202786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_1202786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202786 prefixEnd_1202786 := by exact prefixLift 1202786
  have htrace : WordTrace (prefixWord ++ tailWord_1202786) baseStart_1202786 baseEnd_1202786 := by
    simpa [prefixWord, tailWord_1202786, baseEnd_1202786] using wordTrace_append hprefix tailTrace_1202786
  have hstable : (prefixWord ++ tailWord_1202786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202786).length < 2 ^ (prefixWord ++ tailWord_1202786).sum := by decide
  have hdescent : baseEnd_1202786 < baseStart_1202786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202797 : List Nat := [1, 5, 1, 1, 3, 1, 2, 3, 4]
def baseStart_1202797 : Nat := 118140960795 + 1202797 * 2 ^ 59
def prefixEnd_1202797 : Nat := 4983230072969 + 3 ^ 40 * 1202797 * 2
def baseEnd_1202797 : Nat := 274494662571571459958197

theorem tailTrace_1202797 : CollatzResearch.WordTrace tailWord_1202797 prefixEnd_1202797 274494662571571459958197 := by
  unfold tailWord_1202797
  simp only [CollatzResearch.WordTrace]
  refine ⟨43869610623479365218278645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29246407082319576812185763 43869610623479365218278645)
  ·
    refine ⟨4112775995951190489213623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43869610623479365218278645 4112775995951190489213623)
    ·
      refine ⟨6169163993926785733820435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4112775995951190489213623 6169163993926785733820435)
      ·
        refine ⟨9253745990890178600730653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6169163993926785733820435 9253745990890178600730653)
        ·
          refine ⟨3470154746583816975273995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9253745990890178600730653 3470154746583816975273995)
          ·
            refine ⟨5205232119875725462910993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3470154746583816975273995 5205232119875725462910993)
            ·
              refine ⟨3903924089906794097183245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5205232119875725462910993 3903924089906794097183245)
              ·
                refine ⟨1463971533715047786443717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3903924089906794097183245 1463971533715047786443717)
                ·
                  refine ⟨274494662571571459958197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1463971533715047786443717 274494662571571459958197)
                  ·
                    rfl

theorem cell21_1202797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_1202797 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202797 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202797 prefixEnd_1202797 := by exact prefixLift 1202797
  have htrace : WordTrace (prefixWord ++ tailWord_1202797) baseStart_1202797 baseEnd_1202797 := by
    simpa [prefixWord, tailWord_1202797, baseEnd_1202797] using wordTrace_append hprefix tailTrace_1202797
  have hstable : (prefixWord ++ tailWord_1202797).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202797).length < 2 ^ (prefixWord ++ tailWord_1202797).sum := by decide
  have hdescent : baseEnd_1202797 < baseStart_1202797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202893 : List Nat := [1, 6, 2, 1, 3, 1, 1, 1, 5]
def baseStart_1202893 : Nat := 118140960795 + 1202893 * 2 ^ 59
def prefixEnd_1202893 : Nat := 4983230072969 + 3 ^ 40 * 1202893 * 2
def baseEnd_1202893 : Nat := 274516571079496626358001

theorem tailTrace_1202893 : CollatzResearch.WordTrace tailWord_1202893 prefixEnd_1202893 274516571079496626358001 := by
  unfold tailWord_1202893
  simp only [CollatzResearch.WordTrace]
  refine ⟨43873112031131573613773333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29248741354087715742515555 43873112031131573613773333)
  ·
    refine ⟨2056552126459292513145625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43873112031131573613773333 2056552126459292513145625)
    ·
      refine ⟨1542414094844469384859219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2056552126459292513145625 1542414094844469384859219)
      ·
        refine ⟨2313621142266704077288829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1542414094844469384859219 2313621142266704077288829)
        ·
          refine ⟨867607928350014028983311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2313621142266704077288829 867607928350014028983311)
          ·
            refine ⟨1301411892525021043474967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867607928350014028983311 1301411892525021043474967)
            ·
              refine ⟨1952117838787531565212451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301411892525021043474967 1952117838787531565212451)
              ·
                refine ⟨2928176758181297347818677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952117838787531565212451 2928176758181297347818677)
                ·
                  refine ⟨274516571079496626358001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2928176758181297347818677 274516571079496626358001)
                  ·
                    rfl

theorem cell21_1202893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_1202893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202893 prefixEnd_1202893 := by exact prefixLift 1202893
  have htrace : WordTrace (prefixWord ++ tailWord_1202893) baseStart_1202893 baseEnd_1202893 := by
    simpa [prefixWord, tailWord_1202893, baseEnd_1202893] using wordTrace_append hprefix tailTrace_1202893
  have hstable : (prefixWord ++ tailWord_1202893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202893).length < 2 ^ (prefixWord ++ tailWord_1202893).sum := by decide
  have hdescent : baseEnd_1202893 < baseStart_1202893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202952 : List Nat := [2, 1, 3, 2, 2, 4, 2, 2, 3]
def baseStart_1202952 : Nat := 118140960795 + 1202952 * 2 ^ 59
def prefixEnd_1202952 : Nat := 4983230072969 + 3 ^ 40 * 1202952 * 2
def baseEnd_1202952 : Nat := 274530035683325634874547

theorem tailTrace_1202952 : CollatzResearch.WordTrace tailWord_1202952 prefixEnd_1202952 274530035683325634874547 := by
  unfold tailWord_1202952
  simp only [CollatzResearch.WordTrace]
  refine ⟨21937631968958913345085555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29250175958611884460114073 21937631968958913345085555)
  ·
    refine ⟨32906447953438370017628333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21937631968958913345085555 32906447953438370017628333)
    ·
      refine ⟨12339917982539388756610625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32906447953438370017628333 12339917982539388756610625)
      ·
        refine ⟨9254938486904541567457969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12339917982539388756610625 9254938486904541567457969)
        ·
          refine ⟨6941203865178406175593477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9254938486904541567457969 6941203865178406175593477)
          ·
            refine ⟨1301475724720951157923777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6941203865178406175593477 1301475724720951157923777)
            ·
              refine ⟨976106793540713368442833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1301475724720951157923777 976106793540713368442833)
              ·
                refine ⟨732080095155535026332125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 976106793540713368442833 732080095155535026332125)
                ·
                  refine ⟨274530035683325634874547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 732080095155535026332125 274530035683325634874547)
                  ·
                    rfl

theorem cell21_1202952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 2, 3].length) (baseStart_1202952 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202952 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202952 prefixEnd_1202952 := by exact prefixLift 1202952
  have htrace : WordTrace (prefixWord ++ tailWord_1202952) baseStart_1202952 baseEnd_1202952 := by
    simpa [prefixWord, tailWord_1202952, baseEnd_1202952] using wordTrace_append hprefix tailTrace_1202952
  have hstable : (prefixWord ++ tailWord_1202952).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202952).length < 2 ^ (prefixWord ++ tailWord_1202952).sum := by decide
  have hdescent : baseEnd_1202952 < baseStart_1202952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202977 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 5]
def baseStart_1202977 : Nat := 118140960795 + 1202977 * 2 ^ 59
def prefixEnd_1202977 : Nat := 4983230072969 + 3 ^ 40 * 1202977 * 2
def baseEnd_1202977 : Nat := 274535741023931146957829

theorem tailTrace_1202977 : CollatzResearch.WordTrace tailWord_1202977 prefixEnd_1202977 274535741023931146957829 := by
  unfold tailWord_1202977
  simp only [CollatzResearch.WordTrace]
  refine ⟨43876175762827255959831185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29250783841884837306554123 43876175762827255959831185)
  ·
    refine ⟨32907131822120441969873389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43876175762827255959831185 32907131822120441969873389)
    ·
      refine ⟨12340174433295165738702521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32907131822120441969873389 12340174433295165738702521)
      ·
        refine ⟨9255130824971374304026891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12340174433295165738702521 9255130824971374304026891)
        ·
          refine ⟨13882696237457061456040337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9255130824971374304026891 13882696237457061456040337)
          ·
            refine ⟨10412022178092796092030253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13882696237457061456040337 10412022178092796092030253)
            ·
              refine ⟨3904508316784798534511345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10412022178092796092030253 3904508316784798534511345)
              ·
                refine ⟨2928381237588598900883509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3904508316784798534511345 2928381237588598900883509)
                ·
                  refine ⟨274535741023931146957829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2928381237588598900883509 274535741023931146957829)
                  ·
                    rfl

theorem cell21_1202977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 5].length) (baseStart_1202977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202977 prefixEnd_1202977 := by exact prefixLift 1202977
  have htrace : WordTrace (prefixWord ++ tailWord_1202977) baseStart_1202977 baseEnd_1202977 := by
    simpa [prefixWord, tailWord_1202977, baseEnd_1202977] using wordTrace_append hprefix tailTrace_1202977
  have hstable : (prefixWord ++ tailWord_1202977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202977).length < 2 ^ (prefixWord ++ tailWord_1202977).sum := by decide
  have hdescent : baseEnd_1202977 < baseStart_1202977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1202980 : List Nat := [2, 3, 1, 3, 3, 1, 3, 5]
def baseStart_1202980 : Nat := 118140960795 + 1202980 * 2 ^ 59
def prefixEnd_1202980 : Nat := 4983230072969 + 3 ^ 40 * 1202980 * 2
def baseEnd_1202980 : Nat := 91512141888267936135941

theorem tailTrace_1202980 : CollatzResearch.WordTrace tailWord_1202980 prefixEnd_1202980 91512141888267936135941 := by
  unfold tailWord_1202980
  simp only [CollatzResearch.WordTrace]
  refine ⟨21938142590908193736095197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29250856787877591648126929 21938142590908193736095197)
  ·
    refine ⟨8226803471590572651035699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21938142590908193736095197 8226803471590572651035699)
    ·
      refine ⟨12340205207385858976553549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8226803471590572651035699 12340205207385858976553549)
      ·
        refine ⟨4627576952769697116207581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12340205207385858976553549 4627576952769697116207581)
        ·
          refine ⟨1735341357288636418577843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4627576952769697116207581 1735341357288636418577843)
          ·
            refine ⟨2603012035932954627866765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1735341357288636418577843 2603012035932954627866765)
            ·
              refine ⟨976129513474857985450037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2603012035932954627866765 976129513474857985450037)
              ·
                refine ⟨91512141888267936135941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 976129513474857985450037 91512141888267936135941)
                ·
                  rfl

theorem cell21_1202980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 1, 3, 5].length) (baseStart_1202980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1202980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1202980 prefixEnd_1202980 := by exact prefixLift 1202980
  have htrace : WordTrace (prefixWord ++ tailWord_1202980) baseStart_1202980 baseEnd_1202980 := by
    simpa [prefixWord, tailWord_1202980, baseEnd_1202980] using wordTrace_append hprefix tailTrace_1202980
  have hstable : (prefixWord ++ tailWord_1202980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1202980).length < 2 ^ (prefixWord ++ tailWord_1202980).sum := by decide
  have hdescent : baseEnd_1202980 < baseStart_1202980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1202980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203067 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 6]
def baseStart_1203067 : Nat := 118140960795 + 1203067 * 2 ^ 59
def prefixEnd_1203067 : Nat := 4983230072969 + 3 ^ 40 * 1203067 * 2
def baseEnd_1203067 : Nat := 274556280250110990457645

theorem tailTrace_1203067 : CollatzResearch.WordTrace tailWord_1203067 prefixEnd_1203067 274556280250110990457645 := by
  unfold tailWord_1203067
  simp only [CollatzResearch.WordTrace]
  refine ⟨43879458332501201330607455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29252972221667467553738303 43879458332501201330607455)
  ·
    refine ⟨65819187498751801995911183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43879458332501201330607455 65819187498751801995911183)
    ·
      refine ⟨98728781248127702993866775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65819187498751801995911183 98728781248127702993866775)
      ·
        refine ⟨148093171872191554490800163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98728781248127702993866775 148093171872191554490800163)
        ·
          refine ⟨222139757808287331736200245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 148093171872191554490800163 222139757808287331736200245)
          ·
            refine ⟨20825602294526937350268773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 222139757808287331736200245 20825602294526937350268773)
            ·
              refine ⟨3904800430223800753175395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20825602294526937350268773 3904800430223800753175395)
              ·
                refine ⟨5857200645335701129763093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3904800430223800753175395 5857200645335701129763093)
                ·
                  refine ⟨274556280250110990457645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5857200645335701129763093 274556280250110990457645)
                  ·
                    rfl

theorem cell21_1203067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 6].length) (baseStart_1203067 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203067 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203067 prefixEnd_1203067 := by exact prefixLift 1203067
  have htrace : WordTrace (prefixWord ++ tailWord_1203067) baseStart_1203067 baseEnd_1203067 := by
    simpa [prefixWord, tailWord_1203067, baseEnd_1203067] using wordTrace_append hprefix tailTrace_1203067
  have hstable : (prefixWord ++ tailWord_1203067).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203067).length < 2 ^ (prefixWord ++ tailWord_1203067).sum := by decide
  have hdescent : baseEnd_1203067 < baseStart_1203067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203121 : List Nat := [1, 2, 2, 4, 4, 1, 2, 2, 3]
def baseStart_1203121 : Nat := 118140960795 + 1203121 * 2 ^ 59
def prefixEnd_1203121 : Nat := 4983230072969 + 3 ^ 40 * 1203121 * 2
def baseEnd_1203121 : Nat := 274568603785818896557535

theorem tailTrace_1203121 : CollatzResearch.WordTrace tailWord_1203121 prefixEnd_1203121 274568603785818896557535 := by
  unfold tailWord_1203121
  simp only [CollatzResearch.WordTrace]
  refine ⟨43881427874305568553073217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29254285249537045702048811 43881427874305568553073217)
  ·
    refine ⟨32911070905729176414804913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43881427874305568553073217 32911070905729176414804913)
    ·
      refine ⟨24683303179296882311103685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32911070905729176414804913 24683303179296882311103685)
      ·
        refine ⟨4628119346118165433331941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24683303179296882311103685 4628119346118165433331941)
        ·
          refine ⟨867772377397156018749739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4628119346118165433331941 867772377397156018749739)
          ·
            refine ⟨1301658566095734028124609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 867772377397156018749739 1301658566095734028124609)
            ·
              refine ⟨976243924571800521093457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1301658566095734028124609 976243924571800521093457)
              ·
                refine ⟨732182943428850390820093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 976243924571800521093457 732182943428850390820093)
                ·
                  refine ⟨274568603785818896557535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 732182943428850390820093 274568603785818896557535)
                  ·
                    rfl

theorem cell21_1203121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 2, 2, 3].length) (baseStart_1203121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203121 prefixEnd_1203121 := by exact prefixLift 1203121
  have htrace : WordTrace (prefixWord ++ tailWord_1203121) baseStart_1203121 baseEnd_1203121 := by
    simpa [prefixWord, tailWord_1203121, baseEnd_1203121] using wordTrace_append hprefix tailTrace_1203121
  have hstable : (prefixWord ++ tailWord_1203121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203121).length < 2 ^ (prefixWord ++ tailWord_1203121).sum := by decide
  have hdescent : baseEnd_1203121 < baseStart_1203121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203236 : List Nat := [2, 3, 1, 4, 1, 1, 2, 1, 6]
def baseStart_1203236 : Nat := 118140960795 + 1203236 * 2 ^ 59
def prefixEnd_1203236 : Nat := 4983230072969 + 3 ^ 40 * 1203236 * 2
def baseEnd_1203236 : Nat := 274594848352604252140633

theorem tailTrace_1203236 : CollatzResearch.WordTrace tailWord_1203236 prefixEnd_1203236 274594848352604252140633 := by
  unfold tailWord_1203236
  simp only [CollatzResearch.WordTrace]
  refine ⟨21942811134444471596754781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29257081512592628795673041 21942811134444471596754781)
  ·
    refine ⟨8228554175416676848783043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21942811134444471596754781 8228554175416676848783043)
    ·
      refine ⟨12342831263125015273174565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8228554175416676848783043 12342831263125015273174565)
      ·
        refine ⟨2314280861835940363720231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12342831263125015273174565 2314280861835940363720231)
        ·
          refine ⟨3471421292753910545580347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2314280861835940363720231 3471421292753910545580347)
          ·
            refine ⟨5207131939130865818370521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3471421292753910545580347 5207131939130865818370521)
            ·
              refine ⟨3905348954348149363777891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5207131939130865818370521 3905348954348149363777891)
              ·
                refine ⟨5858023431522224045666837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3905348954348149363777891 5858023431522224045666837)
                ·
                  refine ⟨274594848352604252140633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5858023431522224045666837 274594848352604252140633)
                  ·
                    rfl

theorem cell21_1203236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_1203236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203236 prefixEnd_1203236 := by exact prefixLift 1203236
  have htrace : WordTrace (prefixWord ++ tailWord_1203236) baseStart_1203236 baseEnd_1203236 := by
    simpa [prefixWord, tailWord_1203236, baseEnd_1203236] using wordTrace_append hprefix tailTrace_1203236
  have hstable : (prefixWord ++ tailWord_1203236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203236).length < 2 ^ (prefixWord ++ tailWord_1203236).sum := by decide
  have hdescent : baseEnd_1203236 < baseStart_1203236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203239 : List Nat := [1, 1, 7, 1, 1, 3, 1, 1, 5]
def baseStart_1203239 : Nat := 118140960795 + 1203239 * 2 ^ 59
def prefixEnd_1203239 : Nat := 4983230072969 + 3 ^ 40 * 1203239 * 2
def baseEnd_1203239 : Nat := 274595532993476913590627

theorem tailTrace_1203239 : CollatzResearch.WordTrace tailWord_1203239 prefixEnd_1203239 274595532993476913590627 := by
  unfold tailWord_1203239
  simp only [CollatzResearch.WordTrace]
  refine ⟨43885731687878074705868771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29257154458585383137245847 43885731687878074705868771)
  ·
    refine ⟨65828597531817112058803157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43885731687878074705868771 65828597531817112058803157)
    ·
      refine ⟨1542857754651963563878199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 65828597531817112058803157 1542857754651963563878199)
      ·
        refine ⟨2314286631977945345817299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1542857754651963563878199 2314286631977945345817299)
        ·
          refine ⟨3471429947966918018725949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2314286631977945345817299 3471429947966918018725949)
          ·
            refine ⟨1301786230487594257022231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3471429947966918018725949 1301786230487594257022231)
            ·
              refine ⟨1952679345731391385533347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1301786230487594257022231 1952679345731391385533347)
              ·
                refine ⟨2929019018597087078300021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952679345731391385533347 2929019018597087078300021)
                ·
                  refine ⟨274595532993476913590627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2929019018597087078300021 274595532993476913590627)
                  ·
                    rfl

theorem cell21_1203239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 5].length) (baseStart_1203239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203239 prefixEnd_1203239 := by exact prefixLift 1203239
  have htrace : WordTrace (prefixWord ++ tailWord_1203239) baseStart_1203239 baseEnd_1203239 := by
    simpa [prefixWord, tailWord_1203239, baseEnd_1203239] using wordTrace_append hprefix tailTrace_1203239
  have hstable : (prefixWord ++ tailWord_1203239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203239).length < 2 ^ (prefixWord ++ tailWord_1203239).sum := by decide
  have hdescent : baseEnd_1203239 < baseStart_1203239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203250 : List Nat := [3, 2, 1, 1, 2, 2, 4, 6]
def baseStart_1203250 : Nat := 118140960795 + 1203250 * 2 ^ 59
def prefixEnd_1203250 : Nat := 4983230072969 + 3 ^ 40 * 1203250 * 2
def baseEnd_1203250 : Nat := 91532681114447779635757

theorem tailTrace_1203250 : CollatzResearch.WordTrace tailWord_1203250 prefixEnd_1203250 91532681114447779635757 := by
  unfold tailWord_1203250
  simp only [CollatzResearch.WordTrace]
  refine ⟨10971533222709555896129801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29257421927225482389679469 10971533222709555896129801)
  ·
    refine ⟨8228649917032166922097351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10971533222709555896129801 8228649917032166922097351)
    ·
      refine ⟨12342974875548250383146027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8228649917032166922097351 12342974875548250383146027)
      ·
        refine ⟨18514462313322375574719041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12342974875548250383146027 18514462313322375574719041)
        ·
          refine ⟨13885846734991781681039281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18514462313322375574719041 13885846734991781681039281)
          ·
            refine ⟨10414385051243836260779461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13885846734991781681039281 10414385051243836260779461)
            ·
              refine ⟨1952697197108219298896149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10414385051243836260779461 1952697197108219298896149)
              ·
                refine ⟨91532681114447779635757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1952697197108219298896149 91532681114447779635757)
                ·
                  rfl

theorem cell21_1203250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 6].length) (baseStart_1203250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203250 prefixEnd_1203250 := by exact prefixLift 1203250
  have htrace : WordTrace (prefixWord ++ tailWord_1203250) baseStart_1203250 baseEnd_1203250 := by
    simpa [prefixWord, tailWord_1203250, baseEnd_1203250] using wordTrace_append hprefix tailTrace_1203250
  have hstable : (prefixWord ++ tailWord_1203250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203250).length < 2 ^ (prefixWord ++ tailWord_1203250).sum := by decide
  have hdescent : baseEnd_1203250 < baseStart_1203250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203264 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 7]
def baseStart_1203264 : Nat := 118140960795 + 1203264 * 2 ^ 59
def prefixEnd_1203264 : Nat := 4983230072969 + 3 ^ 40 * 1203264 * 2
def baseEnd_1203264 : Nat := 274601238334082425673909

theorem tailTrace_1203264 : CollatzResearch.WordTrace tailWord_1203264 prefixEnd_1203264 274601238334082425673909 := by
  unfold tailWord_1203264
  simp only [CollatzResearch.WordTrace]
  refine ⟨21943321756393751987764423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29257762341858335983685897 21943321756393751987764423)
  ·
    refine ⟨32914982634590627981646635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21943321756393751987764423 32914982634590627981646635)
    ·
      refine ⟨49372473951885941972469953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32914982634590627981646635 49372473951885941972469953)
      ·
        refine ⟨37029355463914456479352465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49372473951885941972469953 37029355463914456479352465)
        ·
          refine ⟨27772016597935842359514349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37029355463914456479352465 27772016597935842359514349)
          ·
            refine ⟨10414506224225940884817881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27772016597935842359514349 10414506224225940884817881)
            ·
              refine ⟨7810879668169455663613411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10414506224225940884817881 7810879668169455663613411)
              ·
                refine ⟨11716319502254183495420117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7810879668169455663613411 11716319502254183495420117)
                ·
                  refine ⟨274601238334082425673909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11716319502254183495420117 274601238334082425673909)
                  ·
                    rfl

theorem cell21_1203264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_1203264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203264 prefixEnd_1203264 := by exact prefixLift 1203264
  have htrace : WordTrace (prefixWord ++ tailWord_1203264) baseStart_1203264 baseEnd_1203264 := by
    simpa [prefixWord, tailWord_1203264, baseEnd_1203264] using wordTrace_append hprefix tailTrace_1203264
  have hstable : (prefixWord ++ tailWord_1203264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203264).length < 2 ^ (prefixWord ++ tailWord_1203264).sum := by decide
  have hdescent : baseEnd_1203264 < baseStart_1203264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203357 : List Nat := [1, 4, 2, 1, 1, 2, 4, 1, 5]
def baseStart_1203357 : Nat := 118140960795 + 1203357 * 2 ^ 59
def prefixEnd_1203357 : Nat := 4983230072969 + 3 ^ 40 * 1203357 * 2
def baseEnd_1203357 : Nat := 274622462201134930623719

theorem tailTrace_1203357 : CollatzResearch.WordTrace tailWord_1203357 prefixEnd_1203357 274622462201134930623719 := by
  unfold tailWord_1203357
  simp only [CollatzResearch.WordTrace]
  refine ⟨43890035501450580858664325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29260023667633720572442883 43890035501450580858664325)
  ·
    refine ⟨8229381656521983910999561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43890035501450580858664325 8229381656521983910999561)
    ·
      refine ⟨6172036242391487933249671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8229381656521983910999561 6172036242391487933249671)
      ·
        refine ⟨9258054363587231899874507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6172036242391487933249671 9258054363587231899874507)
        ·
          refine ⟨13887081545380847849811761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9258054363587231899874507 13887081545380847849811761)
          ·
            refine ⟨10415311159035635887358821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13887081545380847849811761 10415311159035635887358821)
            ·
              refine ⟨1952870842319181728879779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10415311159035635887358821 1952870842319181728879779)
              ·
                refine ⟨2929306263478772593319669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1952870842319181728879779 2929306263478772593319669)
                ·
                  refine ⟨274622462201134930623719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2929306263478772593319669 274622462201134930623719)
                  ·
                    rfl

theorem cell21_1203357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_1203357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203357 prefixEnd_1203357 := by exact prefixLift 1203357
  have htrace : WordTrace (prefixWord ++ tailWord_1203357) baseStart_1203357 baseEnd_1203357 := by
    simpa [prefixWord, tailWord_1203357, baseEnd_1203357] using wordTrace_append hprefix tailTrace_1203357
  have hstable : (prefixWord ++ tailWord_1203357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203357).length < 2 ^ (prefixWord ++ tailWord_1203357).sum := by decide
  have hdescent : baseEnd_1203357 < baseStart_1203357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203402 : List Nat := [3, 1, 2, 1, 3, 4, 7]
def baseStart_1203402 : Nat := 118140960795 + 1203402 * 2 ^ 59
def prefixEnd_1203402 : Nat := 4983230072969 + 3 ^ 40 * 1203402 * 2
def baseEnd_1203402 : Nat := 30514747979358316930403

theorem tailTrace_1203402 : CollatzResearch.WordTrace tailWord_1203402 prefixEnd_1203402 30514747979358316930403 := by
  unfold tailWord_1203402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10972919196571888386013115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29261117857525035696034973 10972919196571888386013115)
  ·
    refine ⟨16459378794857832579019673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10972919196571888386013115 16459378794857832579019673)
    ·
      refine ⟨12344534096143374434264755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16459378794857832579019673 12344534096143374434264755)
      ·
        refine ⟨18516801144215061651397133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12344534096143374434264755 18516801144215061651397133)
        ·
          refine ⟨6943800429080648119273925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18516801144215061651397133 6943800429080648119273925)
          ·
            refine ⟨1301962580452621522363861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6943800429080648119273925 1301962580452621522363861)
            ·
              refine ⟨30514747979358316930403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1301962580452621522363861 30514747979358316930403)
              ·
                rfl

theorem cell21_1203402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 7].length) (baseStart_1203402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203402 prefixEnd_1203402 := by exact prefixLift 1203402
  have htrace : WordTrace (prefixWord ++ tailWord_1203402) baseStart_1203402 baseEnd_1203402 := by
    simpa [prefixWord, tailWord_1203402, baseEnd_1203402] using wordTrace_append hprefix tailTrace_1203402
  have hstable : (prefixWord ++ tailWord_1203402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203402).length < 2 ^ (prefixWord ++ tailWord_1203402).sum := by decide
  have hdescent : baseEnd_1203402 < baseStart_1203402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203467 : List Nat := [1, 1, 1, 1, 5, 5, 2, 2, 3]
def baseStart_1203467 : Nat := 118140960795 + 1203467 * 2 ^ 59
def prefixEnd_1203467 : Nat := 4983230072969 + 3 ^ 40 * 1203467 * 2
def baseEnd_1203467 : Nat := 274647565699799183790161

theorem tailTrace_1203467 : CollatzResearch.WordTrace tailWord_1203467 prefixEnd_1203467 274647565699799183790161 := by
  unfold tailWord_1203467
  simp only [CollatzResearch.WordTrace]
  refine ⟨43894047531052069645168655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29262698354034713096779103 43894047531052069645168655)
  ·
    refine ⟨65841071296578104467752983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43894047531052069645168655 65841071296578104467752983)
    ·
      refine ⟨98761606944867156701629475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65841071296578104467752983 98761606944867156701629475)
      ·
        refine ⟨148142410417300735052444213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98761606944867156701629475 148142410417300735052444213)
        ·
          refine ⟨13888350976621943911166645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 148142410417300735052444213 13888350976621943911166645)
          ·
            refine ⟨1302032904058307241671873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13888350976621943911166645 1302032904058307241671873)
            ·
              refine ⟨976524678043730431253905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1302032904058307241671873 976524678043730431253905)
              ·
                refine ⟨732393508532797823440429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 976524678043730431253905 732393508532797823440429)
                ·
                  refine ⟨274647565699799183790161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 732393508532797823440429 274647565699799183790161)
                  ·
                    rfl

theorem cell21_1203467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 5, 2, 2, 3].length) (baseStart_1203467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203467 prefixEnd_1203467 := by exact prefixLift 1203467
  have htrace : WordTrace (prefixWord ++ tailWord_1203467) baseStart_1203467 baseEnd_1203467 := by
    simpa [prefixWord, tailWord_1203467, baseEnd_1203467] using wordTrace_append hprefix tailTrace_1203467
  have hstable : (prefixWord ++ tailWord_1203467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203467).length < 2 ^ (prefixWord ++ tailWord_1203467).sum := by decide
  have hdescent : baseEnd_1203467 < baseStart_1203467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203537 : List Nat := [1, 2, 2, 1, 4, 1, 2, 8]
def baseStart_1203537 : Nat := 118140960795 + 1203537 * 2 ^ 59
def prefixEnd_1203537 : Nat := 4983230072969 + 3 ^ 40 * 1203537 * 2
def baseEnd_1203537 : Nat := 91554513551164872541117

theorem tailTrace_1203537 : CollatzResearch.WordTrace tailWord_1203537 prefixEnd_1203537 91554513551164872541117 := by
  unfold tailWord_1203537
  simp only [CollatzResearch.WordTrace]
  refine ⟨43896600640798471600216865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29264400427198981066811243 43896600640798471600216865)
  ·
    refine ⟨32922450480598853700162649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43896600640798471600216865 32922450480598853700162649)
    ·
      refine ⟨24691837860449140275121987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32922450480598853700162649 24691837860449140275121987)
      ·
        refine ⟨37037756790673710412682981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24691837860449140275121987 37037756790673710412682981)
        ·
          refine ⟨6944579398251320702378059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37037756790673710412682981 6944579398251320702378059)
          ·
            refine ⟨10416869097376981053567089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6944579398251320702378059 10416869097376981053567089)
            ·
              refine ⟨7812651823032735790175317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10416869097376981053567089 7812651823032735790175317)
              ·
                refine ⟨91554513551164872541117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7812651823032735790175317 91554513551164872541117)
                ·
                  rfl

theorem cell21_1203537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 8].length) (baseStart_1203537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203537 prefixEnd_1203537 := by exact prefixLift 1203537
  have htrace : WordTrace (prefixWord ++ tailWord_1203537) baseStart_1203537 baseEnd_1203537 := by
    simpa [prefixWord, tailWord_1203537, baseEnd_1203537] using wordTrace_append hprefix tailTrace_1203537
  have hstable : (prefixWord ++ tailWord_1203537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203537).length < 2 ^ (prefixWord ++ tailWord_1203537).sum := by decide
  have hdescent : baseEnd_1203537 < baseStart_1203537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203554 : List Nat := [3, 3, 2, 1, 1, 1, 3, 7]
def baseStart_1203554 : Nat := 118140960795 + 1203554 * 2 ^ 59
def prefixEnd_1203554 : Nat := 4983230072969 + 3 ^ 40 * 1203554 * 2
def baseEnd_1203554 : Nat := 91555806761702121946661

theorem tailTrace_1203554 : CollatzResearch.WordTrace tailWord_1203554 prefixEnd_1203554 91555806761702121946661 := by
  unfold tailWord_1203554
  simp only [CollatzResearch.WordTrace]
  refine ⟨10974305170434220875896429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29264813787824589002390477 10974305170434220875896429)
  ·
    refine ⟨4115364438912832828461161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10974305170434220875896429 4115364438912832828461161)
    ·
      refine ⟨3086523329184624621345871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4115364438912832828461161 3086523329184624621345871)
      ·
        refine ⟨4629784993776936932018807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3086523329184624621345871 4629784993776936932018807)
        ·
          refine ⟨6944677490665405398028211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4629784993776936932018807 6944677490665405398028211)
          ·
            refine ⟨10417016235998108097042317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6944677490665405398028211 10417016235998108097042317)
            ·
              refine ⟨3906381088499290536390869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10417016235998108097042317 3906381088499290536390869)
              ·
                refine ⟨91555806761702121946661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3906381088499290536390869 91555806761702121946661)
                ·
                  rfl

theorem cell21_1203554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_1203554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203554 prefixEnd_1203554 := by exact prefixLift 1203554
  have htrace : WordTrace (prefixWord ++ tailWord_1203554) baseStart_1203554 baseEnd_1203554 := by
    simpa [prefixWord, tailWord_1203554, baseEnd_1203554] using wordTrace_append hprefix tailTrace_1203554
  have hstable : (prefixWord ++ tailWord_1203554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203554).length < 2 ^ (prefixWord ++ tailWord_1203554).sum := by decide
  have hdescent : baseEnd_1203554 < baseStart_1203554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203560 : List Nat := [2, 1, 4, 2, 4, 1, 1, 3, 3]
def baseStart_1203560 : Nat := 118140960795 + 1203560 * 2 ^ 59
def prefixEnd_1203560 : Nat := 4983230072969 + 3 ^ 40 * 1203560 * 2
def baseEnd_1203560 : Nat := 274668789566851688739971

theorem tailTrace_1203560 : CollatzResearch.WordTrace tailWord_1203560 prefixEnd_1203560 274668789566851688739971 := by
  unfold tailWord_1203560
  simp only [CollatzResearch.WordTrace]
  refine ⟨21948719759857573264152067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29264959679810097685536089 21948719759857573264152067)
  ·
    refine ⟨32923079639786359896228101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21948719759857573264152067 32923079639786359896228101)
    ·
      refine ⟨6173077432459942480542769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32923079639786359896228101 6173077432459942480542769)
      ·
        refine ⟨4629808074344956860407077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6173077432459942480542769 4629808074344956860407077)
        ·
          refine ⟨868089013939679411326327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4629808074344956860407077 868089013939679411326327)
          ·
            refine ⟨1302133520909519116989491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868089013939679411326327 1302133520909519116989491)
            ·
              refine ⟨1953200281364278675484237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1302133520909519116989491 1953200281364278675484237)
              ·
                refine ⟨732450105511604503306589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1953200281364278675484237 732450105511604503306589)
                ·
                  refine ⟨274668789566851688739971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 732450105511604503306589 274668789566851688739971)
                  ·
                    rfl

theorem cell21_1203560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 3, 3].length) (baseStart_1203560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203560 prefixEnd_1203560 := by exact prefixLift 1203560
  have htrace : WordTrace (prefixWord ++ tailWord_1203560) baseStart_1203560 baseEnd_1203560 := by
    simpa [prefixWord, tailWord_1203560, baseEnd_1203560] using wordTrace_append hprefix tailTrace_1203560
  have hstable : (prefixWord ++ tailWord_1203560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203560).length < 2 ^ (prefixWord ++ tailWord_1203560).sum := by decide
  have hdescent : baseEnd_1203560 < baseStart_1203560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203720 : List Nat := [2, 1, 3, 2, 1, 1, 4, 2, 5]
def baseStart_1203720 : Nat := 118140960795 + 1203720 * 2 ^ 59
def prefixEnd_1203720 : Nat := 4983230072969 + 3 ^ 40 * 1203720 * 2
def baseEnd_1203720 : Nat := 274705303746726966072977

theorem tailTrace_1203720 : CollatzResearch.WordTrace tailWord_1203720 prefixEnd_1203720 274705303746726966072977 := by
  unfold tailWord_1203720
  simp only [CollatzResearch.WordTrace]
  refine ⟨21951637599567746927064307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29268850132756995902752409 21951637599567746927064307)
  ·
    refine ⟨32927456399351620390596461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21951637599567746927064307 32927456399351620390596461)
    ·
      refine ⟨12347796149756857646473673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32927456399351620390596461 12347796149756857646473673)
      ·
        refine ⟨9260847112317643234855255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12347796149756857646473673 9260847112317643234855255)
        ·
          refine ⟨13891270668476464852282883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9260847112317643234855255 13891270668476464852282883)
          ·
            refine ⟨20836906002714697278424325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13891270668476464852282883 20836906002714697278424325)
            ·
              refine ⟨3906919875509005739704561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20836906002714697278424325 3906919875509005739704561)
              ·
                refine ⟨2930189906631754304778421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3906919875509005739704561 2930189906631754304778421)
                ·
                  refine ⟨274705303746726966072977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2930189906631754304778421 274705303746726966072977)
                  ·
                    rfl

theorem cell21_1203720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_1203720 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203720 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203720 prefixEnd_1203720 := by exact prefixLift 1203720
  have htrace : WordTrace (prefixWord ++ tailWord_1203720) baseStart_1203720 baseEnd_1203720 := by
    simpa [prefixWord, tailWord_1203720, baseEnd_1203720] using wordTrace_append hprefix tailTrace_1203720
  have hstable : (prefixWord ++ tailWord_1203720).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203720).length < 2 ^ (prefixWord ++ tailWord_1203720).sum := by decide
  have hdescent : baseEnd_1203720 < baseStart_1203720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203723 : List Nat := [1, 1, 1, 1, 8, 2, 2, 5]
def baseStart_1203723 : Nat := 118140960795 + 1203723 * 2 ^ 59
def prefixEnd_1203723 : Nat := 4983230072969 + 3 ^ 40 * 1203723 * 2
def baseEnd_1203723 : Nat := 91568662795866542507657

theorem tailTrace_1203723 : CollatzResearch.WordTrace tailWord_1203723 prefixEnd_1203723 91568662795866542507657 := by
  unfold tailWord_1203723
  simp only [CollatzResearch.WordTrace]
  refine ⟨43903384618124625366487823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29268923078749750244325215 43903384618124625366487823)
  ·
    refine ⟨65855076927186938049731735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43903384618124625366487823 65855076927186938049731735)
    ·
      refine ⟨98782615390780407074597603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65855076927186938049731735 98782615390780407074597603)
      ·
        refine ⟨148173923086170610611896405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98782615390780407074597603 148173923086170610611896405)
        ·
          refine ⟨1736413161166061843108161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 148173923086170610611896405 1736413161166061843108161)
          ·
            refine ⟨1302309870874546382331121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1736413161166061843108161 1302309870874546382331121)
            ·
              refine ⟨976732403155909786748341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1302309870874546382331121 976732403155909786748341)
              ·
                refine ⟨91568662795866542507657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 976732403155909786748341 91568662795866542507657)
                ·
                  rfl

theorem cell21_1203723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 5].length) (baseStart_1203723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203723 prefixEnd_1203723 := by exact prefixLift 1203723
  have htrace : WordTrace (prefixWord ++ tailWord_1203723) baseStart_1203723 baseEnd_1203723 := by
    simpa [prefixWord, tailWord_1203723, baseEnd_1203723] using wordTrace_append hprefix tailTrace_1203723
  have hstable : (prefixWord ++ tailWord_1203723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203723).length < 2 ^ (prefixWord ++ tailWord_1203723).sum := by decide
  have hdescent : baseEnd_1203723 < baseStart_1203723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203765 : List Nat := [1, 3, 3, 1, 1, 3, 1, 8]
def baseStart_1203765 : Nat := 118140960795 + 1203765 * 2 ^ 59
def prefixEnd_1203765 : Nat := 4983230072969 + 3 ^ 40 * 1203765 * 2
def baseEnd_1203765 : Nat := 91571857786605629274295

theorem tailTrace_1203765 : CollatzResearch.WordTrace tailWord_1203765 prefixEnd_1203765 91571857786605629274295 := by
  unfold tailWord_1203765
  simp only [CollatzResearch.WordTrace]
  refine ⟨43904916483972466539516749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29269944322648311026344499 43904916483972466539516749)
  ·
    refine ⟨16464343681489674952318781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43904916483972466539516749 16464343681489674952318781)
    ·
      refine ⟨6174128880558628107119543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16464343681489674952318781 6174128880558628107119543)
      ·
        refine ⟨9261193320837942160679315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6174128880558628107119543 9261193320837942160679315)
        ·
          refine ⟨13891789981256913241018973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9261193320837942160679315 13891789981256913241018973)
          ·
            refine ⟨5209421242971342465382115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13891789981256913241018973 5209421242971342465382115)
            ·
              refine ⟨7814131864457013698073173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5209421242971342465382115 7814131864457013698073173)
              ·
                refine ⟨91571857786605629274295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7814131864457013698073173 91571857786605629274295)
                ·
                  rfl

theorem cell21_1203765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 8].length) (baseStart_1203765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203765 prefixEnd_1203765 := by exact prefixLift 1203765
  have htrace : WordTrace (prefixWord ++ tailWord_1203765) baseStart_1203765 baseEnd_1203765 := by
    simpa [prefixWord, tailWord_1203765, baseEnd_1203765] using wordTrace_append hprefix tailTrace_1203765
  have hstable : (prefixWord ++ tailWord_1203765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203765).length < 2 ^ (prefixWord ++ tailWord_1203765).sum := by decide
  have hdescent : baseEnd_1203765 < baseStart_1203765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203768 : List Nat := [2, 1, 2, 1, 4, 2, 4, 1, 4]
def baseStart_1203768 : Nat := 118140960795 + 1203768 * 2 ^ 59
def prefixEnd_1203768 : Nat := 4983230072969 + 3 ^ 40 * 1203768 * 2
def baseEnd_1203768 : Nat := 274716258000689549272879

theorem tailTrace_1203768 : CollatzResearch.WordTrace tailWord_1203768 prefixEnd_1203768 274716258000689549272879 := by
  unfold tailWord_1203768
  simp only [CollatzResearch.WordTrace]
  refine ⟨21952512951480799025937979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29270017268641065367917305 21952512951480799025937979)
  ·
    refine ⟨32928769427221198538906969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21952512951480799025937979 32928769427221198538906969)
    ·
      refine ⟨24696577070415898904180227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32928769427221198538906969 24696577070415898904180227)
      ·
        refine ⟨37044865605623848356270341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24696577070415898904180227 37044865605623848356270341)
        ·
          refine ⟨6945912301054471566800689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37044865605623848356270341 6945912301054471566800689)
          ·
            refine ⟨5209434225790853675100517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6945912301054471566800689 5209434225790853675100517)
            ·
              refine ⟨976768917335785064081347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5209434225790853675100517 976768917335785064081347)
              ·
                refine ⟨1465153376003677596122021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976768917335785064081347 1465153376003677596122021)
                ·
                  refine ⟨274716258000689549272879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1465153376003677596122021 274716258000689549272879)
                  ·
                    rfl

theorem cell21_1203768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 4, 1, 4].length) (baseStart_1203768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203768 prefixEnd_1203768 := by exact prefixLift 1203768
  have htrace : WordTrace (prefixWord ++ tailWord_1203768) baseStart_1203768 baseEnd_1203768 := by
    simpa [prefixWord, tailWord_1203768, baseEnd_1203768] using wordTrace_append hprefix tailTrace_1203768
  have hstable : (prefixWord ++ tailWord_1203768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203768).length < 2 ^ (prefixWord ++ tailWord_1203768).sum := by decide
  have hdescent : baseEnd_1203768 < baseStart_1203768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203805 : List Nat := [1, 4, 4, 2, 1, 2, 2, 2, 3]
def baseStart_1203805 : Nat := 118140960795 + 1203805 * 2 ^ 59
def prefixEnd_1203805 : Nat := 4983230072969 + 3 ^ 40 * 1203805 * 2
def baseEnd_1203805 : Nat := 274724701904785707156137

theorem tailTrace_1203805 : CollatzResearch.WordTrace tailWord_1203805 prefixEnd_1203805 274724701904785707156137 := by
  unfold tailWord_1203805
  simp only [CollatzResearch.WordTrace]
  refine ⟨43906375403827553370972869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29270916935885035580648579 43906375403827553370972869)
  ·
    refine ⟨8232445388217666257057413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43906375403827553370972869 8232445388217666257057413)
    ·
      refine ⟨1543583510290812423198265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8232445388217666257057413 1543583510290812423198265)
      ·
        refine ⟨1157687632718109317398699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1543583510290812423198265 1157687632718109317398699)
        ·
          refine ⟨1736531449077163976098049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1157687632718109317398699 1736531449077163976098049)
          ·
            refine ⟨1302398586807872982073537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1736531449077163976098049 1302398586807872982073537)
            ·
              refine ⟨976798940105904736555153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1302398586807872982073537 976798940105904736555153)
              ·
                refine ⟨732599205079428552416365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 976798940105904736555153 732599205079428552416365)
                ·
                  refine ⟨274724701904785707156137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 732599205079428552416365 274724701904785707156137)
                  ·
                    rfl

theorem cell21_1203805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 2, 2, 2, 3].length) (baseStart_1203805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203805 prefixEnd_1203805 := by exact prefixLift 1203805
  have htrace : WordTrace (prefixWord ++ tailWord_1203805) baseStart_1203805 baseEnd_1203805 := by
    simpa [prefixWord, tailWord_1203805, baseEnd_1203805] using wordTrace_append hprefix tailTrace_1203805
  have hstable : (prefixWord ++ tailWord_1203805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203805).length < 2 ^ (prefixWord ++ tailWord_1203805).sum := by decide
  have hdescent : baseEnd_1203805 < baseStart_1203805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203858 : List Nat := [3, 2, 3, 1, 3, 1, 8]
def baseStart_1203858 : Nat := 118140960795 + 1203858 * 2 ^ 59
def prefixEnd_1203858 : Nat := 4983230072969 + 3 ^ 40 * 1203858 * 2
def baseEnd_1203858 : Nat := 30526310802985488085855

theorem tailTrace_1203858 : CollatzResearch.WordTrace tailWord_1203858 prefixEnd_1203858 30526310802985488085855 := by
  unfold tailWord_1203858
  simp only [CollatzResearch.WordTrace]
  refine ⟨10977077118158885855663057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29272205648423695615101485 10977077118158885855663057)
  ·
    refine ⟨8232807838619164391747293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10977077118158885855663057 8232807838619164391747293)
    ·
      refine ⟨3087302939482186646905235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8232807838619164391747293 3087302939482186646905235)
      ·
        refine ⟨4630954409223279970357853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3087302939482186646905235 4630954409223279970357853)
        ·
          refine ⟨1736607903458729988884195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4630954409223279970357853 1736607903458729988884195)
          ·
            refine ⟨2604911855188094983326293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1736607903458729988884195 2604911855188094983326293)
            ·
              refine ⟨30526310802985488085855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2604911855188094983326293 30526310802985488085855)
              ·
                rfl

theorem cell21_1203858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 8].length) (baseStart_1203858 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203858 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203858 prefixEnd_1203858 := by exact prefixLift 1203858
  have htrace : WordTrace (prefixWord ++ tailWord_1203858) baseStart_1203858 baseEnd_1203858 := by
    simpa [prefixWord, tailWord_1203858, baseEnd_1203858] using wordTrace_append hprefix tailTrace_1203858
  have hstable : (prefixWord ++ tailWord_1203858).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203858).length < 2 ^ (prefixWord ++ tailWord_1203858).sum := by decide
  have hdescent : baseEnd_1203858 < baseStart_1203858 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203872 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 5]
def baseStart_1203872 : Nat := 118140960795 + 1203872 * 2 ^ 59
def prefixEnd_1203872 : Nat := 4983230072969 + 3 ^ 40 * 1203872 * 2
def baseEnd_1203872 : Nat := 274739992217608479539333

theorem tailTrace_1203872 : CollatzResearch.WordTrace tailWord_1203872 prefixEnd_1203872 274739992217608479539333 := by
  unfold tailWord_1203872
  simp only [CollatzResearch.WordTrace]
  refine ⟨21954409547292411906830935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29272546063056549209107913 21954409547292411906830935)
  ·
    refine ⟨32931614320938617860246403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21954409547292411906830935 32931614320938617860246403)
    ·
      refine ⟨49397421481407926790369605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32931614320938617860246403 49397421481407926790369605)
      ·
        refine ⟨9262016527763986273194301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49397421481407926790369605 9262016527763986273194301)
        ·
          refine ⟨3473256197911494852447863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9262016527763986273194301 3473256197911494852447863)
          ·
            refine ⟨5209884296867242278671795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3473256197911494852447863 5209884296867242278671795)
            ·
              refine ⟨7814826445300863418007693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5209884296867242278671795 7814826445300863418007693)
              ·
                refine ⟨2930559916987823781752885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7814826445300863418007693 2930559916987823781752885)
                ·
                  refine ⟨274739992217608479539333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2930559916987823781752885 274739992217608479539333)
                  ·
                    rfl

theorem cell21_1203872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_1203872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203872 prefixEnd_1203872 := by exact prefixLift 1203872
  have htrace : WordTrace (prefixWord ++ tailWord_1203872) baseStart_1203872 baseEnd_1203872 := by
    simpa [prefixWord, tailWord_1203872, baseEnd_1203872] using wordTrace_append hprefix tailTrace_1203872
  have hstable : (prefixWord ++ tailWord_1203872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203872).length < 2 ^ (prefixWord ++ tailWord_1203872).sum := by decide
  have hdescent : baseEnd_1203872 < baseStart_1203872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203937 : List Nat := [1, 2, 3, 1, 5, 2, 2, 1, 4]
def baseStart_1203937 : Nat := 118140960795 + 1203937 * 2 ^ 59
def prefixEnd_1203937 : Nat := 4983230072969 + 3 ^ 40 * 1203937 * 2
def baseEnd_1203937 : Nat := 274754826103182810955867

theorem tailTrace_1203937 : CollatzResearch.WordTrace tailWord_1203937 prefixEnd_1203937 274754826103182810955867 := by
  unfold tailWord_1203937
  simp only [CollatzResearch.WordTrace]
  refine ⟨43911189839349339914778065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29274126559566226609852043 43911189839349339914778065)
  ·
    refine ⟨32933392379512004936083549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43911189839349339914778065 32933392379512004936083549)
    ·
      refine ⟨12350022142317001851031331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32933392379512004936083549 12350022142317001851031331)
      ·
        refine ⟨18525033213475502776546997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12350022142317001851031331 18525033213475502776546997)
        ·
          refine ⟨1736721863763328385301281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 18525033213475502776546997 1736721863763328385301281)
          ·
            refine ⟨1302541397822496288975961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1736721863763328385301281 1302541397822496288975961)
            ·
              refine ⟨976906048366872216731971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1302541397822496288975961 976906048366872216731971)
              ·
                refine ⟨1465359072550308325097957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 976906048366872216731971 1465359072550308325097957)
                ·
                  refine ⟨274754826103182810955867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1465359072550308325097957 274754826103182810955867)
                  ·
                    rfl

theorem cell21_1203937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 1, 4].length) (baseStart_1203937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203937 prefixEnd_1203937 := by exact prefixLift 1203937
  have htrace : WordTrace (prefixWord ++ tailWord_1203937) baseStart_1203937 baseEnd_1203937 := by
    simpa [prefixWord, tailWord_1203937, baseEnd_1203937] using wordTrace_append hprefix tailTrace_1203937
  have hstable : (prefixWord ++ tailWord_1203937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203937).length < 2 ^ (prefixWord ++ tailWord_1203937).sum := by decide
  have hdescent : baseEnd_1203937 < baseStart_1203937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203974 : List Nat := [6, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_1203974 : Nat := 118140960795 + 1203974 * 2 ^ 59
def prefixEnd_1203974 : Nat := 4983230072969 + 3 ^ 40 * 1203974 * 2
def baseEnd_1203974 : Nat := 274763270007278968839125

theorem tailTrace_1203974 : CollatzResearch.WordTrace tailWord_1203974 prefixEnd_1203974 274763270007278968839125 := by
  unfold tailWord_1203974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1372266854381727976058593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29275026226810196822583317 1372266854381727976058593)
  ·
    refine ⟨1029200140786295982043945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1372266854381727976058593 1029200140786295982043945)
    ·
      refine ⟨771900105589721986532959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1029200140786295982043945 771900105589721986532959)
      ·
        refine ⟨1157850158384582979799439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 771900105589721986532959 1157850158384582979799439)
        ·
          refine ⟨1736775237576874469699159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1157850158384582979799439 1736775237576874469699159)
          ·
            refine ⟨2605162856365311704548739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1736775237576874469699159 2605162856365311704548739)
            ·
              refine ⟨3907744284547967556823109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2605162856365311704548739 3907744284547967556823109)
              ·
                refine ⟨732702053352743916904333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3907744284547967556823109 732702053352743916904333)
                ·
                  refine ⟨274763270007278968839125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 732702053352743916904333 274763270007278968839125)
                  ·
                    rfl

theorem cell21_1203974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_1203974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203974 prefixEnd_1203974 := by exact prefixLift 1203974
  have htrace : WordTrace (prefixWord ++ tailWord_1203974) baseStart_1203974 baseEnd_1203974 := by
    simpa [prefixWord, tailWord_1203974, baseEnd_1203974] using wordTrace_append hprefix tailTrace_1203974
  have hstable : (prefixWord ++ tailWord_1203974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203974).length < 2 ^ (prefixWord ++ tailWord_1203974).sum := by decide
  have hdescent : baseEnd_1203974 < baseStart_1203974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1203982 : List Nat := [4, 1, 1, 2, 1, 1, 6, 2, 3]
def baseStart_1203982 : Nat := 118140960795 + 1203982 * 2 ^ 59
def prefixEnd_1203982 : Nat := 4983230072969 + 3 ^ 40 * 1203982 * 2
def baseEnd_1203982 : Nat := 274765095716272732705775

theorem tailTrace_1203982 : CollatzResearch.WordTrace tailWord_1203982 prefixEnd_1203982 274765095716272732705775 := by
  unfold tailWord_1203982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5489103890523289075020775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29275220749457541733444133 5489103890523289075020775)
  ·
    refine ⟨8233655835784933612531163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5489103890523289075020775 8233655835784933612531163)
    ·
      refine ⟨12350483753677400418796745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8233655835784933612531163 12350483753677400418796745)
      ·
        refine ⟨9262862815258050314097559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12350483753677400418796745 9262862815258050314097559)
        ·
          refine ⟨13894294222887075471146339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9262862815258050314097559 13894294222887075471146339)
          ·
            refine ⟨20841441334330613206719509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13894294222887075471146339 20841441334330613206719509)
            ·
              refine ⟨976942562546747494064977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20841441334330613206719509 976942562546747494064977)
              ·
                refine ⟨732706921910060620548733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 976942562546747494064977 732706921910060620548733)
                ·
                  refine ⟨274765095716272732705775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 732706921910060620548733 274765095716272732705775)
                  ·
                    rfl

theorem cell21_1203982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 6, 2, 3].length) (baseStart_1203982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1203982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1203982 prefixEnd_1203982 := by exact prefixLift 1203982
  have htrace : WordTrace (prefixWord ++ tailWord_1203982) baseStart_1203982 baseEnd_1203982 := by
    simpa [prefixWord, tailWord_1203982, baseEnd_1203982] using wordTrace_append hprefix tailTrace_1203982
  have hstable : (prefixWord ++ tailWord_1203982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1203982).length < 2 ^ (prefixWord ++ tailWord_1203982).sum := by decide
  have hdescent : baseEnd_1203982 < baseStart_1203982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1203982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204100 : List Nat := [2, 3, 2, 1, 1, 1, 5, 1, 5]
def baseStart_1204100 : Nat := 118140960795 + 1204100 * 2 ^ 59
def prefixEnd_1204100 : Nat := 4983230072969 + 3 ^ 40 * 1204100 * 2
def baseEnd_1204100 : Nat := 274792024923930749738867

theorem tailTrace_1204100 : CollatzResearch.WordTrace tailWord_1204100 prefixEnd_1204100 274792024923930749738867 := by
  unfold tailWord_1204100
  simp only [CollatzResearch.WordTrace]
  refine ⟨21958567468879409376480877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29278089958505879168641169 21958567468879409376480877)
  ·
    refine ⟨8234462800829778516180329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21958567468879409376480877 8234462800829778516180329)
    ·
      refine ⟨6175847100622333887135247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8234462800829778516180329 6175847100622333887135247)
      ·
        refine ⟨9263770650933500830702871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6175847100622333887135247 9263770650933500830702871)
        ·
          refine ⟨13895655976400251246054307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9263770650933500830702871 13895655976400251246054307)
          ·
            refine ⟨20843483964600376869081461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13895655976400251246054307 20843483964600376869081461)
            ·
              refine ⟨1954076621681285331476387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20843483964600376869081461 1954076621681285331476387)
              ·
                refine ⟨2931114932521927997214581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1954076621681285331476387 2931114932521927997214581)
                ·
                  refine ⟨274792024923930749738867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2931114932521927997214581 274792024923930749738867)
                  ·
                    rfl

theorem cell21_1204100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_1204100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204100 prefixEnd_1204100 := by exact prefixLift 1204100
  have htrace : WordTrace (prefixWord ++ tailWord_1204100) baseStart_1204100 baseEnd_1204100 := by
    simpa [prefixWord, tailWord_1204100, baseEnd_1204100] using wordTrace_append hprefix tailTrace_1204100
  have hstable : (prefixWord ++ tailWord_1204100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204100).length < 2 ^ (prefixWord ++ tailWord_1204100).sum := by decide
  have hdescent : baseEnd_1204100 < baseStart_1204100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204106 : List Nat := [3, 1, 2, 4, 3, 1, 2, 1, 4]
def baseStart_1204106 : Nat := 118140960795 + 1204106 * 2 ^ 59
def prefixEnd_1204106 : Nat := 4983230072969 + 3 ^ 40 * 1204106 * 2
def baseEnd_1204106 : Nat := 274793394205676072638855

theorem tailTrace_1204106 : CollatzResearch.WordTrace tailWord_1204106 prefixEnd_1204106 274793394205676072638855 := by
  unfold tailWord_1204106
  simp only [CollatzResearch.WordTrace]
  refine ⟨10979338443934270444420043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29278235850491387851786781 10979338443934270444420043)
  ·
    refine ⟨16469007665901405666630065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10979338443934270444420043 16469007665901405666630065)
    ·
      refine ⟨12351755749426054249972549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16469007665901405666630065 12351755749426054249972549)
      ·
        refine ⟨2315954203017385171869853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12351755749426054249972549 2315954203017385171869853)
        ·
          refine ⟨868482826131519439451195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2315954203017385171869853 868482826131519439451195)
          ·
            refine ⟨1302724239197279159176793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868482826131519439451195 1302724239197279159176793)
            ·
              refine ⟨977043179397959369382595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1302724239197279159176793 977043179397959369382595)
              ·
                refine ⟨1465564769096939054073893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 977043179397959369382595 1465564769096939054073893)
                ·
                  refine ⟨274793394205676072638855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1465564769096939054073893 274793394205676072638855)
                  ·
                    rfl

theorem cell21_1204106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 3, 1, 2, 1, 4].length) (baseStart_1204106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204106 prefixEnd_1204106 := by exact prefixLift 1204106
  have htrace : WordTrace (prefixWord ++ tailWord_1204106) baseStart_1204106 baseEnd_1204106 := by
    simpa [prefixWord, tailWord_1204106, baseEnd_1204106] using wordTrace_append hprefix tailTrace_1204106
  have hstable : (prefixWord ++ tailWord_1204106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204106).length < 2 ^ (prefixWord ++ tailWord_1204106).sum := by decide
  have hdescent : baseEnd_1204106 < baseStart_1204106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204159 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 5]
def baseStart_1204159 : Nat := 118140960795 + 1204159 * 2 ^ 59
def prefixEnd_1204159 : Nat := 4983230072969 + 3 ^ 40 * 1204159 * 2
def baseEnd_1204159 : Nat := 274805489527759758255413

theorem tailTrace_1204159 : CollatzResearch.WordTrace tailWord_1204159 prefixEnd_1204159 274805489527759758255413 := by
  unfold tailWord_1204159
  simp only [CollatzResearch.WordTrace]
  refine ⟨43919286844545071829359531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29279524563030047886239687 43919286844545071829359531)
  ·
    refine ⟨65878930266817607744039297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43919286844545071829359531 65878930266817607744039297)
    ·
      refine ⟨49409197700113205808029473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65878930266817607744039297 49409197700113205808029473)
      ·
        refine ⟨37056898275084904356022105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49409197700113205808029473 37056898275084904356022105)
        ·
          refine ⟨27792673706313678267016579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37056898275084904356022105 27792673706313678267016579)
          ·
            refine ⟨41689010559470517400524869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27792673706313678267016579 41689010559470517400524869)
            ·
              refine ⟨7816689479900722012598413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41689010559470517400524869 7816689479900722012598413)
              ·
                refine ⟨2931258554962770754724405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7816689479900722012598413 2931258554962770754724405)
                ·
                  refine ⟨274805489527759758255413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2931258554962770754724405 274805489527759758255413)
                  ·
                    rfl

theorem cell21_1204159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 5].length) (baseStart_1204159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204159 prefixEnd_1204159 := by exact prefixLift 1204159
  have htrace : WordTrace (prefixWord ++ tailWord_1204159) baseStart_1204159 baseEnd_1204159 := by
    simpa [prefixWord, tailWord_1204159, baseEnd_1204159] using wordTrace_append hprefix tailTrace_1204159
  have hstable : (prefixWord ++ tailWord_1204159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204159).length < 2 ^ (prefixWord ++ tailWord_1204159).sum := by decide
  have hdescent : baseEnd_1204159 < baseStart_1204159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204230 : List Nat := [6, 2, 1, 2, 1, 2, 2, 5]
def baseStart_1204230 : Nat := 118140960795 + 1204230 * 2 ^ 59
def prefixEnd_1204230 : Nat := 4983230072969 + 3 ^ 40 * 1204230 * 2
def baseEnd_1204230 : Nat := 91607230898359804190645

theorem tailTrace_1204230 : CollatzResearch.WordTrace tailWord_1204230 prefixEnd_1204230 91607230898359804190645 := by
  unfold tailWord_1204230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1372558638352745342349817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29281250951525233970129429 1372558638352745342349817)
  ·
    refine ⟨1029418978764559006762363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1372558638352745342349817 1029418978764559006762363)
    ·
      refine ⟨1544128468146838510143545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1029418978764559006762363 1544128468146838510143545)
      ·
        refine ⟨1158096351110128882607659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1544128468146838510143545 1158096351110128882607659)
        ·
          refine ⟨1737144526665193323911489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158096351110128882607659 1737144526665193323911489)
          ·
            refine ⟨1302858394998894992933617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1737144526665193323911489 1302858394998894992933617)
            ·
              refine ⟨977143796249171244700213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1302858394998894992933617 977143796249171244700213)
              ·
                refine ⟨91607230898359804190645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 977143796249171244700213 91607230898359804190645)
                ·
                  rfl

theorem cell21_1204230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_1204230 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204230 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204230 prefixEnd_1204230 := by exact prefixLift 1204230
  have htrace : WordTrace (prefixWord ++ tailWord_1204230) baseStart_1204230 baseEnd_1204230 := by
    simpa [prefixWord, tailWord_1204230, baseEnd_1204230] using wordTrace_append hprefix tailTrace_1204230
  have hstable : (prefixWord ++ tailWord_1204230).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204230).length < 2 ^ (prefixWord ++ tailWord_1204230).sum := by decide
  have hdescent : baseEnd_1204230 < baseStart_1204230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204235 : List Nat := [1, 1, 1, 1, 6, 1, 1, 4, 5]
def baseStart_1204235 : Nat := 118140960795 + 1204235 * 2 ^ 59
def prefixEnd_1204235 : Nat := 4983230072969 + 3 ^ 40 * 1204235 * 2
def baseEnd_1204235 : Nat := 274822833763200514988591

theorem tailTrace_1204235 : CollatzResearch.WordTrace tailWord_1204235 prefixEnd_1204235 274822833763200514988591 := by
  unfold tailWord_1204235
  simp only [CollatzResearch.WordTrace]
  refine ⟨43922058792269736809126159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29281372528179824539417439 43922058792269736809126159)
  ·
    refine ⟨65883088188404605213689239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43922058792269736809126159 65883088188404605213689239)
    ·
      refine ⟨98824632282606907820533859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65883088188404605213689239 98824632282606907820533859)
      ·
        refine ⟨148236948423910361730800789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98824632282606907820533859 148236948423910361730800789)
        ·
          refine ⟨6948606957370798206131287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 148236948423910361730800789 6948606957370798206131287)
          ·
            refine ⟨10422910436056197309196931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6948606957370798206131287 10422910436056197309196931)
            ·
              refine ⟨15634365654084295963795397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10422910436056197309196931 15634365654084295963795397)
              ·
                refine ⟨2931443560140805493211637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15634365654084295963795397 2931443560140805493211637)
                ·
                  refine ⟨274822833763200514988591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2931443560140805493211637 274822833763200514988591)
                  ·
                    rfl

theorem cell21_1204235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 5].length) (baseStart_1204235 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204235 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204235 prefixEnd_1204235 := by exact prefixLift 1204235
  have htrace : WordTrace (prefixWord ++ tailWord_1204235) baseStart_1204235 baseEnd_1204235 := by
    simpa [prefixWord, tailWord_1204235, baseEnd_1204235] using wordTrace_append hprefix tailTrace_1204235
  have hstable : (prefixWord ++ tailWord_1204235).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204235).length < 2 ^ (prefixWord ++ tailWord_1204235).sum := by decide
  have hdescent : baseEnd_1204235 < baseStart_1204235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204244 : List Nat := [2, 4, 3, 2, 1, 2, 1, 3, 3]
def baseStart_1204244 : Nat := 118140960795 + 1204244 * 2 ^ 59
def prefixEnd_1204244 : Nat := 4983230072969 + 3 ^ 40 * 1204244 * 2
def baseEnd_1204244 : Nat := 274824887685818499338573

theorem tailTrace_1204244 : CollatzResearch.WordTrace tailWord_1204244 prefixEnd_1204244 274824887685818499338573 := by
  unfold tailWord_1204244
  simp only [CollatzResearch.WordTrace]
  refine ⟨21961193524618565673101893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29281591366158087564135857 21961193524618565673101893)
  ·
    refine ⟨4117723785865981063706605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21961193524618565673101893 4117723785865981063706605)
    ·
      refine ⟨1544146419699742898889977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4117723785865981063706605 1544146419699742898889977)
      ·
        refine ⟨1158109814774807174167483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1544146419699742898889977 1158109814774807174167483)
        ·
          refine ⟨1737164722162210761251225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158109814774807174167483 1737164722162210761251225)
          ·
            refine ⟨1302873541621658070938419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1737164722162210761251225 1302873541621658070938419)
            ·
              refine ⟨1954310312432487106407629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1302873541621658070938419 1954310312432487106407629)
              ·
                refine ⟨732866367162182664902861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1954310312432487106407629 732866367162182664902861)
                ·
                  refine ⟨274824887685818499338573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 732866367162182664902861 274824887685818499338573)
                  ·
                    rfl

theorem cell21_1204244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_1204244 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204244 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204244 prefixEnd_1204244 := by exact prefixLift 1204244
  have htrace : WordTrace (prefixWord ++ tailWord_1204244) baseStart_1204244 baseEnd_1204244 := by
    simpa [prefixWord, tailWord_1204244, baseEnd_1204244] using wordTrace_append hprefix tailTrace_1204244
  have hstable : (prefixWord ++ tailWord_1204244).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204244).length < 2 ^ (prefixWord ++ tailWord_1204244).sum := by decide
  have hdescent : baseEnd_1204244 < baseStart_1204244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204376 : List Nat := [2, 1, 2, 4, 3, 2, 1, 2, 4]
def baseStart_1204376 : Nat := 118140960795 + 1204376 * 2 ^ 59
def prefixEnd_1204376 : Nat := 4983230072969 + 3 ^ 40 * 1204376 * 2
def baseEnd_1204376 : Nat := 274855011884215603138303

theorem tailTrace_1204376 : CollatzResearch.WordTrace tailWord_1204376 prefixEnd_1204376 274855011884215603138303 := by
  unfold tailWord_1204376
  simp only [CollatzResearch.WordTrace]
  refine ⟨21963600742379458945004491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29284800989839278593339321 21963600742379458945004491)
  ·
    refine ⟨32945401113569188417506737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21963600742379458945004491 32945401113569188417506737)
    ·
      refine ⟨24709050835176891313130053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32945401113569188417506737 24709050835176891313130053)
      ·
        refine ⟨4632947031595667121211885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24709050835176891313130053 4632947031595667121211885)
        ·
          refine ⟨1737355136848375170454457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4632947031595667121211885 1737355136848375170454457)
          ·
            refine ⟨1303016352636281377840843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1737355136848375170454457 1303016352636281377840843)
            ·
              refine ⟨1954524528954422066761265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303016352636281377840843 1954524528954422066761265)
              ·
                refine ⟨1465893396715816550070949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1954524528954422066761265 1465893396715816550070949)
                ·
                  refine ⟨274855011884215603138303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1465893396715816550070949 274855011884215603138303)
                  ·
                    rfl

theorem cell21_1204376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_1204376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204376 prefixEnd_1204376 := by exact prefixLift 1204376
  have htrace : WordTrace (prefixWord ++ tailWord_1204376) baseStart_1204376 baseEnd_1204376 := by
    simpa [prefixWord, tailWord_1204376, baseEnd_1204376] using wordTrace_append hprefix tailTrace_1204376
  have hstable : (prefixWord ++ tailWord_1204376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204376).length < 2 ^ (prefixWord ++ tailWord_1204376).sum := by decide
  have hdescent : baseEnd_1204376 < baseStart_1204376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204438 : List Nat := [5, 2, 1, 2, 1, 3, 1, 1, 5]
def baseStart_1204438 : Nat := 118140960795 + 1204438 * 2 ^ 59
def prefixEnd_1204438 : Nat := 4983230072969 + 3 ^ 40 * 1204438 * 2
def baseEnd_1204438 : Nat := 274869161128917273104843

theorem tailTrace_1204438 : CollatzResearch.WordTrace tailWord_1204438 prefixEnd_1204438 274869161128917273104843 := by
  unfold tailWord_1204438
  simp only [CollatzResearch.WordTrace]
  refine ⟨2745591425658393904922873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29286308540356201652510645 2745591425658393904922873)
  ·
    refine ⟨2059193569243795428692155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2745591425658393904922873 2059193569243795428692155)
    ·
      refine ⟨3088790353865693143038233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2059193569243795428692155 3088790353865693143038233)
      ·
        refine ⟨2316592765399269857278675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3088790353865693143038233 2316592765399269857278675)
        ·
          refine ⟨3474889148098904785918013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2316592765399269857278675 3474889148098904785918013)
          ·
            refine ⟨1303083430537089294719255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3474889148098904785918013 1303083430537089294719255)
            ·
              refine ⟨1954625145805633942078883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303083430537089294719255 1954625145805633942078883)
              ·
                refine ⟨2931937718708450913118325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1954625145805633942078883 2931937718708450913118325)
                ·
                  refine ⟨274869161128917273104843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2931937718708450913118325 274869161128917273104843)
                  ·
                    rfl

theorem cell21_1204438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 1, 5].length) (baseStart_1204438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204438 prefixEnd_1204438 := by exact prefixLift 1204438
  have htrace : WordTrace (prefixWord ++ tailWord_1204438) baseStart_1204438 baseEnd_1204438 := by
    simpa [prefixWord, tailWord_1204438, baseEnd_1204438] using wordTrace_append hprefix tailTrace_1204438
  have hstable : (prefixWord ++ tailWord_1204438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204438).length < 2 ^ (prefixWord ++ tailWord_1204438).sum := by decide
  have hdescent : baseEnd_1204438 < baseStart_1204438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204477 : List Nat := [1, 4, 1, 1, 1, 1, 1, 3, 8]
def baseStart_1204477 : Nat := 118140960795 + 1204477 * 2 ^ 59
def prefixEnd_1204477 : Nat := 4983230072969 + 3 ^ 40 * 1204477 * 2
def baseEnd_1204477 : Nat := 274878061460261871954763

theorem tailTrace_1204477 : CollatzResearch.WordTrace tailWord_1204477 prefixEnd_1204477 274878061460261871954763 := by
  unfold tailWord_1204477
  simp only [CollatzResearch.WordTrace]
  refine ⟨43930885257393012139435685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29287256838262008092957123 43930885257393012139435685)
  ·
    refine ⟨8237040985761189776144191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43930885257393012139435685 8237040985761189776144191)
    ·
      refine ⟨12355561478641784664216287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8237040985761189776144191 12355561478641784664216287)
      ·
        refine ⟨18533342217962676996324431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12355561478641784664216287 18533342217962676996324431)
        ·
          refine ⟨27800013326944015494486647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18533342217962676996324431 27800013326944015494486647)
          ·
            refine ⟨41700019990416023241729971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27800013326944015494486647 41700019990416023241729971)
            ·
              refine ⟨62550029985624034862594957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41700019990416023241729971 62550029985624034862594957)
              ·
                refine ⟨23456261244609013073473109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62550029985624034862594957 23456261244609013073473109)
                ·
                  refine ⟨274878061460261871954763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23456261244609013073473109 274878061460261871954763)
                  ·
                    rfl

theorem cell21_1204477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_1204477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204477 prefixEnd_1204477 := by exact prefixLift 1204477
  have htrace : WordTrace (prefixWord ++ tailWord_1204477) baseStart_1204477 baseEnd_1204477 := by
    simpa [prefixWord, tailWord_1204477, baseEnd_1204477] using wordTrace_append hprefix tailTrace_1204477
  have hstable : (prefixWord ++ tailWord_1204477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204477).length < 2 ^ (prefixWord ++ tailWord_1204477).sum := by decide
  have hdescent : baseEnd_1204477 < baseStart_1204477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204497 : List Nat := [1, 2, 2, 1, 1, 5, 4, 2, 3]
def baseStart_1204497 : Nat := 118140960795 + 1204497 * 2 ^ 59
def prefixEnd_1204497 : Nat := 4983230072969 + 3 ^ 40 * 1204497 * 2
def baseEnd_1204497 : Nat := 274882625732746281621389

theorem tailTrace_1204497 : CollatzResearch.WordTrace tailWord_1204497 prefixEnd_1204497 274882625732746281621389 := by
  unfold tailWord_1204497
  simp only [CollatzResearch.WordTrace]
  refine ⟨43931614717320555555163745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29287743144880370370109163 43931614717320555555163745)
  ·
    refine ⟨32948711037990416666372809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43931614717320555555163745 32948711037990416666372809)
    ·
      refine ⟨24711533278492812499779607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32948711037990416666372809 24711533278492812499779607)
      ·
        refine ⟨37067299917739218749669411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24711533278492812499779607 37067299917739218749669411)
        ·
          refine ⟨55600949876608828124504117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37067299917739218749669411 55600949876608828124504117)
          ·
            refine ⟨5212589050932077636672261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55600949876608828124504117 5212589050932077636672261)
            ·
              refine ⟨977360447049764556876049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5212589050932077636672261 977360447049764556876049)
              ·
                refine ⟨733020335287323417657037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 977360447049764556876049 733020335287323417657037)
                ·
                  refine ⟨274882625732746281621389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733020335287323417657037 274882625732746281621389)
                  ·
                    rfl

theorem cell21_1204497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 2, 3].length) (baseStart_1204497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204497 prefixEnd_1204497 := by exact prefixLift 1204497
  have htrace : WordTrace (prefixWord ++ tailWord_1204497) baseStart_1204497 baseEnd_1204497 := by
    simpa [prefixWord, tailWord_1204497, baseEnd_1204497] using wordTrace_append hprefix tailTrace_1204497
  have hstable : (prefixWord ++ tailWord_1204497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204497).length < 2 ^ (prefixWord ++ tailWord_1204497).sum := by decide
  have hdescent : baseEnd_1204497 < baseStart_1204497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204545 : List Nat := [1, 2, 5, 2, 3, 1, 1, 2, 4]
def baseStart_1204545 : Nat := 118140960795 + 1204545 * 2 ^ 59
def prefixEnd_1204545 : Nat := 4983230072969 + 3 ^ 40 * 1204545 * 2
def baseEnd_1204545 : Nat := 274893579986708864821291

theorem tailTrace_1204545 : CollatzResearch.WordTrace tailWord_1204545 prefixEnd_1204545 274893579986708864821291 := by
  unfold tailWord_1204545
  simp only [CollatzResearch.WordTrace]
  refine ⟨43933365421146659752911089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29288910280764439835274059 43933365421146659752911089)
  ·
    refine ⟨32950024065859994814683317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43933365421146659752911089 32950024065859994814683317)
    ·
      refine ⟨3089064756174374513876561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32950024065859994814683317 3089064756174374513876561)
      ·
        refine ⟨2316798567130780885407421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3089064756174374513876561 2316798567130780885407421)
        ·
          refine ⟨868799462674042832027783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2316798567130780885407421 868799462674042832027783)
          ·
            refine ⟨1303199194011064248041675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868799462674042832027783 1303199194011064248041675)
            ·
              refine ⟨1954798791016596372062513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303199194011064248041675 1954798791016596372062513)
              ·
                refine ⟨1466099093262447279046885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1954798791016596372062513 1466099093262447279046885)
                ·
                  refine ⟨274893579986708864821291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1466099093262447279046885 274893579986708864821291)
                  ·
                    rfl

theorem cell21_1204545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 2, 4].length) (baseStart_1204545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204545 prefixEnd_1204545 := by exact prefixLift 1204545
  have htrace : WordTrace (prefixWord ++ tailWord_1204545) baseStart_1204545 baseEnd_1204545 := by
    simpa [prefixWord, tailWord_1204545, baseEnd_1204545] using wordTrace_append hprefix tailTrace_1204545
  have hstable : (prefixWord ++ tailWord_1204545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204545).length < 2 ^ (prefixWord ++ tailWord_1204545).sum := by decide
  have hdescent : baseEnd_1204545 < baseStart_1204545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204556 : List Nat := [2, 2, 1, 3, 2, 1, 1, 6, 3]
def baseStart_1204556 : Nat := 118140960795 + 1204556 * 2 ^ 59
def prefixEnd_1204556 : Nat := 4983230072969 + 3 ^ 40 * 1204556 * 2
def baseEnd_1204556 : Nat := 274896090336575290137935

theorem tailTrace_1204556 : CollatzResearch.WordTrace tailWord_1204556 prefixEnd_1204556 274896090336575290137935 := by
  unfold tailWord_1204556
  simp only [CollatzResearch.WordTrace]
  refine ⟨21966883312053404315780761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29289177749404539087707681 21966883312053404315780761)
  ·
    refine ⟨16475162484040053236835571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21966883312053404315780761 16475162484040053236835571)
    ·
      refine ⟨24712743726060079855253357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16475162484040053236835571 24712743726060079855253357)
      ·
        refine ⟨9267278897272529945720009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24712743726060079855253357 9267278897272529945720009)
        ·
          refine ⟨6950459172954397459290007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9267278897272529945720009 6950459172954397459290007)
          ·
            refine ⟨10425688759431596188935011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6950459172954397459290007 10425688759431596188935011)
            ·
              refine ⟨15638533139147394283402517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10425688759431596188935011 15638533139147394283402517)
              ·
                refine ⟨733056240897534107034493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15638533139147394283402517 733056240897534107034493)
                ·
                  refine ⟨274896090336575290137935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733056240897534107034493 274896090336575290137935)
                  ·
                    rfl

theorem cell21_1204556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 6, 3].length) (baseStart_1204556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204556 prefixEnd_1204556 := by exact prefixLift 1204556
  have htrace : WordTrace (prefixWord ++ tailWord_1204556) baseStart_1204556 baseEnd_1204556 := by
    simpa [prefixWord, tailWord_1204556, baseEnd_1204556] using wordTrace_append hprefix tailTrace_1204556
  have hstable : (prefixWord ++ tailWord_1204556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204556).length < 2 ^ (prefixWord ++ tailWord_1204556).sum := by decide
  have hdescent : baseEnd_1204556 < baseStart_1204556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204618 : List Nat := [3, 1, 2, 5, 1, 1, 2, 6]
def baseStart_1204618 : Nat := 118140960795 + 1204618 * 2 ^ 59
def prefixEnd_1204618 : Nat := 4983230072969 + 3 ^ 40 * 1204618 * 2
def baseEnd_1204618 : Nat := 91636746527092320034825

theorem tailTrace_1204618 : CollatzResearch.WordTrace tailWord_1204618 prefixEnd_1204618 91636746527092320034825 := by
  unfold tailWord_1204618
  simp only [CollatzResearch.WordTrace]
  refine ⟨10984006987470548305079627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29290685299921462146879005 10984006987470548305079627)
  ·
    refine ⟨16476010481205822457619441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10984006987470548305079627 16476010481205822457619441)
    ·
      refine ⟨12357007860904366843214581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16476010481205822457619441 12357007860904366843214581)
      ·
        refine ⟨1158469486959784391551367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12357007860904366843214581 1158469486959784391551367)
        ·
          refine ⟨1737704230439676587327051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158469486959784391551367 1737704230439676587327051)
          ·
            refine ⟨2606556345659514880990577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1737704230439676587327051 2606556345659514880990577)
            ·
              refine ⟨1954917259244636160742933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2606556345659514880990577 1954917259244636160742933)
              ·
                refine ⟨91636746527092320034825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1954917259244636160742933 91636746527092320034825)
                ·
                  rfl

theorem cell21_1204618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 6].length) (baseStart_1204618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204618 prefixEnd_1204618 := by exact prefixLift 1204618
  have htrace : WordTrace (prefixWord ++ tailWord_1204618) baseStart_1204618 baseEnd_1204618 := by
    simpa [prefixWord, tailWord_1204618, baseEnd_1204618] using wordTrace_append hprefix tailTrace_1204618
  have hstable : (prefixWord ++ tailWord_1204618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204618).length < 2 ^ (prefixWord ++ tailWord_1204618).sum := by decide
  have hdescent : baseEnd_1204618 < baseStart_1204618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204694 : List Nat := [5, 2, 1, 1, 1, 1, 5, 5]
def baseStart_1204694 : Nat := 118140960795 + 1204694 * 2 ^ 59
def prefixEnd_1204694 : Nat := 4983230072969 + 3 ^ 40 * 1204694 * 2
def baseEnd_1204694 : Nat := 91642527938905905612551

theorem tailTrace_1204694 : CollatzResearch.WordTrace tailWord_1204694 prefixEnd_1204694 91642527938905905612551 := by
  unfold tailWord_1204694
  simp only [CollatzResearch.WordTrace]
  refine ⟨2746174993600428637505321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29292533265071238800056757 2746174993600428637505321)
  ·
    refine ⟨2059631245200321478128991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2746174993600428637505321 2059631245200321478128991)
    ·
      refine ⟨3089446867800482217193487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2059631245200321478128991 3089446867800482217193487)
      ·
        refine ⟨4634170301700723325790231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3089446867800482217193487 4634170301700723325790231)
        ·
          refine ⟨6951255452551084988685347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4634170301700723325790231 6951255452551084988685347)
          ·
            refine ⟨10426883178826627483028021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6951255452551084988685347 10426883178826627483028021)
            ·
              refine ⟨977520298014996326533877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10426883178826627483028021 977520298014996326533877)
              ·
                refine ⟨91642527938905905612551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 977520298014996326533877 91642527938905905612551)
                ·
                  rfl

theorem cell21_1204694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_1204694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204694 prefixEnd_1204694 := by exact prefixLift 1204694
  have htrace : WordTrace (prefixWord ++ tailWord_1204694) baseStart_1204694 baseEnd_1204694 := by
    simpa [prefixWord, tailWord_1204694, baseEnd_1204694] using wordTrace_append hprefix tailTrace_1204694
  have hstable : (prefixWord ++ tailWord_1204694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204694).length < 2 ^ (prefixWord ++ tailWord_1204694).sum := by decide
  have hdescent : baseEnd_1204694 < baseStart_1204694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204705 : List Nat := [1, 2, 3, 1, 2, 2, 2, 2, 6]
def baseStart_1204705 : Nat := 118140960795 + 1204705 * 2 ^ 59
def prefixEnd_1204705 : Nat := 4983230072969 + 3 ^ 40 * 1204705 * 2
def baseEnd_1204705 : Nat := 274930094166584142154297

theorem tailTrace_1204705 : CollatzResearch.WordTrace tailWord_1204705 prefixEnd_1204705 274930094166584142154297 := by
  unfold tailWord_1204705
  simp only [CollatzResearch.WordTrace]
  refine ⟨43939201100567007078735569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29292800733711338052490379 43939201100567007078735569)
  ·
    refine ⟨32954400825425255309051677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43939201100567007078735569 32954400825425255309051677)
    ·
      refine ⟨12357900309534470740894379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32954400825425255309051677 12357900309534470740894379)
      ·
        refine ⟨18536850464301706111341569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12357900309534470740894379 18536850464301706111341569)
        ·
          refine ⟨13902637848226279583506177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18536850464301706111341569 13902637848226279583506177)
          ·
            refine ⟨10426978386169709687629633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13902637848226279583506177 10426978386169709687629633)
            ·
              refine ⟨7820233789627282265722225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10426978386169709687629633 7820233789627282265722225)
              ·
                refine ⟨5865175342220461699291669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7820233789627282265722225 5865175342220461699291669)
                ·
                  refine ⟨274930094166584142154297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5865175342220461699291669 274930094166584142154297)
                  ·
                    rfl

theorem cell21_1204705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 2, 6].length) (baseStart_1204705 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204705 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204705 prefixEnd_1204705 := by exact prefixLift 1204705
  have htrace : WordTrace (prefixWord ++ tailWord_1204705) baseStart_1204705 baseEnd_1204705 := by
    simpa [prefixWord, tailWord_1204705, baseEnd_1204705] using wordTrace_append hprefix tailTrace_1204705
  have hstable : (prefixWord ++ tailWord_1204705).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204705).length < 2 ^ (prefixWord ++ tailWord_1204705).sum := by decide
  have hdescent : baseEnd_1204705 < baseStart_1204705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204725 : List Nat := [1, 3, 5, 1, 2, 1, 2, 1, 5]
def baseStart_1204725 : Nat := 118140960795 + 1204725 * 2 ^ 59
def prefixEnd_1204725 : Nat := 4983230072969 + 3 ^ 40 * 1204725 * 2
def baseEnd_1204725 : Nat := 274934658439068551820923

theorem tailTrace_1204725 : CollatzResearch.WordTrace tailWord_1204725 prefixEnd_1204725 274934658439068551820923 := by
  unfold tailWord_1204725
  simp only [CollatzResearch.WordTrace]
  refine ⟨43939930560494550494463629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29293287040329700329642419 43939930560494550494463629)
  ·
    refine ⟨16477473960185456435423861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43939930560494550494463629 16477473960185456435423861)
    ·
      refine ⟨1544763183767386540820987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16477473960185456435423861 1544763183767386540820987)
      ·
        refine ⟨2317144775651079811231481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544763183767386540820987 2317144775651079811231481)
        ·
          refine ⟨1737858581738309858423611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2317144775651079811231481 1737858581738309858423611)
          ·
            refine ⟨2606787872607464787635417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1737858581738309858423611 2606787872607464787635417)
            ·
              refine ⟨1955090904455598590726563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2606787872607464787635417 1955090904455598590726563)
              ·
                refine ⟨2932636356683397886089845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1955090904455598590726563 2932636356683397886089845)
                ·
                  refine ⟨274934658439068551820923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2932636356683397886089845 274934658439068551820923)
                  ·
                    rfl

theorem cell21_1204725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_1204725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204725 prefixEnd_1204725 := by exact prefixLift 1204725
  have htrace : WordTrace (prefixWord ++ tailWord_1204725) baseStart_1204725 baseEnd_1204725 := by
    simpa [prefixWord, tailWord_1204725, baseEnd_1204725] using wordTrace_append hprefix tailTrace_1204725
  have hstable : (prefixWord ++ tailWord_1204725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204725).length < 2 ^ (prefixWord ++ tailWord_1204725).sum := by decide
  have hdescent : baseEnd_1204725 < baseStart_1204725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204742 : List Nat := [6, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1204742 : Nat := 118140960795 + 1204742 * 2 ^ 59
def prefixEnd_1204742 : Nat := 4983230072969 + 3 ^ 40 * 1204742 * 2
def baseEnd_1204742 : Nat := 274938538070680300037555

theorem tailTrace_1204742 : CollatzResearch.WordTrace tailWord_1204742 prefixEnd_1204742 274938538070680300037555 := by
  unfold tailWord_1204742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1373142206294780074932265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29293700400955308265221653 1373142206294780074932265)
  ·
    refine ⟨1029856654721085056199199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1373142206294780074932265 1029856654721085056199199)
    ·
      refine ⟨1544784982081627584298799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1029856654721085056199199 1544784982081627584298799)
      ·
        refine ⟨2317177473122441376448199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1544784982081627584298799 2317177473122441376448199)
        ·
          refine ⟨3475766209683662064672299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2317177473122441376448199 3475766209683662064672299)
          ·
            refine ⟨5213649314525493097008449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3475766209683662064672299 5213649314525493097008449)
            ·
              refine ⟨3910236985894119822756337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5213649314525493097008449 3910236985894119822756337)
              ·
                refine ⟨2932677739420589867067253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3910236985894119822756337 2932677739420589867067253)
                ·
                  refine ⟨274938538070680300037555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2932677739420589867067253 274938538070680300037555)
                  ·
                    rfl

theorem cell21_1204742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1204742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204742 prefixEnd_1204742 := by exact prefixLift 1204742
  have htrace : WordTrace (prefixWord ++ tailWord_1204742) baseStart_1204742 baseEnd_1204742 := by
    simpa [prefixWord, tailWord_1204742, baseEnd_1204742] using wordTrace_append hprefix tailTrace_1204742
  have hstable : (prefixWord ++ tailWord_1204742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204742).length < 2 ^ (prefixWord ++ tailWord_1204742).sum := by decide
  have hdescent : baseEnd_1204742 < baseStart_1204742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204759 : List Nat := [1, 1, 3, 6, 2, 1, 1, 3, 3]
def baseStart_1204759 : Nat := 118140960795 + 1204759 * 2 ^ 59
def prefixEnd_1204759 : Nat := 4983230072969 + 3 ^ 40 * 1204759 * 2
def baseEnd_1204759 : Nat := 274942417702292048254187

theorem tailTrace_1204759 : CollatzResearch.WordTrace tailWord_1204759 prefixEnd_1204759 274942417702292048254187 := by
  unfold tailWord_1204759
  simp only [CollatzResearch.WordTrace]
  refine ⟨43941170642371374301201331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29294113761580916200800887 43941170642371374301201331)
  ·
    refine ⟨65911755963557061451801997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43941170642371374301201331 65911755963557061451801997)
    ·
      refine ⟨24716908486333898044425749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65911755963557061451801997 24716908486333898044425749)
      ·
        refine ⟨1158605085296901470832457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 24716908486333898044425749 1158605085296901470832457)
        ·
          refine ⟨868953813972676103124343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1158605085296901470832457 868953813972676103124343)
          ·
            refine ⟨1303430720959014154686515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 868953813972676103124343 1303430720959014154686515)
            ·
              refine ⟨1955146081438521232029773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303430720959014154686515 1955146081438521232029773)
              ·
                refine ⟨733179780539445462011165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1955146081438521232029773 733179780539445462011165)
                ·
                  refine ⟨274942417702292048254187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733179780539445462011165 274942417702292048254187)
                  ·
                    rfl

theorem cell21_1204759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 3, 3].length) (baseStart_1204759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204759 prefixEnd_1204759 := by exact prefixLift 1204759
  have htrace : WordTrace (prefixWord ++ tailWord_1204759) baseStart_1204759 baseEnd_1204759 := by
    simpa [prefixWord, tailWord_1204759, baseEnd_1204759] using wordTrace_append hprefix tailTrace_1204759
  have hstable : (prefixWord ++ tailWord_1204759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204759).length < 2 ^ (prefixWord ++ tailWord_1204759).sum := by decide
  have hdescent : baseEnd_1204759 < baseStart_1204759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204936 : List Nat := [2, 1, 3, 1, 2, 3, 3, 3, 3]
def baseStart_1204936 : Nat := 118140960795 + 1204936 * 2 ^ 59
def prefixEnd_1204936 : Nat := 4983230072969 + 3 ^ 40 * 1204936 * 2
def baseEnd_1204936 : Nat := 274982811513779073803825

theorem tailTrace_1204936 : CollatzResearch.WordTrace tailWord_1204936 prefixEnd_1204936 274982811513779073803825 := by
  unfold tailWord_1204936
  simp only [CollatzResearch.WordTrace]
  refine ⟨21973813181365066765197331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29298417575153422353596441 21973813181365066765197331)
  ·
    refine ⟨32960719772047600147795997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21973813181365066765197331 32960719772047600147795997)
    ·
      refine ⟨12360269914517850055423499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32960719772047600147795997 12360269914517850055423499)
      ·
        refine ⟨18540404871776775083135249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12360269914517850055423499 18540404871776775083135249)
        ·
          refine ⟨13905303653832581312351437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18540404871776775083135249 13905303653832581312351437)
          ·
            refine ⟨5214488870187217992131789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13905303653832581312351437 5214488870187217992131789)
            ·
              refine ⟨1955433326320206747049421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5214488870187217992131789 1955433326320206747049421)
              ·
                refine ⟨733287497370077530143533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1955433326320206747049421 733287497370077530143533)
                ·
                  refine ⟨274982811513779073803825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733287497370077530143533 274982811513779073803825)
                  ·
                    rfl

theorem cell21_1204936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 3, 3].length) (baseStart_1204936 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204936 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204936 prefixEnd_1204936 := by exact prefixLift 1204936
  have htrace : WordTrace (prefixWord ++ tailWord_1204936) baseStart_1204936 baseEnd_1204936 := by
    simpa [prefixWord, tailWord_1204936, baseEnd_1204936] using wordTrace_append hprefix tailTrace_1204936
  have hstable : (prefixWord ++ tailWord_1204936).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204936).length < 2 ^ (prefixWord ++ tailWord_1204936).sum := by decide
  have hdescent : baseEnd_1204936 < baseStart_1204936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204964 : List Nat := [2, 3, 1, 1, 1, 5, 2, 6]
def baseStart_1204964 : Nat := 118140960795 + 1204964 * 2 ^ 59
def prefixEnd_1204964 : Nat := 4983230072969 + 3 ^ 40 * 1204964 * 2
def baseEnd_1204964 : Nat := 91663067165085749112367

theorem tailTrace_1204964 : CollatzResearch.WordTrace tailWord_1204964 prefixEnd_1204964 91663067165085749112367 := by
  unfold tailWord_1204964
  simp only [CollatzResearch.WordTrace]
  refine ⟨21974323803314347156206973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29299098404419129541609297 21974323803314347156206973)
  ·
    refine ⟨8240371426242880183577615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21974323803314347156206973 8240371426242880183577615)
    ·
      refine ⟨12360557139364320275366423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8240371426242880183577615 12360557139364320275366423)
      ·
        refine ⟨18540835709046480413049635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12360557139364320275366423 18540835709046480413049635)
        ·
          refine ⟨27811253563569720619574453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18540835709046480413049635 27811253563569720619574453)
          ·
            refine ⟨2607305021584661308085105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27811253563569720619574453 2607305021584661308085105)
            ·
              refine ⟨1955478766188495981063829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2607305021584661308085105 1955478766188495981063829)
              ·
                refine ⟨91663067165085749112367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1955478766188495981063829 91663067165085749112367)
                ·
                  rfl

theorem cell21_1204964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 6].length) (baseStart_1204964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204964 prefixEnd_1204964 := by exact prefixLift 1204964
  have htrace : WordTrace (prefixWord ++ tailWord_1204964) baseStart_1204964 baseEnd_1204964 := by
    simpa [prefixWord, tailWord_1204964, baseEnd_1204964] using wordTrace_append hprefix tailTrace_1204964
  have hstable : (prefixWord ++ tailWord_1204964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204964).length < 2 ^ (prefixWord ++ tailWord_1204964).sum := by decide
  have hdescent : baseEnd_1204964 < baseStart_1204964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204995 : List Nat := [1, 1, 1, 3, 2, 2, 1, 7, 3]
def baseStart_1204995 : Nat := 118140960795 + 1204995 * 2 ^ 59
def prefixEnd_1204995 : Nat := 4983230072969 + 3 ^ 40 * 1204995 * 2
def baseEnd_1204995 : Nat := 274996276117608082320371

theorem tailTrace_1204995 : CollatzResearch.WordTrace tailWord_1204995 prefixEnd_1204995 274996276117608082320371 := by
  unfold tailWord_1204995
  simp only [CollatzResearch.WordTrace]
  refine ⟨43949778269516386606792439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29299852179677591071194959 43949778269516386606792439)
  ·
    refine ⟨65924667404274579910188659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43949778269516386606792439 65924667404274579910188659)
    ·
      refine ⟨98887001106411869865282989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65924667404274579910188659 98887001106411869865282989)
      ·
        refine ⟨37082625414904451199481121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98887001106411869865282989 37082625414904451199481121)
        ·
          refine ⟨27811969061178338399610841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37082625414904451199481121 27811969061178338399610841)
          ·
            refine ⟨20858976795883753799708131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27811969061178338399610841 20858976795883753799708131)
            ·
              refine ⟨31288465193825630699562197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20858976795883753799708131 31288465193825630699562197)
              ·
                refine ⟨733323402980288219520989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 31288465193825630699562197 733323402980288219520989)
                ·
                  refine ⟨274996276117608082320371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733323402980288219520989 274996276117608082320371)
                  ·
                    rfl

theorem cell21_1204995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7, 3].length) (baseStart_1204995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204995 prefixEnd_1204995 := by exact prefixLift 1204995
  have htrace : WordTrace (prefixWord ++ tailWord_1204995) baseStart_1204995 baseEnd_1204995 := by
    simpa [prefixWord, tailWord_1204995, baseEnd_1204995] using wordTrace_append hprefix tailTrace_1204995
  have hstable : (prefixWord ++ tailWord_1204995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204995).length < 2 ^ (prefixWord ++ tailWord_1204995).sum := by decide
  have hdescent : baseEnd_1204995 < baseStart_1204995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1204998 : List Nat := [6, 2, 2, 11]
def baseStart_1204998 : Nat := 118140960795 + 1204998 * 2 ^ 59
def prefixEnd_1204998 : Nat := 4983230072969 + 3 ^ 40 * 1204998 * 2
def baseEnd_1204998 : Nat := 1131674735631607999055

theorem tailTrace_1204998 : CollatzResearch.WordTrace tailWord_1204998 prefixEnd_1204998 1131674735631607999055 := by
  unfold tailWord_1204998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1373433990265797441223489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29299925125670345412767765 1373433990265797441223489)
  ·
    refine ⟨1030075492699348080917617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1373433990265797441223489 1030075492699348080917617)
    ·
      refine ⟨772556619524511060688213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1030075492699348080917617 772556619524511060688213)
      ·
        refine ⟨1131674735631607999055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 772556619524511060688213 1131674735631607999055)
        ·
          rfl

theorem cell21_1204998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 11].length) (baseStart_1204998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1204998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1204998 prefixEnd_1204998 := by exact prefixLift 1204998
  have htrace : WordTrace (prefixWord ++ tailWord_1204998) baseStart_1204998 baseEnd_1204998 := by
    simpa [prefixWord, tailWord_1204998, baseEnd_1204998] using wordTrace_append hprefix tailTrace_1204998
  have hstable : (prefixWord ++ tailWord_1204998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1204998).length < 2 ^ (prefixWord ++ tailWord_1204998).sum := by decide
  have hdescent : baseEnd_1204998 < baseStart_1204998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1204998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205009 : List Nat := [1, 2, 2, 1, 1, 3, 3, 4, 4]
def baseStart_1205009 : Nat := 118140960795 + 1205009 * 2 ^ 59
def prefixEnd_1205009 : Nat := 4983230072969 + 3 ^ 40 * 1205009 * 2
def baseEnd_1205009 : Nat := 274999471108347169087009

theorem tailTrace_1205009 : CollatzResearch.WordTrace tailWord_1205009 prefixEnd_1205009 274999471108347169087009 := by
  unfold tailWord_1205009
  simp only [CollatzResearch.WordTrace]
  refine ⟨43950288891465666997802081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29300192594310444665201387 43950288891465666997802081)
  ·
    refine ⟨32962716668599250248351561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43950288891465666997802081 32962716668599250248351561)
    ·
      refine ⟨24722037501449437686263671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32962716668599250248351561 24722037501449437686263671)
      ·
        refine ⟨37083056252174156529395507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24722037501449437686263671 37083056252174156529395507)
        ·
          refine ⟨55624584378261234794093261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37083056252174156529395507 55624584378261234794093261)
          ·
            refine ⟨20859219141847963047784973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55624584378261234794093261 20859219141847963047784973)
            ·
              refine ⟨7822207178192986142919365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20859219141847963047784973 7822207178192986142919365)
              ·
                refine ⟨1466663845911184901797381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7822207178192986142919365 1466663845911184901797381)
                ·
                  refine ⟨274999471108347169087009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1466663845911184901797381 274999471108347169087009)
                  ·
                    rfl

theorem cell21_1205009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_1205009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205009 prefixEnd_1205009 := by exact prefixLift 1205009
  have htrace : WordTrace (prefixWord ++ tailWord_1205009) baseStart_1205009 baseEnd_1205009 := by
    simpa [prefixWord, tailWord_1205009, baseEnd_1205009] using wordTrace_append hprefix tailTrace_1205009
  have hstable : (prefixWord ++ tailWord_1205009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205009).length < 2 ^ (prefixWord ++ tailWord_1205009).sum := by decide
  have hdescent : baseEnd_1205009 < baseStart_1205009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205026 : List Nat := [3, 3, 1, 1, 2, 2, 2, 3, 4]
def baseStart_1205026 : Nat := 118140960795 + 1205026 * 2 ^ 59
def prefixEnd_1205026 : Nat := 4983230072969 + 3 ^ 40 * 1205026 * 2
def baseEnd_1205026 : Nat := 275003350739958917303641

theorem tailTrace_1205026 : CollatzResearch.WordTrace tailWord_1205026 prefixEnd_1205026 275003350739958917303641 := by
  unfold tailWord_1205026
  simp only [CollatzResearch.WordTrace]
  refine ⟨10987727233101019725292733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29300605954936052600780621 10987727233101019725292733)
  ·
    refine ⟨4120397712412882396984775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10987727233101019725292733 4120397712412882396984775)
    ·
      refine ⟨6180596568619323595477163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4120397712412882396984775 6180596568619323595477163)
      ·
        refine ⟨9270894852928985393215745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6180596568619323595477163 9270894852928985393215745)
        ·
          refine ⟨6953171139696739044911809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9270894852928985393215745 6953171139696739044911809)
          ·
            refine ⟨5214878354772554283683857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6953171139696739044911809 5214878354772554283683857)
            ·
              refine ⟨3911158766079415712762893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5214878354772554283683857 3911158766079415712762893)
              ·
                refine ⟨1466684537279780892286085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3911158766079415712762893 1466684537279780892286085)
                ·
                  refine ⟨275003350739958917303641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1466684537279780892286085 275003350739958917303641)
                  ·
                    rfl

theorem cell21_1205026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_1205026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205026 prefixEnd_1205026 := by exact prefixLift 1205026
  have htrace : WordTrace (prefixWord ++ tailWord_1205026) baseStart_1205026 baseEnd_1205026 := by
    simpa [prefixWord, tailWord_1205026, baseEnd_1205026] using wordTrace_append hprefix tailTrace_1205026
  have hstable : (prefixWord ++ tailWord_1205026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205026).length < 2 ^ (prefixWord ++ tailWord_1205026).sum := by decide
  have hdescent : baseEnd_1205026 < baseStart_1205026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205046 : List Nat := [5, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_1205046 : Nat := 118140960795 + 1205046 * 2 ^ 59
def prefixEnd_1205046 : Nat := 4983230072969 + 3 ^ 40 * 1205046 * 2
def baseEnd_1205046 : Nat := 275007915012443326970267

theorem tailTrace_1205046 : CollatzResearch.WordTrace tailWord_1205046 prefixEnd_1205046 275007915012443326970267 := by
  unfold tailWord_1205046
  simp only [CollatzResearch.WordTrace]
  refine ⟨2746977399520726394806187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29301092261554414877932661 2746977399520726394806187)
  ·
    refine ⟨4120466099281089592209281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2746977399520726394806187 4120466099281089592209281)
    ·
      refine ⟨3090349574460817194156961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4120466099281089592209281 3090349574460817194156961)
      ·
        refine ⟨2317762180845612895617721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3090349574460817194156961 2317762180845612895617721)
        ·
          refine ⟨1738321635634209671713291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2317762180845612895617721 1738321635634209671713291)
          ·
            refine ⟨2607482453451314507569937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1738321635634209671713291 2607482453451314507569937)
            ·
              refine ⟨1955611840088485880677453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2607482453451314507569937 1955611840088485880677453)
              ·
                refine ⟨733354440033182205254045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1955611840088485880677453 733354440033182205254045)
                ·
                  refine ⟨275007915012443326970267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733354440033182205254045 275007915012443326970267)
                  ·
                    rfl

theorem cell21_1205046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_1205046 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205046 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205046 prefixEnd_1205046 := by exact prefixLift 1205046
  have htrace : WordTrace (prefixWord ++ tailWord_1205046) baseStart_1205046 baseEnd_1205046 := by
    simpa [prefixWord, tailWord_1205046, baseEnd_1205046] using wordTrace_append hprefix tailTrace_1205046
  have hstable : (prefixWord ++ tailWord_1205046).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205046).length < 2 ^ (prefixWord ++ tailWord_1205046).sum := by decide
  have hdescent : baseEnd_1205046 < baseStart_1205046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205057 : List Nat := [1, 2, 5, 3, 1, 1, 8]
def baseStart_1205057 : Nat := 118140960795 + 1205057 * 2 ^ 59
def prefixEnd_1205057 : Nat := 4983230072969 + 3 ^ 40 * 1205057 * 2
def baseEnd_1205057 : Nat := 30556713929145528031879

theorem tailTrace_1205057 : CollatzResearch.WordTrace tailWord_1205057 prefixEnd_1205057 30556713929145528031879 := by
  unfold tailWord_1205057
  simp only [CollatzResearch.WordTrace]
  refine ⟨43952039595291771195549425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29301359730194514130366283 43952039595291771195549425)
  ·
    refine ⟨32964029696468828396662069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43952039595291771195549425 32964029696468828396662069)
    ·
      refine ⟨3090377784043952662187069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32964029696468828396662069 3090377784043952662187069)
      ·
        refine ⟨1158891669016482248320151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3090377784043952662187069 1158891669016482248320151)
        ·
          refine ⟨1738337503524723372480227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158891669016482248320151 1738337503524723372480227)
          ·
            refine ⟨2607506255287085058720341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1738337503524723372480227 2607506255287085058720341)
            ·
              refine ⟨30556713929145528031879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2607506255287085058720341 30556713929145528031879)
              ·
                rfl

theorem cell21_1205057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 8].length) (baseStart_1205057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205057 prefixEnd_1205057 := by exact prefixLift 1205057
  have htrace : WordTrace (prefixWord ++ tailWord_1205057) baseStart_1205057 baseEnd_1205057 := by
    simpa [prefixWord, tailWord_1205057, baseEnd_1205057] using wordTrace_append hprefix tailTrace_1205057
  have hstable : (prefixWord ++ tailWord_1205057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205057).length < 2 ^ (prefixWord ++ tailWord_1205057).sum := by decide
  have hdescent : baseEnd_1205057 < baseStart_1205057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205122 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 5]
def baseStart_1205122 : Nat := 118140960795 + 1205122 * 2 ^ 59
def prefixEnd_1205122 : Nat := 4983230072969 + 3 ^ 40 * 1205122 * 2
def baseEnd_1205122 : Nat := 275025259247884083703445

theorem tailTrace_1205122 : CollatzResearch.WordTrace tailWord_1205122 prefixEnd_1205122 275025259247884083703445 := by
  unfold tailWord_1205122
  simp only [CollatzResearch.WordTrace]
  refine ⟨10988602585014071824166405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29302940226704191531110413 10988602585014071824166405)
  ·
    refine ⟨2060362984690138467031201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10988602585014071824166405 2060362984690138467031201)
    ·
      refine ⟨1545272238517603850273401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2060362984690138467031201 1545272238517603850273401)
      ·
        refine ⟨1158954178888202887705051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1545272238517603850273401 1158954178888202887705051)
        ·
          refine ⟨1738431268332304331557577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1158954178888202887705051 1738431268332304331557577)
          ·
            refine ⟨1303823451249228248668183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1738431268332304331557577 1303823451249228248668183)
            ·
              refine ⟨1955735176873842373002275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1303823451249228248668183 1955735176873842373002275)
              ·
                refine ⟨2933602765310763559503413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1955735176873842373002275 2933602765310763559503413)
                ·
                  refine ⟨275025259247884083703445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2933602765310763559503413 275025259247884083703445)
                  ·
                    rfl

theorem cell21_1205122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_1205122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205122 prefixEnd_1205122 := by exact prefixLift 1205122
  have htrace : WordTrace (prefixWord ++ tailWord_1205122) baseStart_1205122 baseEnd_1205122 := by
    simpa [prefixWord, tailWord_1205122, baseEnd_1205122] using wordTrace_append hprefix tailTrace_1205122
  have hstable : (prefixWord ++ tailWord_1205122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205122).length < 2 ^ (prefixWord ++ tailWord_1205122).sum := by decide
  have hdescent : baseEnd_1205122 < baseStart_1205122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205296 : List Nat := [2, 1, 1, 1, 2, 4, 1, 3, 6]
def baseStart_1205296 : Nat := 118140960795 + 1205296 * 2 ^ 59
def prefixEnd_1205296 : Nat := 4983230072969 + 3 ^ 40 * 1205296 * 2
def baseEnd_1205296 : Nat := 275064968418498447803089

theorem tailTrace_1205296 : CollatzResearch.WordTrace tailWord_1205296 prefixEnd_1205296 275064968418498447803089 := by
  unfold tailWord_1205296
  simp only [CollatzResearch.WordTrace]
  refine ⟨21980378320712957506749871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29307171094283943342333161 21980378320712957506749871)
  ·
    refine ⟨32970567481069436260124807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21980378320712957506749871 32970567481069436260124807)
    ·
      refine ⟨49455851221604154390187211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32970567481069436260124807 49455851221604154390187211)
      ·
        refine ⟨74183776832406231585280817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49455851221604154390187211 74183776832406231585280817)
        ·
          refine ⟨55637832624304673688960613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74183776832406231585280817 55637832624304673688960613)
          ·
            refine ⟨10432093617057126316680115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55637832624304673688960613 10432093617057126316680115)
            ·
              refine ⟨15648140425585689475020173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10432093617057126316680115 15648140425585689475020173)
              ·
                refine ⟨5868052659594633553132565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15648140425585689475020173 5868052659594633553132565)
                ·
                  refine ⟨275064968418498447803089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5868052659594633553132565 275064968418498447803089)
                  ·
                    rfl

theorem cell21_1205296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_1205296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205296 prefixEnd_1205296 := by exact prefixLift 1205296
  have htrace : WordTrace (prefixWord ++ tailWord_1205296) baseStart_1205296 baseEnd_1205296 := by
    simpa [prefixWord, tailWord_1205296, baseEnd_1205296] using wordTrace_append hprefix tailTrace_1205296
  have hstable : (prefixWord ++ tailWord_1205296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205296).length < 2 ^ (prefixWord ++ tailWord_1205296).sum := by decide
  have hdescent : baseEnd_1205296 < baseStart_1205296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205406 : List Nat := [4, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1205406 : Nat := 118140960795 + 1205406 * 2 ^ 59
def prefixEnd_1205406 : Nat := 4983230072969 + 3 ^ 40 * 1205406 * 2
def baseEnd_1205406 : Nat := 275090071917162700969531

theorem tailTrace_1205406 : CollatzResearch.WordTrace tailWord_1205406 prefixEnd_1205406 275090071917162700969531 := by
  unfold tailWord_1205406
  simp only [CollatzResearch.WordTrace]
  refine ⟨5495596083878425475000509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29309845780684935866669381 5495596083878425475000509)
  ·
    refine ⟨2060848531454409553125191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5495596083878425475000509 2060848531454409553125191)
    ·
      refine ⟨3091272797181614329687787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2060848531454409553125191 3091272797181614329687787)
      ·
        refine ⟨4636909195772421494531681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3091272797181614329687787 4636909195772421494531681)
        ·
          refine ⟨3477681896829316120898761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4636909195772421494531681 3477681896829316120898761)
          ·
            refine ⟨2608261422621987090674071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3477681896829316120898761 2608261422621987090674071)
            ·
              refine ⟨3912392133932980636011107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2608261422621987090674071 3912392133932980636011107)
              ·
                refine ⟨5868588200899470954016661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3912392133932980636011107 5868588200899470954016661)
                ·
                  refine ⟨275090071917162700969531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5868588200899470954016661 275090071917162700969531)
                  ·
                    rfl

theorem cell21_1205406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1205406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205406 prefixEnd_1205406 := by exact prefixLift 1205406
  have htrace : WordTrace (prefixWord ++ tailWord_1205406) baseStart_1205406 baseEnd_1205406 := by
    simpa [prefixWord, tailWord_1205406, baseEnd_1205406] using wordTrace_append hprefix tailTrace_1205406
  have hstable : (prefixWord ++ tailWord_1205406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205406).length < 2 ^ (prefixWord ++ tailWord_1205406).sum := by decide
  have hdescent : baseEnd_1205406 < baseStart_1205406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205448 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 6]
def baseStart_1205448 : Nat := 118140960795 + 1205448 * 2 ^ 59
def prefixEnd_1205448 : Nat := 4983230072969 + 3 ^ 40 * 1205448 * 2
def baseEnd_1205448 : Nat := 275099656889379961269445

theorem tailTrace_1205448 : CollatzResearch.WordTrace tailWord_1205448 prefixEnd_1205448 275099656889379961269445 := by
  unfold tailWord_1205448
  simp only [CollatzResearch.WordTrace]
  refine ⟨21983150268437622486516499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29310867024583496648688665 21983150268437622486516499)
  ·
    refine ⟨32974725402656433729774749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21983150268437622486516499 32974725402656433729774749)
    ·
      refine ⟨12365522025996162648665531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32974725402656433729774749 12365522025996162648665531)
      ·
        refine ⟨18548283038994243972998297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12365522025996162648665531 18548283038994243972998297)
        ·
          refine ⟨13911212279245682979748723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18548283038994243972998297 13911212279245682979748723)
          ·
            refine ⟨20866818418868524469623085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13911212279245682979748723 20866818418868524469623085)
            ·
              refine ⟨7825056907075696676108657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20866818418868524469623085 7825056907075696676108657)
              ·
                refine ⟨5868792680306772507081493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7825056907075696676108657 5868792680306772507081493)
                ·
                  refine ⟨275099656889379961269445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5868792680306772507081493 275099656889379961269445)
                  ·
                    rfl

theorem cell21_1205448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_1205448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205448 prefixEnd_1205448 := by exact prefixLift 1205448
  have htrace : WordTrace (prefixWord ++ tailWord_1205448) baseStart_1205448 baseEnd_1205448 := by
    simpa [prefixWord, tailWord_1205448, baseEnd_1205448] using wordTrace_append hprefix tailTrace_1205448
  have hstable : (prefixWord ++ tailWord_1205448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205448).length < 2 ^ (prefixWord ++ tailWord_1205448).sum := by decide
  have hdescent : baseEnd_1205448 < baseStart_1205448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205482 : List Nat := [3, 1, 3, 1, 1, 3, 4, 1, 4]
def baseStart_1205482 : Nat := 118140960795 + 1205482 * 2 ^ 59
def prefixEnd_1205482 : Nat := 4983230072969 + 3 ^ 40 * 1205482 * 2
def baseEnd_1205482 : Nat := 275107416152603457702709

theorem tailTrace_1205482 : CollatzResearch.WordTrace tailWord_1205482 prefixEnd_1205482 275107416152603457702709 := by
  unfold tailWord_1205482
  simp only [CollatzResearch.WordTrace]
  refine ⟨10991885154688017194942675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29311693745834712519847133 10991885154688017194942675)
  ·
    refine ⟨16487827732032025792414013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10991885154688017194942675 16487827732032025792414013)
    ·
      refine ⟨6182935399512009672155255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16487827732032025792414013 6182935399512009672155255)
      ·
        refine ⟨9274403099268014508232883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6182935399512009672155255 9274403099268014508232883)
        ·
          refine ⟨13911604648902021762349325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9274403099268014508232883 13911604648902021762349325)
          ·
            refine ⟨5216851743338258160880997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13911604648902021762349325 5216851743338258160880997)
            ·
              refine ⟨978159701875923405165187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5216851743338258160880997 978159701875923405165187)
              ·
                refine ⟨1467239552813885107747781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978159701875923405165187 1467239552813885107747781)
                ·
                  refine ⟨275107416152603457702709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1467239552813885107747781 275107416152603457702709)
                  ·
                    rfl

theorem cell21_1205482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_1205482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205482 prefixEnd_1205482 := by exact prefixLift 1205482
  have htrace : WordTrace (prefixWord ++ tailWord_1205482) baseStart_1205482 baseEnd_1205482 := by
    simpa [prefixWord, tailWord_1205482, baseEnd_1205482] using wordTrace_append hprefix tailTrace_1205482
  have hstable : (prefixWord ++ tailWord_1205482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205482).length < 2 ^ (prefixWord ++ tailWord_1205482).sum := by decide
  have hdescent : baseEnd_1205482 < baseStart_1205482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205527 : List Nat := [1, 1, 3, 4, 1, 1, 3, 4, 3]
def baseStart_1205527 : Nat := 118140960795 + 1205527 * 2 ^ 59
def prefixEnd_1205527 : Nat := 4983230072969 + 3 ^ 40 * 1205527 * 2
def baseEnd_1205527 : Nat := 275117685765693379452617

theorem tailTrace_1205527 : CollatzResearch.WordTrace tailWord_1205527 prefixEnd_1205527 275117685765693379452617 := by
  unfold tailWord_1205527
  simp only [CollatzResearch.WordTrace]
  refine ⟨43969181903589041465158835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29312787935726027643439223 43969181903589041465158835)
  ·
    refine ⟨65953772855383562197738253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43969181903589041465158835 65953772855383562197738253)
    ·
      refine ⟨24732664820768835824151845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65953772855383562197738253 24732664820768835824151845)
      ·
        refine ⟨4637374653894156717028471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24732664820768835824151845 4637374653894156717028471)
        ·
          refine ⟨6956061980841235075542707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4637374653894156717028471 6956061980841235075542707)
          ·
            refine ⟨10434092971261852613314061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6956061980841235075542707 10434092971261852613314061)
            ·
              refine ⟨3912784864223194729992773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10434092971261852613314061 3912784864223194729992773)
              ·
                refine ⟨733647162041849011873645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3912784864223194729992773 733647162041849011873645)
                ·
                  refine ⟨275117685765693379452617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733647162041849011873645 275117685765693379452617)
                  ·
                    rfl

theorem cell21_1205527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 4, 3].length) (baseStart_1205527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205527 prefixEnd_1205527 := by exact prefixLift 1205527
  have htrace : WordTrace (prefixWord ++ tailWord_1205527) baseStart_1205527 baseEnd_1205527 := by
    simpa [prefixWord, tailWord_1205527, baseEnd_1205527] using wordTrace_append hprefix tailTrace_1205527
  have hstable : (prefixWord ++ tailWord_1205527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205527).length < 2 ^ (prefixWord ++ tailWord_1205527).sum := by decide
  have hdescent : baseEnd_1205527 < baseStart_1205527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205541 : List Nat := [1, 3, 1, 2, 4, 1, 2, 3, 4]
def baseStart_1205541 : Nat := 118140960795 + 1205541 * 2 ^ 59
def prefixEnd_1205541 : Nat := 4983230072969 + 3 ^ 40 * 1205541 * 2
def baseEnd_1205541 : Nat := 275120880756432466219255

theorem tailTrace_1205541 : CollatzResearch.WordTrace tailWord_1205541 prefixEnd_1205541 275120880756432466219255 := by
  unfold tailWord_1205541
  simp only [CollatzResearch.WordTrace]
  refine ⟨43969692525538321856168477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29313128350358881237445651 43969692525538321856168477)
  ·
    refine ⟨16488634697076870696063179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43969692525538321856168477 16488634697076870696063179)
    ·
      refine ⟨24732952045615306044094769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16488634697076870696063179 24732952045615306044094769)
      ·
        refine ⟨18549714034211479533071077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24732952045615306044094769 18549714034211479533071077)
        ·
          refine ⟨3478071381414652412450827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18549714034211479533071077 3478071381414652412450827)
          ·
            refine ⟨5217107072121978618676241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3478071381414652412450827 5217107072121978618676241)
            ·
              refine ⟨3912830304091483964007181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5217107072121978618676241 3912830304091483964007181)
              ·
                refine ⟨1467311364034306486502693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3912830304091483964007181 1467311364034306486502693)
                ·
                  refine ⟨275120880756432466219255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1467311364034306486502693 275120880756432466219255)
                  ·
                    rfl

theorem cell21_1205541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_1205541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205541 prefixEnd_1205541 := by exact prefixLift 1205541
  have htrace : WordTrace (prefixWord ++ tailWord_1205541) baseStart_1205541 baseEnd_1205541 := by
    simpa [prefixWord, tailWord_1205541, baseEnd_1205541] using wordTrace_append hprefix tailTrace_1205541
  have hstable : (prefixWord ++ tailWord_1205541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205541).length < 2 ^ (prefixWord ++ tailWord_1205541).sum := by decide
  have hdescent : baseEnd_1205541 < baseStart_1205541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205572 : List Nat := [2, 3, 4, 1, 1, 2, 8]
def baseStart_1205572 : Nat := 118140960795 + 1205572 * 2 ^ 59
def prefixEnd_1205572 : Nat := 4983230072969 + 3 ^ 40 * 1205572 * 2
def baseEnd_1205572 : Nat := 30569772819864811244725

theorem tailTrace_1205572 : CollatzResearch.WordTrace tailWord_1205572 prefixEnd_1205572 30569772819864811244725 := by
  unfold tailWord_1205572
  simp only [CollatzResearch.WordTrace]
  refine ⟨21985411594213007075273485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29313882125617342767031313 21985411594213007075273485)
  ·
    refine ⟨8244529347829877653227557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21985411594213007075273485 8244529347829877653227557)
    ·
      refine ⟨1545849252718102059980167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8244529347829877653227557 1545849252718102059980167)
      ·
        refine ⟨2318773879077153089970251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1545849252718102059980167 2318773879077153089970251)
        ·
          refine ⟨3478160818615729634955377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2318773879077153089970251 3478160818615729634955377)
          ·
            refine ⟨2608620613961797226216533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3478160818615729634955377 2608620613961797226216533)
            ·
              refine ⟨30569772819864811244725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2608620613961797226216533 30569772819864811244725)
              ·
                rfl

theorem cell21_1205572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 8].length) (baseStart_1205572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205572 prefixEnd_1205572 := by exact prefixLift 1205572
  have htrace : WordTrace (prefixWord ++ tailWord_1205572) baseStart_1205572 baseEnd_1205572 := by
    simpa [prefixWord, tailWord_1205572, baseEnd_1205572] using wordTrace_append hprefix tailTrace_1205572
  have hstable : (prefixWord ++ tailWord_1205572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205572).length < 2 ^ (prefixWord ++ tailWord_1205572).sum := by decide
  have hdescent : baseEnd_1205572 < baseStart_1205572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205634 : List Nat := [3, 4, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1205634 : Nat := 118140960795 + 1205634 * 2 ^ 59
def prefixEnd_1205634 : Nat := 4983230072969 + 3 ^ 40 * 1205634 * 2
def baseEnd_1205634 : Nat := 275142104623484971169065

theorem tailTrace_1205634 : CollatzResearch.WordTrace tailWord_1205634 prefixEnd_1205634 275142104623484971169065 := by
  unfold tailWord_1205634
  simp only [CollatzResearch.WordTrace]
  refine ⟨10993271128550349684825989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29315389676134265826202637 10993271128550349684825989)
  ·
    refine ⟨2061238336603190565904873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10993271128550349684825989 2061238336603190565904873)
    ·
      refine ⟨1545928752452392924428655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2061238336603190565904873 1545928752452392924428655)
      ·
        refine ⟨2318893128678589386642983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1545928752452392924428655 2318893128678589386642983)
        ·
          refine ⟨3478339693017884079964475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2318893128678589386642983 3478339693017884079964475)
          ·
            refine ⟨5217509539526826119946713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3478339693017884079964475 5217509539526826119946713)
            ·
              refine ⟨3913132154645119589960035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5217509539526826119946713 3913132154645119589960035)
              ·
                refine ⟨5869698231967679384940053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913132154645119589960035 5869698231967679384940053)
                ·
                  refine ⟨275142104623484971169065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5869698231967679384940053 275142104623484971169065)
                  ·
                    rfl

theorem cell21_1205634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1205634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205634 prefixEnd_1205634 := by exact prefixLift 1205634
  have htrace : WordTrace (prefixWord ++ tailWord_1205634) baseStart_1205634 baseEnd_1205634 := by
    simpa [prefixWord, tailWord_1205634, baseEnd_1205634] using wordTrace_append hprefix tailTrace_1205634
  have hstable : (prefixWord ++ tailWord_1205634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205634).length < 2 ^ (prefixWord ++ tailWord_1205634).sum := by decide
  have hdescent : baseEnd_1205634 < baseStart_1205634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205693 : List Nat := [1, 4, 1, 2, 2, 1, 4, 2, 4]
def baseStart_1205693 : Nat := 118140960795 + 1205693 * 2 ^ 59
def prefixEnd_1205693 : Nat := 4983230072969 + 3 ^ 40 * 1205693 * 2
def baseEnd_1205693 : Nat := 275155569227313979685611

theorem tailTrace_1205693 : CollatzResearch.WordTrace tailWord_1205693 prefixEnd_1205693 275155569227313979685611 := by
  unfold tailWord_1205693
  simp only [CollatzResearch.WordTrace]
  refine ⟨43975236420987651815701733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29316824280658434543801155 43975236420987651815701733)
  ·
    refine ⟨8245356828935184715444075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43975236420987651815701733 8245356828935184715444075)
    ·
      refine ⟨12368035243402777073166113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8245356828935184715444075 12368035243402777073166113)
      ·
        refine ⟨9276026432552082804874585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12368035243402777073166113 9276026432552082804874585)
        ·
          refine ⟨6957019824414062103655939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9276026432552082804874585 6957019824414062103655939)
          ·
            refine ⟨10435529736621093155483909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6957019824414062103655939 10435529736621093155483909)
            ·
              refine ⟨1956661825616454966653233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10435529736621093155483909 1956661825616454966653233)
              ·
                refine ⟨1467496369212341224989925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1956661825616454966653233 1467496369212341224989925)
                ·
                  refine ⟨275155569227313979685611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1467496369212341224989925 275155569227313979685611)
                  ·
                    rfl

theorem cell21_1205693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_1205693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205693 prefixEnd_1205693 := by exact prefixLift 1205693
  have htrace : WordTrace (prefixWord ++ tailWord_1205693) baseStart_1205693 baseEnd_1205693 := by
    simpa [prefixWord, tailWord_1205693, baseEnd_1205693] using wordTrace_append hprefix tailTrace_1205693
  have hstable : (prefixWord ++ tailWord_1205693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205693).length < 2 ^ (prefixWord ++ tailWord_1205693).sum := by decide
  have hdescent : baseEnd_1205693 < baseStart_1205693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205721 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 7]
def baseStart_1205721 : Nat := 118140960795 + 1205721 * 2 ^ 59
def prefixEnd_1205721 : Nat := 4983230072969 + 3 ^ 40 * 1205721 * 2
def baseEnd_1205721 : Nat := 275161959208792153218887

theorem tailTrace_1205721 : CollatzResearch.WordTrace tailWord_1205721 prefixEnd_1205721 275161959208792153218887 := by
  unfold tailWord_1205721
  simp only [CollatzResearch.WordTrace]
  refine ⟨43976257664886212597721017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29317505109924141731814011 43976257664886212597721017)
  ·
    refine ⟨32982193248664659448290763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43976257664886212597721017 32982193248664659448290763)
    ·
      refine ⟨49473289872996989172436145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32982193248664659448290763 49473289872996989172436145)
      ·
        refine ⟨37104967404747741879327109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49473289872996989172436145 37104967404747741879327109)
        ·
          refine ⟨6957181388390201602373833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37104967404747741879327109 6957181388390201602373833)
          ·
            refine ⟨5217886041292651201780375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6957181388390201602373833 5217886041292651201780375)
            ·
              refine ⟨7826829061938976802670563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5217886041292651201780375 7826829061938976802670563)
              ·
                refine ⟨11740243592908465204005845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7826829061938976802670563 11740243592908465204005845)
                ·
                  refine ⟨275161959208792153218887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11740243592908465204005845 275161959208792153218887)
                  ·
                    rfl

theorem cell21_1205721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_1205721 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205721 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205721 prefixEnd_1205721 := by exact prefixLift 1205721
  have htrace : WordTrace (prefixWord ++ tailWord_1205721) baseStart_1205721 baseEnd_1205721 := by
    simpa [prefixWord, tailWord_1205721, baseEnd_1205721] using wordTrace_append hprefix tailTrace_1205721
  have hstable : (prefixWord ++ tailWord_1205721).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205721).length < 2 ^ (prefixWord ++ tailWord_1205721).sum := by decide
  have hdescent : baseEnd_1205721 < baseStart_1205721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205752 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 6]
def baseStart_1205752 : Nat := 118140960795 + 1205752 * 2 ^ 59
def prefixEnd_1205752 : Nat := 4983230072969 + 3 ^ 40 * 1205752 * 2
def baseEnd_1205752 : Nat := 275169033831142988202157

theorem tailTrace_1205752 : CollatzResearch.WordTrace tailWord_1205752 prefixEnd_1205752 275169033831142988202157 := by
  unfold tailWord_1205752
  simp only [CollatzResearch.WordTrace]
  refine ⟨21988694163886952446049755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29318258885182603261399673 21988694163886952446049755)
  ·
    refine ⟨32983041245830428669074633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21988694163886952446049755 32983041245830428669074633)
    ·
      refine ⟨24737280934372821501805975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32983041245830428669074633 24737280934372821501805975)
      ·
        refine ⟨37105921401559232252708963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24737280934372821501805975 37105921401559232252708963)
        ·
          refine ⟨55658882102338848379063445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37105921401559232252708963 55658882102338848379063445)
          ·
            refine ⟨2609010098547133517768599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 55658882102338848379063445 2609010098547133517768599)
            ·
              refine ⟨3913515147820700276652899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2609010098547133517768599 3913515147820700276652899)
              ·
                refine ⟨5870272721731050414979349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3913515147820700276652899 5870272721731050414979349)
                ·
                  refine ⟨275169033831142988202157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5870272721731050414979349 275169033831142988202157)
                  ·
                    rfl

theorem cell21_1205752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_1205752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205752 prefixEnd_1205752 := by exact prefixLift 1205752
  have htrace : WordTrace (prefixWord ++ tailWord_1205752) baseStart_1205752 baseEnd_1205752 := by
    simpa [prefixWord, tailWord_1205752, baseEnd_1205752] using wordTrace_append hprefix tailTrace_1205752
  have hstable : (prefixWord ++ tailWord_1205752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205752).length < 2 ^ (prefixWord ++ tailWord_1205752).sum := by decide
  have hdescent : baseEnd_1205752 < baseStart_1205752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205769 : List Nat := [1, 2, 1, 1, 3, 1, 7, 1, 4]
def baseStart_1205769 : Nat := 118140960795 + 1205769 * 2 ^ 59
def prefixEnd_1205769 : Nat := 4983230072969 + 3 ^ 40 * 1205769 * 2
def baseEnd_1205769 : Nat := 275172913462754736418789

theorem tailTrace_1205769 : CollatzResearch.WordTrace tailWord_1205769 prefixEnd_1205769 275172913462754736418789 := by
  unfold tailWord_1205769
  simp only [CollatzResearch.WordTrace]
  refine ⟨43978008368712316795468361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29318672245808211196978907 43978008368712316795468361)
  ·
    refine ⟨32983506276534237596601271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43978008368712316795468361 32983506276534237596601271)
    ·
      refine ⟨49475259414801356394901907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32983506276534237596601271 49475259414801356394901907)
      ·
        refine ⟨74212889122202034592352861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49475259414801356394901907 74212889122202034592352861)
        ·
          refine ⟨27829833420825762972132323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74212889122202034592352861 27829833420825762972132323)
          ·
            refine ⟨41744750131238644458198485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27829833420825762972132323 41744750131238644458198485)
            ·
              refine ⟨978392581200905729489027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 41744750131238644458198485 978392581200905729489027)
              ·
                refine ⟨1467588871801358594233541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 978392581200905729489027 1467588871801358594233541)
                ·
                  refine ⟨275172913462754736418789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1467588871801358594233541 275172913462754736418789)
                  ·
                    rfl

theorem cell21_1205769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 1, 4].length) (baseStart_1205769 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205769 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205769 prefixEnd_1205769 := by exact prefixLift 1205769
  have htrace : WordTrace (prefixWord ++ tailWord_1205769) baseStart_1205769 baseEnd_1205769 := by
    simpa [prefixWord, tailWord_1205769, baseEnd_1205769] using wordTrace_append hprefix tailTrace_1205769
  have hstable : (prefixWord ++ tailWord_1205769).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205769).length < 2 ^ (prefixWord ++ tailWord_1205769).sum := by decide
  have hdescent : baseEnd_1205769 < baseStart_1205769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205800 : List Nat := [2, 1, 5, 2, 2, 2, 7]
def baseStart_1205800 : Nat := 118140960795 + 1205800 * 2 ^ 59
def prefixEnd_1205800 : Nat := 4983230072969 + 3 ^ 40 * 1205800 * 2
def baseEnd_1205800 : Nat := 30575554231678396822451

theorem tailTrace_1205800 : CollatzResearch.WordTrace tailWord_1205800 prefixEnd_1205800 30575554231678396822451 := by
  unfold tailWord_1205800
  simp only [CollatzResearch.WordTrace]
  refine ⟨21989569515800004544923427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29319426021066672726564569 21989569515800004544923427)
  ·
    refine ⟨32984354273700006817385141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21989569515800004544923427 32984354273700006817385141)
    ·
      refine ⟨3092283213159375639129857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32984354273700006817385141 3092283213159375639129857)
      ·
        refine ⟨2319212409869531729347393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3092283213159375639129857 2319212409869531729347393)
        ·
          refine ⟨1739409307402148797010545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2319212409869531729347393 1739409307402148797010545)
          ·
            refine ⟨1304556980551611597757909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1739409307402148797010545 1304556980551611597757909)
            ·
              refine ⟨30575554231678396822451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1304556980551611597757909 30575554231678396822451)
              ·
                rfl

theorem cell21_1205800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 7].length) (baseStart_1205800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205800 prefixEnd_1205800 := by exact prefixLift 1205800
  have htrace : WordTrace (prefixWord ++ tailWord_1205800) baseStart_1205800 baseEnd_1205800 := by
    simpa [prefixWord, tailWord_1205800, baseEnd_1205800] using wordTrace_append hprefix tailTrace_1205800
  have hstable : (prefixWord ++ tailWord_1205800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205800).length < 2 ^ (prefixWord ++ tailWord_1205800).sum := by decide
  have hdescent : baseEnd_1205800 < baseStart_1205800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205921 : List Nat := [1, 2, 3, 3, 2, 1, 3, 2, 4]
def baseStart_1205921 : Nat := 118140960795 + 1205921 * 2 ^ 59
def prefixEnd_1205921 : Nat := 4983230072969 + 3 ^ 40 * 1205921 * 2
def baseEnd_1205921 : Nat := 275207601933636249885145

theorem tailTrace_1205921 : CollatzResearch.WordTrace tailWord_1205921 prefixEnd_1205921 275207601933636249885145 := by
  unfold tailWord_1205921
  simp only [CollatzResearch.WordTrace]
  refine ⟨43983552264161646755001617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29322368176107764503334411 43983552264161646755001617)
  ·
    refine ⟨32987664198121235066251213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43983552264161646755001617 32987664198121235066251213)
    ·
      refine ⟨12370374074295463149844205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32987664198121235066251213 12370374074295463149844205)
      ·
        refine ⟨4638890277860798681191577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12370374074295463149844205 4638890277860798681191577)
        ·
          refine ⟨3479167708395599010893683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4638890277860798681191577 3479167708395599010893683)
          ·
            refine ⟨5218751562593398516340525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3479167708395599010893683 5218751562593398516340525)
            ·
              refine ⟨1957031835972524443627697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5218751562593398516340525 1957031835972524443627697)
              ·
                refine ⟨1467773876979393332720773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1957031835972524443627697 1467773876979393332720773)
                ·
                  refine ⟨275207601933636249885145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1467773876979393332720773 275207601933636249885145)
                  ·
                    rfl

theorem cell21_1205921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_1205921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205921 prefixEnd_1205921 := by exact prefixLift 1205921
  have htrace : WordTrace (prefixWord ++ tailWord_1205921) baseStart_1205921 baseEnd_1205921 := by
    simpa [prefixWord, tailWord_1205921, baseEnd_1205921] using wordTrace_append hprefix tailTrace_1205921
  have hstable : (prefixWord ++ tailWord_1205921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205921).length < 2 ^ (prefixWord ++ tailWord_1205921).sum := by decide
  have hdescent : baseEnd_1205921 < baseStart_1205921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205949 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 5]
def baseStart_1205949 : Nat := 118140960795 + 1205949 * 2 ^ 59
def prefixEnd_1205949 : Nat := 4983230072969 + 3 ^ 40 * 1205949 * 2
def baseEnd_1205949 : Nat := 275213991915114423418421

theorem tailTrace_1205949 : CollatzResearch.WordTrace tailWord_1205949 prefixEnd_1205949 275213991915114423418421 := by
  unfold tailWord_1205949
  simp only [CollatzResearch.WordTrace]
  refine ⟨43984573508060207537020901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29323049005373471691347267 43984573508060207537020901)
  ·
    refine ⟨8247107532761288913191419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43984573508060207537020901 8247107532761288913191419)
    ·
      refine ⟨12370661299141933369787129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8247107532761288913191419 12370661299141933369787129)
      ·
        refine ⟨9277995974356450027340347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12370661299141933369787129 9277995974356450027340347)
        ·
          refine ⟨13916993961534675041010521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9277995974356450027340347 13916993961534675041010521)
          ·
            refine ⟨10437745471151006280757891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13916993961534675041010521 10437745471151006280757891)
            ·
              refine ⟨15656618206726509421136837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10437745471151006280757891 15656618206726509421136837)
              ·
                refine ⟨2935615913761220516463157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15656618206726509421136837 2935615913761220516463157)
                ·
                  refine ⟨275213991915114423418421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2935615913761220516463157 275213991915114423418421)
                  ·
                    rfl

theorem cell21_1205949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_1205949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205949 prefixEnd_1205949 := by exact prefixLift 1205949
  have htrace : WordTrace (prefixWord ++ tailWord_1205949) baseStart_1205949 baseEnd_1205949 := by
    simpa [prefixWord, tailWord_1205949, baseEnd_1205949] using wordTrace_append hprefix tailTrace_1205949
  have hstable : (prefixWord ++ tailWord_1205949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205949).length < 2 ^ (prefixWord ++ tailWord_1205949).sum := by decide
  have hdescent : baseEnd_1205949 < baseStart_1205949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205958 : List Nat := [6, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_1205958 : Nat := 118140960795 + 1205958 * 2 ^ 59
def prefixEnd_1205958 : Nat := 4983230072969 + 3 ^ 40 * 1205958 * 2
def baseEnd_1205958 : Nat := 275216045837732407768403

theorem tailTrace_1205958 : CollatzResearch.WordTrace tailWord_1205958 prefixEnd_1205958 275216045837732407768403 := by
  unfold tailWord_1205958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1374528180157112564815579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29323267843351734716065685 1374528180157112564815579)
  ·
    refine ⟨2061792270235668847223369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1374528180157112564815579 2061792270235668847223369)
    ·
      refine ⟨1546344202676751635417527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2061792270235668847223369 1546344202676751635417527)
      ·
        refine ⟨2319516304015127453126291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1546344202676751635417527 2319516304015127453126291)
        ·
          refine ⟨3479274456022691179689437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2319516304015127453126291 3479274456022691179689437)
          ·
            refine ⟨1304727921008509192383539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3479274456022691179689437 1304727921008509192383539)
            ·
              refine ⟨1957091881512763788575309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1304727921008509192383539 1957091881512763788575309)
              ·
                refine ⟨733909455567286420715741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1957091881512763788575309 733909455567286420715741)
                ·
                  refine ⟨275216045837732407768403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733909455567286420715741 275216045837732407768403)
                  ·
                    rfl

theorem cell21_1205958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_1205958 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205958 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205958 prefixEnd_1205958 := by exact prefixLift 1205958
  have htrace : WordTrace (prefixWord ++ tailWord_1205958) baseStart_1205958 baseEnd_1205958 := by
    simpa [prefixWord, tailWord_1205958, baseEnd_1205958] using wordTrace_append hprefix tailTrace_1205958
  have hstable : (prefixWord ++ tailWord_1205958).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205958).length < 2 ^ (prefixWord ++ tailWord_1205958).sum := by decide
  have hdescent : baseEnd_1205958 < baseStart_1205958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205983 : List Nat := [1, 1, 2, 3, 2, 2, 5, 2, 3]
def baseStart_1205983 : Nat := 118140960795 + 1205983 * 2 ^ 59
def prefixEnd_1205983 : Nat := 4983230072969 + 3 ^ 40 * 1205983 * 2
def baseEnd_1205983 : Nat := 275221751178337919851685

theorem tailTrace_1205983 : CollatzResearch.WordTrace tailWord_1205983 prefixEnd_1205983 275221751178337919851685 := by
  unfold tailWord_1205983
  simp only [CollatzResearch.WordTrace]
  refine ⟨43985813589937031343758603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29323875726624687562505735 43985813589937031343758603)
  ·
    refine ⟨65978720384905547015637905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43985813589937031343758603 65978720384905547015637905)
    ·
      refine ⟨49484040288679160261728429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65978720384905547015637905 49484040288679160261728429)
      ·
        refine ⟨18556515108254685098148161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49484040288679160261728429 18556515108254685098148161)
        ·
          refine ⟨13917386331191013823611121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18556515108254685098148161 13917386331191013823611121)
          ·
            refine ⟨10438039748393260367708341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13917386331191013823611121 10438039748393260367708341)
            ·
              refine ⟨978566226411868159472657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10438039748393260367708341 978566226411868159472657)
              ·
                refine ⟨733924669808901119604493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 978566226411868159472657 733924669808901119604493)
                ·
                  refine ⟨275221751178337919851685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 733924669808901119604493 275221751178337919851685)
                  ·
                    rfl

theorem cell21_1205983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 2, 3].length) (baseStart_1205983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205983 prefixEnd_1205983 := by exact prefixLift 1205983
  have htrace : WordTrace (prefixWord ++ tailWord_1205983) baseStart_1205983 baseEnd_1205983 := by
    simpa [prefixWord, tailWord_1205983, baseEnd_1205983] using wordTrace_append hprefix tailTrace_1205983
  have hstable : (prefixWord ++ tailWord_1205983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205983).length < 2 ^ (prefixWord ++ tailWord_1205983).sum := by decide
  have hdescent : baseEnd_1205983 < baseStart_1205983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205994 : List Nat := [3, 1, 3, 1, 1, 1, 3, 8]
def baseStart_1205994 : Nat := 118140960795 + 1205994 * 2 ^ 59
def prefixEnd_1205994 : Nat := 4983230072969 + 3 ^ 40 * 1205994 * 2
def baseEnd_1205994 : Nat := 91741420509401448389443

theorem tailTrace_1205994 : CollatzResearch.WordTrace tailWord_1205994 prefixEnd_1205994 91741420509401448389443 := by
  unfold tailWord_1205994
  simp only [CollatzResearch.WordTrace]
  refine ⟨10996553698224295055602259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29324143195264786814939357 10996553698224295055602259)
  ·
    refine ⟨16494830547336442583403389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10996553698224295055602259 16494830547336442583403389)
    ·
      refine ⟨6185561455251165968776271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16494830547336442583403389 6185561455251165968776271)
      ·
        refine ⟨9278342182876748953164407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6185561455251165968776271 9278342182876748953164407)
        ·
          refine ⟨13917513274315123429746611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9278342182876748953164407 13917513274315123429746611)
          ·
            refine ⟨20876269911472685144619917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13917513274315123429746611 20876269911472685144619917)
            ·
              refine ⟨7828601216802256929232469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20876269911472685144619917 7828601216802256929232469)
              ·
                refine ⟨91741420509401448389443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7828601216802256929232469 91741420509401448389443)
                ·
                  rfl

theorem cell21_1205994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_1205994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205994 prefixEnd_1205994 := by exact prefixLift 1205994
  have htrace : WordTrace (prefixWord ++ tailWord_1205994) baseStart_1205994 baseEnd_1205994 := by
    simpa [prefixWord, tailWord_1205994, baseEnd_1205994] using wordTrace_append hprefix tailTrace_1205994
  have hstable : (prefixWord ++ tailWord_1205994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205994).length < 2 ^ (prefixWord ++ tailWord_1205994).sum := by decide
  have hdescent : baseEnd_1205994 < baseStart_1205994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1205997 : List Nat := [1, 5, 1, 2, 1, 3, 1, 3, 4]
def baseStart_1205997 : Nat := 118140960795 + 1205997 * 2 ^ 59
def prefixEnd_1205997 : Nat := 4983230072969 + 3 ^ 40 * 1205997 * 2
def baseEnd_1205997 : Nat := 275224946169077006618323

theorem tailTrace_1205997 : CollatzResearch.WordTrace tailWord_1205997 prefixEnd_1205997 275224946169077006618323 := by
  unfold tailWord_1205997
  simp only [CollatzResearch.WordTrace]
  refine ⟨43986324211886311734768245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29324216141257541156512163 43986324211886311734768245)
  ·
    refine ⟨4123717894864341725134523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43986324211886311734768245 4123717894864341725134523)
    ·
      refine ⟨6185576842296512587701785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4123717894864341725134523 6185576842296512587701785)
      ·
        refine ⟨4639182631722384440776339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6185576842296512587701785 4639182631722384440776339)
        ·
          refine ⟨6958773947583576661164509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4639182631722384440776339 6958773947583576661164509)
          ·
            refine ⟨2609540230343841247936691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6958773947583576661164509 2609540230343841247936691)
            ·
              refine ⟨3914310345515761871905037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2609540230343841247936691 3914310345515761871905037)
              ·
                refine ⟨1467866379568410701964389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3914310345515761871905037 1467866379568410701964389)
                ·
                  refine ⟨275224946169077006618323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1467866379568410701964389 275224946169077006618323)
                  ·
                    rfl

theorem cell21_1205997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_1205997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1205997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1205997 prefixEnd_1205997 := by exact prefixLift 1205997
  have htrace : WordTrace (prefixWord ++ tailWord_1205997) baseStart_1205997 baseEnd_1205997 := by
    simpa [prefixWord, tailWord_1205997, baseEnd_1205997] using wordTrace_append hprefix tailTrace_1205997
  have hstable : (prefixWord ++ tailWord_1205997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1205997).length < 2 ^ (prefixWord ++ tailWord_1205997).sum := by decide
  have hdescent : baseEnd_1205997 < baseStart_1205997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1205997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206101 : List Nat := [1, 3, 2, 2, 2, 2, 1, 3, 5]
def baseStart_1206101 : Nat := 118140960795 + 1206101 * 2 ^ 59
def prefixEnd_1206101 : Nat := 4983230072969 + 3 ^ 40 * 1206101 * 2
def baseEnd_1206101 : Nat := 275248680385995936884777

theorem tailTrace_1206101 : CollatzResearch.WordTrace tailWord_1206101 prefixEnd_1206101 275248680385995936884777 := by
  unfold tailWord_1206101
  simp only [CollatzResearch.WordTrace]
  refine ⟨43990117403509537496554157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29326744935673024997702771 43990117403509537496554157)
  ·
    refine ⟨16496294026316076561207809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43990117403509537496554157 16496294026316076561207809)
    ·
      refine ⟨12372220519737057420905857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16496294026316076561207809 12372220519737057420905857)
      ·
        refine ⟨9279165389802793065679393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12372220519737057420905857 9279165389802793065679393)
        ·
          refine ⟨6959374042352094799259545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9279165389802793065679393 6959374042352094799259545)
          ·
            refine ⟨5219530531764071099444659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6959374042352094799259545 5219530531764071099444659)
            ·
              refine ⟨7829295797646106649166989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5219530531764071099444659 7829295797646106649166989)
              ·
                refine ⟨2935985924117289993437621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7829295797646106649166989 2935985924117289993437621)
                ·
                  refine ⟨275248680385995936884777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2935985924117289993437621 275248680385995936884777)
                  ·
                    rfl

theorem cell21_1206101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 3, 5].length) (baseStart_1206101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1206101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1206101 prefixEnd_1206101 := by exact prefixLift 1206101
  have htrace : WordTrace (prefixWord ++ tailWord_1206101) baseStart_1206101 baseEnd_1206101 := by
    simpa [prefixWord, tailWord_1206101, baseEnd_1206101] using wordTrace_append hprefix tailTrace_1206101
  have hstable : (prefixWord ++ tailWord_1206101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206101).length < 2 ^ (prefixWord ++ tailWord_1206101).sum := by decide
  have hdescent : baseEnd_1206101 < baseStart_1206101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206152 : List Nat := [2, 1, 3, 3, 3, 1, 3, 2, 3]
def baseStart_1206152 : Nat := 118140960795 + 1206152 * 2 ^ 59
def prefixEnd_1206152 : Nat := 4983230072969 + 3 ^ 40 * 1206152 * 2
def baseEnd_1206152 : Nat := 275260319280831181534673

theorem tailTrace_1206152 : CollatzResearch.WordTrace tailWord_1206152 prefixEnd_1206152 275260319280831181534673 := by
  unfold tailWord_1206152
  simp only [CollatzResearch.WordTrace]
  refine ⟨21995988763162386603330355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29327985017549848804440473 21995988763162386603330355)
  ·
    refine ⟨32993983144743579904995533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21995988763162386603330355 32993983144743579904995533)
    ·
      refine ⟨12372743679278842464373325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32993983144743579904995533 12372743679278842464373325)
      ·
        refine ⟨4639778879729565924139997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12372743679278842464373325 4639778879729565924139997)
        ·
          refine ⟨1739917079898587221552499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4639778879729565924139997 1739917079898587221552499)
          ·
            refine ⟨2609875619847880832328749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1739917079898587221552499 2609875619847880832328749)
            ·
              refine ⟨978703357442955312123281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2609875619847880832328749 978703357442955312123281)
              ·
                refine ⟨734027518082216484092461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 978703357442955312123281 734027518082216484092461)
                ·
                  refine ⟨275260319280831181534673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 734027518082216484092461 275260319280831181534673)
                  ·
                    rfl

theorem cell21_1206152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 3, 2, 3].length) (baseStart_1206152 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1206152 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1206152 prefixEnd_1206152 := by exact prefixLift 1206152
  have htrace : WordTrace (prefixWord ++ tailWord_1206152) baseStart_1206152 baseEnd_1206152 := by
    simpa [prefixWord, tailWord_1206152, baseEnd_1206152] using wordTrace_append hprefix tailTrace_1206152
  have hstable : (prefixWord ++ tailWord_1206152).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206152).length < 2 ^ (prefixWord ++ tailWord_1206152).sum := by decide
  have hdescent : baseEnd_1206152 < baseStart_1206152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206208 : List Nat := [2, 1, 1, 2, 3, 2, 4, 2, 4]
def baseStart_1206208 : Nat := 118140960795 + 1206208 * 2 ^ 59
def prefixEnd_1206208 : Nat := 4983230072969 + 3 ^ 40 * 1206208 * 2
def baseEnd_1206208 : Nat := 275273099243787528601225

theorem tailTrace_1206208 : CollatzResearch.WordTrace tailWord_1206208 prefixEnd_1206208 275273099243787528601225 := by
  unfold tailWord_1206208
  simp only [CollatzResearch.WordTrace]
  refine ⟨21997010007060947385349639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29329346676081263180466185 21997010007060947385349639)
  ·
    refine ⟨32995515010591421078024459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21997010007060947385349639 32995515010591421078024459)
    ·
      refine ⟨49493272515887131617036689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32995515010591421078024459 49493272515887131617036689)
      ·
        refine ⟨37119954386915348712777517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49493272515887131617036689 37119954386915348712777517)
        ·
          refine ⟨13919982895093255767291569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37119954386915348712777517 13919982895093255767291569)
          ·
            refine ⟨10439987171319941825468677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13919982895093255767291569 10439987171319941825468677)
            ·
              refine ⟨1957497594622489092275377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10439987171319941825468677 1957497594622489092275377)
              ·
                refine ⟨1468123195966866819206533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1957497594622489092275377 1468123195966866819206533)
                ·
                  refine ⟨275273099243787528601225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1468123195966866819206533 275273099243787528601225)
                  ·
                    rfl

theorem cell21_1206208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_1206208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1206208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1206208 prefixEnd_1206208 := by exact prefixLift 1206208
  have htrace : WordTrace (prefixWord ++ tailWord_1206208) baseStart_1206208 baseEnd_1206208 := by
    simpa [prefixWord, tailWord_1206208, baseEnd_1206208] using wordTrace_append hprefix tailTrace_1206208
  have hstable : (prefixWord ++ tailWord_1206208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206208).length < 2 ^ (prefixWord ++ tailWord_1206208).sum := by decide
  have hdescent : baseEnd_1206208 < baseStart_1206208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206239 : List Nat := [1, 1, 2, 3, 4, 2, 3, 5]
def baseStart_1206239 : Nat := 118140960795 + 1206239 * 2 ^ 59
def prefixEnd_1206239 : Nat := 4983230072969 + 3 ^ 40 * 1206239 * 2
def baseEnd_1206239 : Nat := 91760057955379454528165

theorem tailTrace_1206239 : CollatzResearch.WordTrace tailWord_1206239 prefixEnd_1206239 91760057955379454528165 := by
  unfold tailWord_1206239
  simp only [CollatzResearch.WordTrace]
  refine ⟨43995150677009587065077771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29330100451339724710051847 43995150677009587065077771)
  ·
    refine ⟨65992726015514380597616657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43995150677009587065077771 65992726015514380597616657)
    ·
      refine ⟨49494544511635785448212493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65992726015514380597616657 49494544511635785448212493)
      ·
        refine ⟨18560454191863419543079685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49494544511635785448212493 18560454191863419543079685)
        ·
          refine ⟨3480085160974391164327441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18560454191863419543079685 3480085160974391164327441)
          ·
            refine ⟨2610063870730793373245581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3480085160974391164327441 2610063870730793373245581)
            ·
              refine ⟨978773951524047514967093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2610063870730793373245581 978773951524047514967093)
              ·
                refine ⟨91760057955379454528165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 978773951524047514967093 91760057955379454528165)
                ·
                  rfl

theorem cell21_1206239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 3, 5].length) (baseStart_1206239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1206239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1206239 prefixEnd_1206239 := by exact prefixLift 1206239
  have htrace : WordTrace (prefixWord ++ tailWord_1206239) baseStart_1206239 baseEnd_1206239 := by
    simpa [prefixWord, tailWord_1206239, baseEnd_1206239] using wordTrace_append hprefix tailTrace_1206239
  have hstable : (prefixWord ++ tailWord_1206239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206239).length < 2 ^ (prefixWord ++ tailWord_1206239).sum := by decide
  have hdescent : baseEnd_1206239 < baseStart_1206239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206270 : List Nat := [4, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1206270 : Nat := 118140960795 + 1206270 * 2 ^ 59
def prefixEnd_1206270 : Nat := 4983230072969 + 3 ^ 40 * 1206270 * 2
def baseEnd_1206270 : Nat := 275287248488489198567765

theorem tailTrace_1206270 : CollatzResearch.WordTrace tailWord_1206270 prefixEnd_1206270 275287248488489198567765 := by
  unfold tailWord_1206270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5499535167487159919932033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29330854226598186239637509 5499535167487159919932033)
  ·
    refine ⟨4124651375615369939949025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5499535167487159919932033 4124651375615369939949025)
    ·
      refine ⟨3093488531711527454961769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4124651375615369939949025 3093488531711527454961769)
      ·
        refine ⟨2320116398783645591221327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3093488531711527454961769 2320116398783645591221327)
        ·
          refine ⟨3480174598175468386831991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2320116398783645591221327 3480174598175468386831991)
          ·
            refine ⟨5220261897263202580247987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3480174598175468386831991 5220261897263202580247987)
            ·
              refine ⟨7830392845894803870371981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5220261897263202580247987 7830392845894803870371981)
              ·
                refine ⟨2936397317210551451389493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7830392845894803870371981 2936397317210551451389493)
                ·
                  refine ⟨275287248488489198567765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2936397317210551451389493 275287248488489198567765)
                  ·
                    rfl

theorem cell21_1206270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1206270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1206270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1206270 prefixEnd_1206270 := by exact prefixLift 1206270
  have htrace : WordTrace (prefixWord ++ tailWord_1206270) baseStart_1206270 baseEnd_1206270 := by
    simpa [prefixWord, tailWord_1206270, baseEnd_1206270] using wordTrace_append hprefix tailTrace_1206270
  have hstable : (prefixWord ++ tailWord_1206270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206270).length < 2 ^ (prefixWord ++ tailWord_1206270).sum := by decide
  have hdescent : baseEnd_1206270 < baseStart_1206270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206298 : List Nat := [3, 1, 1, 3, 1, 4, 1, 7]
def baseStart_1206298 : Nat := 118140960795 + 1206298 * 2 ^ 59
def prefixEnd_1206298 : Nat := 4983230072969 + 3 ^ 40 * 1206298 * 2
def baseEnd_1206298 : Nat := 91764546156655790700347

theorem tailTrace_1206298 : CollatzResearch.WordTrace tailWord_1206298 prefixEnd_1206298 91764546156655790700347 := by
  unfold tailWord_1206298
  simp only [CollatzResearch.WordTrace]
  refine ⟨10999325645948960035368887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29331535055863893427650365 10999325645948960035368887)
  ·
    refine ⟨16498988468923440053053331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10999325645948960035368887 16498988468923440053053331)
    ·
      refine ⟨24748482703385160079579997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16498988468923440053053331 24748482703385160079579997)
      ·
        refine ⟨9280681013769435029842499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24748482703385160079579997 9280681013769435029842499)
        ·
          refine ⟨13921021520654152544763749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9280681013769435029842499 13921021520654152544763749)
          ·
            refine ⟨2610191535122653602143203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13921021520654152544763749 2610191535122653602143203)
            ·
              refine ⟨3915287302683980403214805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610191535122653602143203 3915287302683980403214805)
              ·
                refine ⟨91764546156655790700347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3915287302683980403214805 91764546156655790700347)
                ·
                  rfl

theorem cell21_1206298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 7].length) (baseStart_1206298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1206298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1206298 prefixEnd_1206298 := by exact prefixLift 1206298
  have htrace : WordTrace (prefixWord ++ tailWord_1206298) baseStart_1206298 baseEnd_1206298 := by
    simpa [prefixWord, tailWord_1206298, baseEnd_1206298] using wordTrace_append hprefix tailTrace_1206298
  have hstable : (prefixWord ++ tailWord_1206298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206298).length < 2 ^ (prefixWord ++ tailWord_1206298).sum := by decide
  have hdescent : baseEnd_1206298 < baseStart_1206298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206405 : List Nat := [1, 3, 1, 1, 5, 2, 1, 2, 5]
def baseStart_1206405 : Nat := 118140960795 + 1206405 * 2 ^ 59
def prefixEnd_1206405 : Nat := 4983230072969 + 3 ^ 40 * 1206405 * 2
def baseEnd_1206405 : Nat := 275318057327758963817489

theorem tailTrace_1206405 : CollatzResearch.WordTrace tailWord_1206405 prefixEnd_1206405 275318057327758963817489 := by
  unfold tailWord_1206405
  simp only [CollatzResearch.WordTrace]
  refine ⟨44001205194408197415620669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29334136796272131610413779 44001205194408197415620669)
  ·
    refine ⟨16500451947903074030857751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44001205194408197415620669 16500451947903074030857751)
    ·
      refine ⟨24750677921854611046286627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16500451947903074030857751 24750677921854611046286627)
      ·
        refine ⟨37126016882781916569429941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24750677921854611046286627 37126016882781916569429941)
        ·
          refine ⟨3480564082760804678384057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37126016882781916569429941 3480564082760804678384057)
          ·
            refine ⟨2610423062070603508788043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3480564082760804678384057 2610423062070603508788043)
            ·
              refine ⟨3915634593105905263182065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610423062070603508788043 3915634593105905263182065)
              ·
                refine ⟨2936725944829428947386549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3915634593105905263182065 2936725944829428947386549)
                ·
                  refine ⟨275318057327758963817489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2936725944829428947386549 275318057327758963817489)
                  ·
                    rfl

theorem cell21_1206405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_1206405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1206405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1206405 prefixEnd_1206405 := by exact prefixLift 1206405
  have htrace : WordTrace (prefixWord ++ tailWord_1206405) baseStart_1206405 baseEnd_1206405 := by
    simpa [prefixWord, tailWord_1206405, baseEnd_1206405] using wordTrace_append hprefix tailTrace_1206405
  have hstable : (prefixWord ++ tailWord_1206405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206405).length < 2 ^ (prefixWord ++ tailWord_1206405).sum := by decide
  have hdescent : baseEnd_1206405 < baseStart_1206405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206436 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 6]
def baseStart_1206436 : Nat := 118140960795 + 1206436 * 2 ^ 59
def prefixEnd_1206436 : Nat := 4983230072969 + 3 ^ 40 * 1206436 * 2
def baseEnd_1206436 : Nat := 275325131950109798800759

theorem tailTrace_1206436 : CollatzResearch.WordTrace tailWord_1206436 prefixEnd_1206436 275325131950109798800759 := by
  unfold tailWord_1206436
  simp only [CollatzResearch.WordTrace]
  refine ⟨22001167928647944854999581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29334890571530593139999441 22001167928647944854999581)
  ·
    refine ⟨8250437973242979320624843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22001167928647944854999581 8250437973242979320624843)
    ·
      refine ⟨12375656959864468980937265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8250437973242979320624843 12375656959864468980937265)
      ·
        refine ⟨9281742719898351735702949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12375656959864468980937265 9281742719898351735702949)
        ·
          refine ⟨1740326759980940950444303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9281742719898351735702949 1740326759980940950444303)
          ·
            refine ⟨2610490139971411425666455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1740326759980940950444303 2610490139971411425666455)
            ·
              refine ⟨3915735209957117138499683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2610490139971411425666455 3915735209957117138499683)
              ·
                refine ⟨5873602814935675707749525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3915735209957117138499683 5873602814935675707749525)
                ·
                  refine ⟨275325131950109798800759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5873602814935675707749525 275325131950109798800759)
                  ·
                    rfl

theorem cell21_1206436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_1206436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1206436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1206436 prefixEnd_1206436 := by exact prefixLift 1206436
  have htrace : WordTrace (prefixWord ++ tailWord_1206436) baseStart_1206436 baseEnd_1206436 := by
    simpa [prefixWord, tailWord_1206436, baseEnd_1206436] using wordTrace_append hprefix tailTrace_1206436
  have hstable : (prefixWord ++ tailWord_1206436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206436).length < 2 ^ (prefixWord ++ tailWord_1206436).sum := by decide
  have hdescent : baseEnd_1206436 < baseStart_1206436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206495 : List Nat := [1, 1, 2, 3, 2, 1, 1, 6, 4]
def baseStart_1206495 : Nat := 118140960795 + 1206495 * 2 ^ 59
def prefixEnd_1206495 : Nat := 4983230072969 + 3 ^ 40 * 1206495 * 2
def baseEnd_1206495 : Nat := 275338596553938807317305

theorem tailTrace_1206495 : CollatzResearch.WordTrace tailWord_1206495 prefixEnd_1206495 275338596553938807317305 := by
  unfold tailWord_1206495
  simp only [CollatzResearch.WordTrace]
  refine ⟨44004487764082142786396939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29336325176054761857597959 44004487764082142786396939)
  ·
    refine ⟨66006731646123214179595409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44004487764082142786396939 66006731646123214179595409)
    ·
      refine ⟨49505048734592410634696557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66006731646123214179595409 49505048734592410634696557)
      ·
        refine ⟨18564393275472153988011209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49505048734592410634696557 18564393275472153988011209)
        ·
          refine ⟨13923294956604115491008407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18564393275472153988011209 13923294956604115491008407)
          ·
            refine ⟨20884942434906173236512611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13923294956604115491008407 20884942434906173236512611)
            ·
              refine ⟨31327413652359259854768917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20884942434906173236512611 31327413652359259854768917)
              ·
                refine ⟨1468472514954340305692293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31327413652359259854768917 1468472514954340305692293)
                ·
                  refine ⟨275338596553938807317305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1468472514954340305692293 275338596553938807317305)
                  ·
                    rfl

theorem cell21_1206495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 6, 4].length) (baseStart_1206495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1206495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1206495 prefixEnd_1206495 := by exact prefixLift 1206495
  have htrace : WordTrace (prefixWord ++ tailWord_1206495) baseStart_1206495 baseEnd_1206495 := by
    simpa [prefixWord, tailWord_1206495, baseEnd_1206495] using wordTrace_append hprefix tailTrace_1206495
  have hstable : (prefixWord ++ tailWord_1206495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206495).length < 2 ^ (prefixWord ++ tailWord_1206495).sum := by decide
  have hdescent : baseEnd_1206495 < baseStart_1206495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206526 : List Nat := [4, 2, 2, 1, 1, 1, 1, 9]
def baseStart_1206526 : Nat := 118140960795 + 1206526 * 2 ^ 59
def prefixEnd_1206526 : Nat := 4983230072969 + 3 ^ 40 * 1206526 * 2
def baseEnd_1206526 : Nat := 91781890392096547433525

theorem tailTrace_1206526 : CollatzResearch.WordTrace tailWord_1206526 prefixEnd_1206526 91781890392096547433525 := by
  unfold tailWord_1206526
  simp only [CollatzResearch.WordTrace]
  refine ⟨5500702303371229385096929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29337078951313223387183621 5500702303371229385096929)
  ·
    refine ⟨4125526727528422038822697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5500702303371229385096929 4125526727528422038822697)
    ·
      refine ⟨3094145045646316529117023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4125526727528422038822697 3094145045646316529117023)
      ·
        refine ⟨4641217568469474793675535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3094145045646316529117023 4641217568469474793675535)
        ·
          refine ⟨6961826352704212190513303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4641217568469474793675535 6961826352704212190513303)
          ·
            refine ⟨10442739529056318285769955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6961826352704212190513303 10442739529056318285769955)
            ·
              refine ⟨15664109293584477428654933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10442739529056318285769955 15664109293584477428654933)
              ·
                refine ⟨91781890392096547433525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15664109293584477428654933 91781890392096547433525)
                ·
                  rfl

theorem cell21_1206526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_1206526 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1206526 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1206526 prefixEnd_1206526 := by exact prefixLift 1206526
  have htrace : WordTrace (prefixWord ++ tailWord_1206526) baseStart_1206526 baseEnd_1206526 := by
    simpa [prefixWord, tailWord_1206526, baseEnd_1206526] using wordTrace_append hprefix tailTrace_1206526
  have hstable : (prefixWord ++ tailWord_1206526).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206526).length < 2 ^ (prefixWord ++ tailWord_1206526).sum := by decide
  have hdescent : baseEnd_1206526 < baseStart_1206526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206636 : List Nat := [2, 2, 1, 1, 7, 1, 2, 5]
def baseStart_1206636 : Nat := 118140960795 + 1206636 * 2 ^ 59
def prefixEnd_1206636 : Nat := 4983230072969 + 3 ^ 40 * 1206636 * 2
def baseEnd_1206636 : Nat := 91790258224984631822339

theorem tailTrace_1206636 : CollatzResearch.WordTrace tailWord_1206636 prefixEnd_1206636 91790258224984631822339 := by
  unfold tailWord_1206636
  simp only [CollatzResearch.WordTrace]
  refine ⟨22004815228285661933639881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29339753637714215911519841 22004815228285661933639881)
  ·
    refine ⟨16503611421214246450229911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22004815228285661933639881 16503611421214246450229911)
    ·
      refine ⟨24755417131821369675344867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16503611421214246450229911 24755417131821369675344867)
      ·
        refine ⟨37133125697732054513017301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24755417131821369675344867 37133125697732054513017301)
        ·
          refine ⟨870307633540595027648843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 37133125697732054513017301 870307633540595027648843)
          ·
            refine ⟨1305461450310892541473265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870307633540595027648843 1305461450310892541473265)
            ·
              refine ⟨979096087733169406104949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1305461450310892541473265 979096087733169406104949)
              ·
                refine ⟨91790258224984631822339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 979096087733169406104949 91790258224984631822339)
                ·
                  rfl

theorem cell21_1206636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 2, 5].length) (baseStart_1206636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1206636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1206636 prefixEnd_1206636 := by exact prefixLift 1206636
  have htrace : WordTrace (prefixWord ++ tailWord_1206636) baseStart_1206636 baseEnd_1206636 := by
    simpa [prefixWord, tailWord_1206636, baseEnd_1206636] using wordTrace_append hprefix tailTrace_1206636
  have hstable : (prefixWord ++ tailWord_1206636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206636).length < 2 ^ (prefixWord ++ tailWord_1206636).sum := by decide
  have hdescent : baseEnd_1206636 < baseStart_1206636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206692 : List Nat := [2, 3, 1, 2, 1, 1, 2, 4, 5]
def baseStart_1206692 : Nat := 118140960795 + 1206692 * 2 ^ 59
def prefixEnd_1206692 : Nat := 4983230072969 + 3 ^ 40 * 1206692 * 2
def baseEnd_1206692 : Nat := 275383554637910242533569

theorem tailTrace_1206692 : CollatzResearch.WordTrace tailWord_1206692 prefixEnd_1206692 275383554637910242533569 := by
  unfold tailWord_1206692
  simp only [CollatzResearch.WordTrace]
  refine ⟨22005836472184222715659165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29341115296245630287545553 22005836472184222715659165)
  ·
    refine ⟨8252188677069083518372187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22005836472184222715659165 8252188677069083518372187)
    ·
      refine ⟨12378283015603625277558281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8252188677069083518372187 12378283015603625277558281)
      ·
        refine ⟨9283712261702718958168711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12378283015603625277558281 9283712261702718958168711)
        ·
          refine ⟨13925568392554078437253067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9283712261702718958168711 13925568392554078437253067)
          ·
            refine ⟨20888352588831117655879601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13925568392554078437253067 20888352588831117655879601)
            ·
              refine ⟨15666264441623338241909701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20888352588831117655879601 15666264441623338241909701)
              ·
                refine ⟨2937424582804375920358069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15666264441623338241909701 2937424582804375920358069)
                ·
                  refine ⟨275383554637910242533569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2937424582804375920358069 275383554637910242533569)
                  ·
                    rfl

theorem cell21_1206692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_1206692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1206692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1206692 prefixEnd_1206692 := by exact prefixLift 1206692
  have htrace : WordTrace (prefixWord ++ tailWord_1206692) baseStart_1206692 baseEnd_1206692 := by
    simpa [prefixWord, tailWord_1206692, baseEnd_1206692] using wordTrace_append hprefix tailTrace_1206692
  have hstable : (prefixWord ++ tailWord_1206692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206692).length < 2 ^ (prefixWord ++ tailWord_1206692).sum := by decide
  have hdescent : baseEnd_1206692 < baseStart_1206692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206740 : List Nat := [2, 4, 1, 2, 2, 1, 2, 3, 4]
def baseStart_1206740 : Nat := 118140960795 + 1206740 * 2 ^ 59
def prefixEnd_1206740 : Nat := 4983230072969 + 3 ^ 40 * 1206740 * 2
def baseEnd_1206740 : Nat := 275394508891872825733471

theorem tailTrace_1206740 : CollatzResearch.WordTrace tailWord_1206740 prefixEnd_1206740 275394508891872825733471 := by
  unfold tailWord_1206740
  simp only [CollatzResearch.WordTrace]
  refine ⟨22006711824097274814532837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29342282432129699752710449 22006711824097274814532837)
  ·
    refine ⟨4126258467018239027724907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22006711824097274814532837 4126258467018239027724907)
    ·
      refine ⟨6189387700527358541587361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4126258467018239027724907 6189387700527358541587361)
      ·
        refine ⟨4642040775395518906190521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6189387700527358541587361 4642040775395518906190521)
        ·
          refine ⟨3481530581546639179642891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4642040775395518906190521 3481530581546639179642891)
          ·
            refine ⟨5222295872319958769464337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3481530581546639179642891 5222295872319958769464337)
            ·
              refine ⟨3916721904239969077098253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5222295872319958769464337 3916721904239969077098253)
              ·
                refine ⟨1468770714089988403911845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3916721904239969077098253 1468770714089988403911845)
                ·
                  refine ⟨275394508891872825733471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1468770714089988403911845 275394508891872825733471)
                  ·
                    rfl

theorem cell21_1206740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_1206740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1206740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1206740 prefixEnd_1206740 := by exact prefixLift 1206740
  have htrace : WordTrace (prefixWord ++ tailWord_1206740) baseStart_1206740 baseEnd_1206740 := by
    simpa [prefixWord, tailWord_1206740, baseEnd_1206740] using wordTrace_append hprefix tailTrace_1206740
  have hstable : (prefixWord ++ tailWord_1206740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206740).length < 2 ^ (prefixWord ++ tailWord_1206740).sum := by decide
  have hdescent : baseEnd_1206740 < baseStart_1206740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206785 : List Nat := [1, 2, 4, 1, 3, 2, 2, 1, 5]
def baseStart_1206785 : Nat := 118140960795 + 1206785 * 2 ^ 59
def prefixEnd_1206785 : Nat := 4983230072969 + 3 ^ 40 * 1206785 * 2
def baseEnd_1206785 : Nat := 275404778504962747483379

theorem tailTrace_1206785 : CollatzResearch.WordTrace tailWord_1206785 prefixEnd_1206785 275404778504962747483379 := by
  unfold tailWord_1206785
  simp only [CollatzResearch.WordTrace]
  refine ⟨44015064933031522314453809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29343376622021014876302539 44015064933031522314453809)
  ·
    refine ⟨33011298699773641735840357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44015064933031522314453809 33011298699773641735840357)
    ·
      refine ⟨6189618506207557825470067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33011298699773641735840357 6189618506207557825470067)
      ·
        refine ⟨9284427759311336738205101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6189618506207557825470067 9284427759311336738205101)
        ·
          refine ⟨3481660409741751276826913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9284427759311336738205101 3481660409741751276826913)
          ·
            refine ⟨2611245307306313457620185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3481660409741751276826913 2611245307306313457620185)
            ·
              refine ⟨1958433980479735093215139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2611245307306313457620185 1958433980479735093215139)
              ·
                refine ⟨2937650970719602639822709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1958433980479735093215139 2937650970719602639822709)
                ·
                  refine ⟨275404778504962747483379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2937650970719602639822709 275404778504962747483379)
                  ·
                    rfl

theorem cell21_1206785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 5].length) (baseStart_1206785 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1206785 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1206785 prefixEnd_1206785 := by exact prefixLift 1206785
  have htrace : WordTrace (prefixWord ++ tailWord_1206785) baseStart_1206785 baseEnd_1206785 := by
    simpa [prefixWord, tailWord_1206785, baseEnd_1206785] using wordTrace_append hprefix tailTrace_1206785
  have hstable : (prefixWord ++ tailWord_1206785).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206785).length < 2 ^ (prefixWord ++ tailWord_1206785).sum := by decide
  have hdescent : baseEnd_1206785 < baseStart_1206785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206827 : List Nat := [1, 1, 1, 1, 2, 1, 3, 4, 7]
def baseStart_1206827 : Nat := 118140960795 + 1206827 * 2 ^ 59
def prefixEnd_1206827 : Nat := 4983230072969 + 3 ^ 40 * 1206827 * 2
def baseEnd_1206827 : Nat := 275414363477180007783293

theorem tailTrace_1206827 : CollatzResearch.WordTrace tailWord_1206827 prefixEnd_1206827 275414363477180007783293 := by
  unfold tailWord_1206827
  simp only [CollatzResearch.WordTrace]
  refine ⟨44016596798879363487482735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29344397865919575658321823 44016596798879363487482735)
  ·
    refine ⟨66024895198319045231224103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44016596798879363487482735 66024895198319045231224103)
    ·
      refine ⟨99037342797478567846836155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66024895198319045231224103 99037342797478567846836155)
      ·
        refine ⟨148556014196217851770254233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99037342797478567846836155 148556014196217851770254233)
        ·
          refine ⟨111417010647163388827690675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148556014196217851770254233 111417010647163388827690675)
          ·
            refine ⟨167125515970745083241536013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111417010647163388827690675 167125515970745083241536013)
            ·
              refine ⟨62672068489029406215576005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 167125515970745083241536013 62672068489029406215576005)
              ·
                refine ⟨11751012841693013665420501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62672068489029406215576005 11751012841693013665420501)
                ·
                  refine ⟨275414363477180007783293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11751012841693013665420501 275414363477180007783293)
                  ·
                    rfl

theorem cell21_1206827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 4, 7].length) (baseStart_1206827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1206827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1206827 prefixEnd_1206827 := by exact prefixLift 1206827
  have htrace : WordTrace (prefixWord ++ tailWord_1206827) baseStart_1206827 baseEnd_1206827 := by
    simpa [prefixWord, tailWord_1206827, baseEnd_1206827] using wordTrace_append hprefix tailTrace_1206827
  have hstable : (prefixWord ++ tailWord_1206827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206827).length < 2 ^ (prefixWord ++ tailWord_1206827).sum := by decide
  have hdescent : baseEnd_1206827 < baseStart_1206827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206836 : List Nat := [2, 5, 1, 3, 2, 1, 1, 1, 5]
def baseStart_1206836 : Nat := 118140960795 + 1206836 * 2 ^ 59
def prefixEnd_1206836 : Nat := 4983230072969 + 3 ^ 40 * 1206836 * 2
def baseEnd_1206836 : Nat := 275416417399797992133275

theorem tailTrace_1206836 : CollatzResearch.WordTrace tailWord_1206836 prefixEnd_1206836 275416417399797992133275 := by
  unfold tailWord_1206836
  simp only [CollatzResearch.WordTrace]
  refine ⟨22008462527923379012280181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29344616703897838683040241 22008462527923379012280181)
  ·
    refine ⟨2063293361992816782401267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22008462527923379012280181 2063293361992816782401267)
    ·
      refine ⟨3094940042989225173601901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2063293361992816782401267 3094940042989225173601901)
      ·
        refine ⟨1160602516120959440100713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3094940042989225173601901 1160602516120959440100713)
        ·
          refine ⟨870451887090719580075535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1160602516120959440100713 870451887090719580075535)
          ·
            refine ⟨1305677830636079370113303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 870451887090719580075535 1305677830636079370113303)
            ·
              refine ⟨1958516745954119055169955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305677830636079370113303 1958516745954119055169955)
              ·
                refine ⟨2937775118931178582754933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1958516745954119055169955 2937775118931178582754933)
                ·
                  refine ⟨275416417399797992133275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2937775118931178582754933 275416417399797992133275)
                  ·
                    rfl

theorem cell21_1206836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_1206836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1206836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1206836 prefixEnd_1206836 := by exact prefixLift 1206836
  have htrace : WordTrace (prefixWord ++ tailWord_1206836) baseStart_1206836 baseEnd_1206836 := by
    simpa [prefixWord, tailWord_1206836, baseEnd_1206836] using wordTrace_append hprefix tailTrace_1206836
  have hstable : (prefixWord ++ tailWord_1206836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206836).length < 2 ^ (prefixWord ++ tailWord_1206836).sum := by decide
  have hdescent : baseEnd_1206836 < baseStart_1206836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1206937 : List Nat := [1, 2, 1, 2, 1, 2, 6, 3, 3]
def baseStart_1206937 : Nat := 118140960795 + 1206937 * 2 ^ 59
def prefixEnd_1206937 : Nat := 4983230072969 + 3 ^ 40 * 1206937 * 2
def baseEnd_1206937 : Nat := 275439466975844260949735

theorem tailTrace_1206937 : CollatzResearch.WordTrace tailWord_1206937 prefixEnd_1206937 275439466975844260949735 := by
  unfold tailWord_1206937
  simp only [CollatzResearch.WordTrace]
  refine ⟨44020608828480852273987065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29347072552320568182658043 44020608828480852273987065)
  ·
    refine ⟨33015456621360639205490299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44020608828480852273987065 33015456621360639205490299)
    ·
      refine ⟨49523184932040958808235449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33015456621360639205490299 49523184932040958808235449)
      ·
        refine ⟨37142388699030719106176587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49523184932040958808235449 37142388699030719106176587)
        ·
          refine ⟨55713583048546078659264881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37142388699030719106176587 55713583048546078659264881)
          ·
            refine ⟨41785187286409558994448661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55713583048546078659264881 41785187286409558994448661)
            ·
              refine ⟨1958680654050448077864781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 41785187286409558994448661 1958680654050448077864781)
              ·
                refine ⟨734505245268918029199293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1958680654050448077864781 734505245268918029199293)
                ·
                  refine ⟨275439466975844260949735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 734505245268918029199293 275439466975844260949735)
                  ·
                    rfl

theorem cell21_1206937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 3, 3].length) (baseStart_1206937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1206937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1206937 prefixEnd_1206937 := by exact prefixLift 1206937
  have htrace : WordTrace (prefixWord ++ tailWord_1206937) baseStart_1206937 baseEnd_1206937 := by
    simpa [prefixWord, tailWord_1206937, baseEnd_1206937] using wordTrace_append hprefix tailTrace_1206937
  have hstable : (prefixWord ++ tailWord_1206937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1206937).length < 2 ^ (prefixWord ++ tailWord_1206937).sum := by decide
  have hdescent : baseEnd_1206937 < baseStart_1206937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1206937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207013 : List Nat := [1, 3, 1, 4, 1, 4, 1, 1, 5]
def baseStart_1207013 : Nat := 118140960795 + 1207013 * 2 ^ 59
def prefixEnd_1207013 : Nat := 4983230072969 + 3 ^ 40 * 1207013 * 2
def baseEnd_1207013 : Nat := 275456811211285017682913

theorem tailTrace_1207013 : CollatzResearch.WordTrace tailWord_1207013 prefixEnd_1207013 275456811211285017682913 := by
  unfold tailWord_1207013
  simp only [CollatzResearch.WordTrace]
  refine ⟨44023380776205517253753693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29348920517470344835835795 44023380776205517253753693)
  ·
    refine ⟨16508767791077068970157635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44023380776205517253753693 16508767791077068970157635)
    ·
      refine ⟨24763151686615603455236453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16508767791077068970157635 24763151686615603455236453)
      ·
        refine ⟨4643090941240425647856835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24763151686615603455236453 4643090941240425647856835)
        ·
          refine ⟨6964636411860638471785253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4643090941240425647856835 6964636411860638471785253)
          ·
            refine ⟨1305869327223869713459735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6964636411860638471785253 1305869327223869713459735)
            ·
              refine ⟨1958803990835804570189603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1305869327223869713459735 1958803990835804570189603)
              ·
                refine ⟨2938205986253706855284405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1958803990835804570189603 2938205986253706855284405)
                ·
                  refine ⟨275456811211285017682913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2938205986253706855284405 275456811211285017682913)
                  ·
                    rfl

theorem cell21_1207013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_1207013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1207013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1207013 prefixEnd_1207013 := by exact prefixLift 1207013
  have htrace : WordTrace (prefixWord ++ tailWord_1207013) baseStart_1207013 baseEnd_1207013 := by
    simpa [prefixWord, tailWord_1207013, baseEnd_1207013] using wordTrace_append hprefix tailTrace_1207013
  have hstable : (prefixWord ++ tailWord_1207013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207013).length < 2 ^ (prefixWord ++ tailWord_1207013).sum := by decide
  have hdescent : baseEnd_1207013 < baseStart_1207013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207058 : List Nat := [3, 2, 4, 1, 2, 9]
def baseStart_1207058 : Nat := 118140960795 + 1207058 * 2 ^ 59
def prefixEnd_1207058 : Nat := 4983230072969 + 3 ^ 40 * 1207058 * 2
def baseEnd_1207058 : Nat := 10202484474976849608623

theorem tailTrace_1207058 : CollatzResearch.WordTrace tailWord_1207058 prefixEnd_1207058 10202484474976849608623 := by
  unfold tailWord_1207058
  simp only [CollatzResearch.WordTrace]
  refine ⟨11006255515260622484785457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29350014707361659959427885 11006255515260622484785457)
  ·
    refine ⟨8254691636445466863589093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11006255515260622484785457 8254691636445466863589093)
    ·
      refine ⟨1547754681833525036922955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8254691636445466863589093 1547754681833525036922955)
      ·
        refine ⟨2321632022750287555384433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1547754681833525036922955 2321632022750287555384433)
        ·
          refine ⟨1741224017062715666538325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2321632022750287555384433 1741224017062715666538325)
          ·
            refine ⟨10202484474976849608623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1741224017062715666538325 10202484474976849608623)
            ·
              rfl

theorem cell21_1207058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 9].length) (baseStart_1207058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1207058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1207058 prefixEnd_1207058 := by exact prefixLift 1207058
  have htrace : WordTrace (prefixWord ++ tailWord_1207058) baseStart_1207058 baseEnd_1207058 := by
    simpa [prefixWord, tailWord_1207058, baseEnd_1207058] using wordTrace_append hprefix tailTrace_1207058
  have hstable : (prefixWord ++ tailWord_1207058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207058).length < 2 ^ (prefixWord ++ tailWord_1207058).sum := by decide
  have hdescent : baseEnd_1207058 < baseStart_1207058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207165 : List Nat := [1, 4, 1, 1, 2, 1, 5, 3, 3]
def baseStart_1207165 : Nat := 118140960795 + 1207165 * 2 ^ 59
def prefixEnd_1207165 : Nat := 4983230072969 + 3 ^ 40 * 1207165 * 2
def baseEnd_1207165 : Nat := 275491499682166531149269

theorem tailTrace_1207165 : CollatzResearch.WordTrace tailWord_1207165 prefixEnd_1207165 275491499682166531149269 := by
  unfold tailWord_1207165
  simp only [CollatzResearch.WordTrace]
  refine ⟨44028924671654847213286949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29352616447769898142191299 44028924671654847213286949)
  ·
    refine ⟨8255423375935283852491303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44028924671654847213286949 8255423375935283852491303)
    ·
      refine ⟨12383135063902925778736955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8255423375935283852491303 12383135063902925778736955)
      ·
        refine ⟨18574702595854388668105433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12383135063902925778736955 18574702595854388668105433)
        ·
          refine ⟨13931026946890791501079075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18574702595854388668105433 13931026946890791501079075)
          ·
            refine ⟨20896540420336187251618613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13931026946890791501079075 20896540420336187251618613)
            ·
              refine ⟨1959050664406517554839245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20896540420336187251618613 1959050664406517554839245)
              ·
                refine ⟨734643999152444083064717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1959050664406517554839245 734643999152444083064717)
                ·
                  refine ⟨275491499682166531149269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 734643999152444083064717 275491499682166531149269)
                  ·
                    rfl

theorem cell21_1207165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_1207165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1207165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1207165 prefixEnd_1207165 := by exact prefixLift 1207165
  have htrace : WordTrace (prefixWord ++ tailWord_1207165) baseStart_1207165 baseEnd_1207165 := by
    simpa [prefixWord, tailWord_1207165, baseEnd_1207165] using wordTrace_append hprefix tailTrace_1207165
  have hstable : (prefixWord ++ tailWord_1207165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207165).length < 2 ^ (prefixWord ++ tailWord_1207165).sum := by decide
  have hdescent : baseEnd_1207165 < baseStart_1207165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207196 : List Nat := [2, 2, 3, 3, 2, 1, 1, 3, 4]
def baseStart_1207196 : Nat := 118140960795 + 1207196 * 2 ^ 59
def prefixEnd_1207196 : Nat := 4983230072969 + 3 ^ 40 * 1207196 * 2
def baseEnd_1207196 : Nat := 275498574304517366132539

theorem tailTrace_1207196 : CollatzResearch.WordTrace tailWord_1207196 prefixEnd_1207196 275498574304517366132539 := by
  unfold tailWord_1207196
  simp only [CollatzResearch.WordTrace]
  refine ⟨22015027667271269753832721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29353370223028359671776961 22015027667271269753832721)
  ·
    refine ⟨16511270750453452315374541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22015027667271269753832721 16511270750453452315374541)
    ·
      refine ⟨6191726531420044618265453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16511270750453452315374541 6191726531420044618265453)
      ·
        refine ⟨2321897449282516731849545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6191726531420044618265453 2321897449282516731849545)
        ·
          refine ⟨1741423086961887548887159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2321897449282516731849545 1741423086961887548887159)
          ·
            refine ⟨2612134630442831323330739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1741423086961887548887159 2612134630442831323330739)
            ·
              refine ⟨3918201945664246984996109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2612134630442831323330739 3918201945664246984996109)
              ·
                refine ⟨1469325729624092619373541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3918201945664246984996109 1469325729624092619373541)
                ·
                  refine ⟨275498574304517366132539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1469325729624092619373541 275498574304517366132539)
                  ·
                    rfl

theorem cell21_1207196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_1207196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1207196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1207196 prefixEnd_1207196 := by exact prefixLift 1207196
  have htrace : WordTrace (prefixWord ++ tailWord_1207196) baseStart_1207196 baseEnd_1207196 := by
    simpa [prefixWord, tailWord_1207196, baseEnd_1207196] using wordTrace_append hprefix tailTrace_1207196
  have hstable : (prefixWord ++ tailWord_1207196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207196).length < 2 ^ (prefixWord ++ tailWord_1207196).sum := by decide
  have hdescent : baseEnd_1207196 < baseStart_1207196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207438 : List Nat := [4, 1, 1, 3, 2, 2, 3, 5]
def baseStart_1207438 : Nat := 118140960795 + 1207438 * 2 ^ 59
def prefixEnd_1207438 : Nat := 4983230072969 + 3 ^ 40 * 1207438 * 2
def baseEnd_1207438 : Nat := 91851267333859574366237

theorem tailTrace_1207438 : CollatzResearch.WordTrace tailWord_1207438 prefixEnd_1207438 91851267333859574366237 := by
  unfold tailWord_1207438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5504860224958226854746871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29359254533110543225316645 5504860224958226854746871)
  ·
    refine ⟨8257290337437340282120307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5504860224958226854746871 8257290337437340282120307)
    ·
      refine ⟨12385935506156010423180461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8257290337437340282120307 12385935506156010423180461)
      ·
        refine ⟨4644725814808503908692673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12385935506156010423180461 4644725814808503908692673)
        ·
          refine ⟨3483544361106377931519505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4644725814808503908692673 3483544361106377931519505)
          ·
            refine ⟨2612658270829783448639629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3483544361106377931519505 2612658270829783448639629)
            ·
              refine ⟨979746851561168793239861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2612658270829783448639629 979746851561168793239861)
              ·
                refine ⟨91851267333859574366237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 979746851561168793239861 91851267333859574366237)
                ·
                  rfl

theorem cell21_1207438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_1207438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1207438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1207438 prefixEnd_1207438 := by exact prefixLift 1207438
  have htrace : WordTrace (prefixWord ++ tailWord_1207438) baseStart_1207438 baseEnd_1207438 := by
    simpa [prefixWord, tailWord_1207438, baseEnd_1207438] using wordTrace_append hprefix tailTrace_1207438
  have hstable : (prefixWord ++ tailWord_1207438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207438).length < 2 ^ (prefixWord ++ tailWord_1207438).sum := by decide
  have hdescent : baseEnd_1207438 < baseStart_1207438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207469 : List Nat := [1, 5, 2, 1, 3, 1, 2, 1, 5]
def baseStart_1207469 : Nat := 118140960795 + 1207469 * 2 ^ 59
def prefixEnd_1207469 : Nat := 4983230072969 + 3 ^ 40 * 1207469 * 2
def baseEnd_1207469 : Nat := 275560876623929558081981

theorem tailTrace_1207469 : CollatzResearch.WordTrace tailWord_1207469 prefixEnd_1207469 275560876623929558081981 := by
  unfold tailWord_1207469
  simp only [CollatzResearch.WordTrace]
  refine ⟨44040012462553507132353461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29360008308369004754902307 44040012462553507132353461)
  ·
    refine ⟨4128751168364391293658137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44040012462553507132353461 4128751168364391293658137)
    ·
      refine ⟨3096563376273293470243603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4128751168364391293658137 3096563376273293470243603)
      ·
        refine ⟨4644845064409940205365405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3096563376273293470243603 4644845064409940205365405)
        ·
          refine ⟨1741816899153727577012027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4644845064409940205365405 1741816899153727577012027)
          ·
            refine ⟨2612725348730591365518041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1741816899153727577012027 2612725348730591365518041)
            ·
              refine ⟨1959544011547943524138531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2612725348730591365518041 1959544011547943524138531)
              ·
                refine ⟨2939316017321915286207797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1959544011547943524138531 2939316017321915286207797)
                ·
                  refine ⟨275560876623929558081981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2939316017321915286207797 275560876623929558081981)
                  ·
                    rfl

theorem cell21_1207469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_1207469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1207469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1207469 prefixEnd_1207469 := by exact prefixLift 1207469
  have htrace : WordTrace (prefixWord ++ tailWord_1207469) baseStart_1207469 baseEnd_1207469 := by
    simpa [prefixWord, tailWord_1207469, baseEnd_1207469] using wordTrace_append hprefix tailTrace_1207469
  have hstable : (prefixWord ++ tailWord_1207469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207469).length < 2 ^ (prefixWord ++ tailWord_1207469).sum := by decide
  have hdescent : baseEnd_1207469 < baseStart_1207469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207604 : List Nat := [2, 5, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1207604 : Nat := 118140960795 + 1207604 * 2 ^ 59
def prefixEnd_1207604 : Nat := 4983230072969 + 3 ^ 40 * 1207604 * 2
def baseEnd_1207604 : Nat := 275591685463199323331705

theorem tailTrace_1207604 : CollatzResearch.WordTrace tailWord_1207604 prefixEnd_1207604 275591685463199323331705 := by
  unfold tailWord_1207604
  simp only [CollatzResearch.WordTrace]
  refine ⟨22022468158532212594258933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29363290878042950125678577 22022468158532212594258933)
  ·
    refine ⟨2064606389862394930711775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22022468158532212594258933 2064606389862394930711775)
    ·
      refine ⟨3096909584793592396067663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2064606389862394930711775 3096909584793592396067663)
      ·
        refine ⟨4645364377190388594101495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3096909584793592396067663 4645364377190388594101495)
        ·
          refine ⟨6968046565785582891152243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4645364377190388594101495 6968046565785582891152243)
          ·
            refine ⟨10452069848678374336728365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6968046565785582891152243 10452069848678374336728365)
            ·
              refine ⟨3919526193254390376273137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10452069848678374336728365 3919526193254390376273137)
              ·
                refine ⟨2939644644940792782204853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3919526193254390376273137 2939644644940792782204853)
                ·
                  refine ⟨275591685463199323331705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2939644644940792782204853 275591685463199323331705)
                  ·
                    rfl

theorem cell21_1207604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1207604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1207604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1207604 prefixEnd_1207604 := by exact prefixLift 1207604
  have htrace : WordTrace (prefixWord ++ tailWord_1207604) baseStart_1207604 baseEnd_1207604 := by
    simpa [prefixWord, tailWord_1207604, baseEnd_1207604] using wordTrace_append hprefix tailTrace_1207604
  have hstable : (prefixWord ++ tailWord_1207604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207604).length < 2 ^ (prefixWord ++ tailWord_1207604).sum := by decide
  have hdescent : baseEnd_1207604 < baseStart_1207604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207677 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 8]
def baseStart_1207677 : Nat := 118140960795 + 1207677 * 2 ^ 59
def prefixEnd_1207677 : Nat := 4983230072969 + 3 ^ 40 * 1207677 * 2
def baseEnd_1207677 : Nat := 275608345057767418614889

theorem tailTrace_1207677 : CollatzResearch.WordTrace tailWord_1207677 prefixEnd_1207677 275608345057767418614889 := by
  unfold tailWord_1207677
  simp only [CollatzResearch.WordTrace]
  refine ⟨44047598845799958655925285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29365065897199972437283523 44047598845799958655925285)
  ·
    refine ⟨8258924783587492247985991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44047598845799958655925285 8258924783587492247985991)
    ·
      refine ⟨12388387175381238371978987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8258924783587492247985991 12388387175381238371978987)
      ·
        refine ⟨18582580763071857557968481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12388387175381238371978987 18582580763071857557968481)
        ·
          refine ⟨13936935572303893168476361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18582580763071857557968481 13936935572303893168476361)
          ·
            refine ⟨10452701679227919876357271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13936935572303893168476361 10452701679227919876357271)
            ·
              refine ⟨15679052518841879814535907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10452701679227919876357271 15679052518841879814535907)
              ·
                refine ⟨23518578778262819721803861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15679052518841879814535907 23518578778262819721803861)
                ·
                  refine ⟨275608345057767418614889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23518578778262819721803861 275608345057767418614889)
                  ·
                    rfl

theorem cell21_1207677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_1207677 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1207677 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1207677 prefixEnd_1207677 := by exact prefixLift 1207677
  have htrace : WordTrace (prefixWord ++ tailWord_1207677) baseStart_1207677 baseEnd_1207677 := by
    simpa [prefixWord, tailWord_1207677, baseEnd_1207677] using wordTrace_append hprefix tailTrace_1207677
  have hstable : (prefixWord ++ tailWord_1207677).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207677).length < 2 ^ (prefixWord ++ tailWord_1207677).sum := by decide
  have hdescent : baseEnd_1207677 < baseStart_1207677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207711 : List Nat := [1, 1, 2, 5, 1, 2, 4, 1, 4]
def baseStart_1207711 : Nat := 118140960795 + 1207711 * 2 ^ 59
def prefixEnd_1207711 : Nat := 4983230072969 + 3 ^ 40 * 1207711 * 2
def baseEnd_1207711 : Nat := 275616104320990915048153

theorem tailTrace_1207711 : CollatzResearch.WordTrace tailWord_1207711 prefixEnd_1207711 275616104320990915048153 := by
  unfold tailWord_1207711
  simp only [CollatzResearch.WordTrace]
  refine ⟨44048838927676782462662987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29365892618451188308441991 44048838927676782462662987)
  ·
    refine ⟨66073258391515173693994481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44048838927676782462662987 66073258391515173693994481)
    ·
      refine ⟨49554943793636380270495861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66073258391515173693994481 49554943793636380270495861)
      ·
        refine ⟨4645775980653410650358987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49554943793636380270495861 4645775980653410650358987)
        ·
          refine ⟨6968663970980115975538481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4645775980653410650358987 6968663970980115975538481)
          ·
            refine ⟨5226497978235086981653861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6968663970980115975538481 5226497978235086981653861)
            ·
              refine ⟨979968370919078809060099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5226497978235086981653861 979968370919078809060099)
              ·
                refine ⟨1469952556378618213590149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 979968370919078809060099 1469952556378618213590149)
                ·
                  refine ⟨275616104320990915048153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1469952556378618213590149 275616104320990915048153)
                  ·
                    rfl

theorem cell21_1207711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 4, 1, 4].length) (baseStart_1207711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1207711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1207711 prefixEnd_1207711 := by exact prefixLift 1207711
  have htrace : WordTrace (prefixWord ++ tailWord_1207711) baseStart_1207711 baseEnd_1207711 := by
    simpa [prefixWord, tailWord_1207711, baseEnd_1207711] using wordTrace_append hprefix tailTrace_1207711
  have hstable : (prefixWord ++ tailWord_1207711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207711).length < 2 ^ (prefixWord ++ tailWord_1207711).sum := by decide
  have hdescent : baseEnd_1207711 < baseStart_1207711 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207725 : List Nat := [1, 5, 2, 2, 1, 1, 2, 7]
def baseStart_1207725 : Nat := 118140960795 + 1207725 * 2 ^ 59
def prefixEnd_1207725 : Nat := 4983230072969 + 3 ^ 40 * 1207725 * 2
def baseEnd_1207725 : Nat := 91873099770576667271597

theorem tailTrace_1207725 : CollatzResearch.WordTrace tailWord_1207725 prefixEnd_1207725 91873099770576667271597 := by
  unfold tailWord_1207725
  simp only [CollatzResearch.WordTrace]
  refine ⟨44049349549626062853672629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29366233033084041902448419 44049349549626062853672629)
  ·
    refine ⟨4129626520277443392531809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44049349549626062853672629 4129626520277443392531809)
    ·
      refine ⟨3097219890208082544398857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4129626520277443392531809 3097219890208082544398857)
      ·
        refine ⟨2322914917656061908299143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3097219890208082544398857 2322914917656061908299143)
        ·
          refine ⟨3484372376484092862448715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2322914917656061908299143 3484372376484092862448715)
          ·
            refine ⟨5226558564726139293673073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3484372376484092862448715 5226558564726139293673073)
            ·
              refine ⟨3919918923544604470254805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5226558564726139293673073 3919918923544604470254805)
              ·
                refine ⟨91873099770576667271597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3919918923544604470254805 91873099770576667271597)
                ·
                  rfl

theorem cell21_1207725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 7].length) (baseStart_1207725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1207725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1207725 prefixEnd_1207725 := by exact prefixLift 1207725
  have htrace : WordTrace (prefixWord ++ tailWord_1207725) baseStart_1207725 baseEnd_1207725 := by
    simpa [prefixWord, tailWord_1207725, baseEnd_1207725] using wordTrace_append hprefix tailTrace_1207725
  have hstable : (prefixWord ++ tailWord_1207725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207725).length < 2 ^ (prefixWord ++ tailWord_1207725).sum := by decide
  have hdescent : baseEnd_1207725 < baseStart_1207725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207770 : List Nat := [3, 1, 1, 2, 3, 2, 2, 3, 4]
def baseStart_1207770 : Nat := 118140960795 + 1207770 * 2 ^ 59
def prefixEnd_1207770 : Nat := 4983230072969 + 3 ^ 40 * 1207770 * 2
def baseEnd_1207770 : Nat := 275629568924819923564699

theorem tailTrace_1207770 : CollatzResearch.WordTrace tailWord_1207770 prefixEnd_1207770 275629568924819923564699 := by
  unfold tailWord_1207770
  simp only [CollatzResearch.WordTrace]
  refine ⟨11012747708615758884765191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29367327222975357026040509 11012747708615758884765191)
  ·
    refine ⟨16519121562923638327147787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11012747708615758884765191 16519121562923638327147787)
    ·
      refine ⟨24778682344385457490721681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16519121562923638327147787 24778682344385457490721681)
      ·
        refine ⟨18584011758289093118041261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24778682344385457490721681 18584011758289093118041261)
        ·
          refine ⟨6969004409358409919265473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18584011758289093118041261 6969004409358409919265473)
          ·
            refine ⟨5226753307018807439449105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6969004409358409919265473 5226753307018807439449105)
            ·
              refine ⟨3920064980264105579586829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5226753307018807439449105 3920064980264105579586829)
              ·
                refine ⟨1470024367599039592345061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3920064980264105579586829 1470024367599039592345061)
                ·
                  refine ⟨275629568924819923564699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1470024367599039592345061 275629568924819923564699)
                  ·
                    rfl

theorem cell21_1207770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_1207770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1207770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1207770 prefixEnd_1207770 := by exact prefixLift 1207770
  have htrace : WordTrace (prefixWord ++ tailWord_1207770) baseStart_1207770 baseEnd_1207770 := by
    simpa [prefixWord, tailWord_1207770, baseEnd_1207770] using wordTrace_append hprefix tailTrace_1207770
  have hstable : (prefixWord ++ tailWord_1207770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207770).length < 2 ^ (prefixWord ++ tailWord_1207770).sum := by decide
  have hdescent : baseEnd_1207770 < baseStart_1207770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207815 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 5]
def baseStart_1207815 : Nat := 118140960795 + 1207815 * 2 ^ 59
def prefixEnd_1207815 : Nat := 4983230072969 + 3 ^ 40 * 1207815 * 2
def baseEnd_1207815 : Nat := 275639838537909845314607

theorem tailTrace_1207815 : CollatzResearch.WordTrace tailWord_1207815 prefixEnd_1207815 275639838537909845314607 := by
  unfold tailWord_1207815
  simp only [CollatzResearch.WordTrace]
  refine ⟨44052632119300008224448899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29368421412866672149632599 44052632119300008224448899)
  ·
    refine ⟨66078948178950012336673349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44052632119300008224448899 66078948178950012336673349)
    ·
      refine ⟨12389802783553127313126253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66078948178950012336673349 12389802783553127313126253)
      ·
        refine ⟨4646176043832422742422345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12389802783553127313126253 4646176043832422742422345)
        ·
          refine ⟨3484632032874317056816759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4646176043832422742422345 3484632032874317056816759)
          ·
            refine ⟨5226948049311475585225139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3484632032874317056816759 5226948049311475585225139)
            ·
              refine ⟨7840422073967213377837709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5226948049311475585225139 7840422073967213377837709)
              ·
                refine ⟨2940158277737705016689141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7840422073967213377837709 2940158277737705016689141)
                ·
                  refine ⟨275639838537909845314607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2940158277737705016689141 275639838537909845314607)
                  ·
                    rfl

theorem cell21_1207815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 5].length) (baseStart_1207815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1207815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1207815 prefixEnd_1207815 := by exact prefixLift 1207815
  have htrace : WordTrace (prefixWord ++ tailWord_1207815) baseStart_1207815 baseEnd_1207815 := by
    simpa [prefixWord, tailWord_1207815, baseEnd_1207815] using wordTrace_append hprefix tailTrace_1207815
  have hstable : (prefixWord ++ tailWord_1207815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207815).length < 2 ^ (prefixWord ++ tailWord_1207815).sum := by decide
  have hdescent : baseEnd_1207815 < baseStart_1207815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207922 : List Nat := [3, 2, 1, 2, 3, 1, 1, 4, 4]
def baseStart_1207922 : Nat := 118140960795 + 1207922 * 2 ^ 59
def prefixEnd_1207922 : Nat := 4983230072969 + 3 ^ 40 * 1207922 * 2
def baseEnd_1207922 : Nat := 275664257395701437031055

theorem tailTrace_1207922 : CollatzResearch.WordTrace tailWord_1207922 prefixEnd_1207922 275664257395701437031055 := by
  unfold tailWord_1207922
  simp only [CollatzResearch.WordTrace]
  refine ⟨11014133682478091374648505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29371023153274910332396013 11014133682478091374648505)
  ·
    refine ⟨8260600261858568530986379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11014133682478091374648505 8260600261858568530986379)
    ·
      refine ⟨12390900392787852796479569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8260600261858568530986379 12390900392787852796479569)
      ·
        refine ⟨9293175294590889597359677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12390900392787852796479569 9293175294590889597359677)
        ·
          refine ⟨3484940735471583599009879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9293175294590889597359677 3484940735471583599009879)
          ·
            refine ⟨5227411103207375398514819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3484940735471583599009879 5227411103207375398514819)
            ·
              refine ⟨7841116654811063097772229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5227411103207375398514819 7841116654811063097772229)
              ·
                refine ⟨1470209372777074330832293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7841116654811063097772229 1470209372777074330832293)
                ·
                  refine ⟨275664257395701437031055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1470209372777074330832293 275664257395701437031055)
                  ·
                    rfl

theorem cell21_1207922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_1207922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1207922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1207922 prefixEnd_1207922 := by exact prefixLift 1207922
  have htrace : WordTrace (prefixWord ++ tailWord_1207922) baseStart_1207922 baseEnd_1207922 := by
    simpa [prefixWord, tailWord_1207922, baseEnd_1207922] using wordTrace_append hprefix tailTrace_1207922
  have hstable : (prefixWord ++ tailWord_1207922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207922).length < 2 ^ (prefixWord ++ tailWord_1207922).sum := by decide
  have hdescent : baseEnd_1207922 < baseStart_1207922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1207925 : List Nat := [1, 3, 4, 2, 1, 2, 1, 4, 3]
def baseStart_1207925 : Nat := 118140960795 + 1207925 * 2 ^ 59
def prefixEnd_1207925 : Nat := 4983230072969 + 3 ^ 40 * 1207925 * 2
def baseEnd_1207925 : Nat := 275664942036574098481049

theorem tailTrace_1207925 : CollatzResearch.WordTrace tailWord_1207925 prefixEnd_1207925 275664942036574098481049 := by
  unfold tailWord_1207925
  simp only [CollatzResearch.WordTrace]
  refine ⟨44056644148901497010953229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29371096099267664673968819 44056644148901497010953229)
  ·
    refine ⟨16521241555838061379107461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44056644148901497010953229 16521241555838061379107461)
    ·
      refine ⟨3097732791719636508582649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16521241555838061379107461 3097732791719636508582649)
      ·
        refine ⟨2323299593789727381436987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3097732791719636508582649 2323299593789727381436987)
        ·
          refine ⟨3484949390684591072155481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2323299593789727381436987 3484949390684591072155481)
          ·
            refine ⟨2613712043013443304116611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3484949390684591072155481 2613712043013443304116611)
            ·
              refine ⟨3920568064520164956174917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2613712043013443304116611 3920568064520164956174917)
              ·
                refine ⟨735106512097530929282797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3920568064520164956174917 735106512097530929282797)
                ·
                  refine ⟨275664942036574098481049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 735106512097530929282797 275664942036574098481049)
                  ·
                    rfl

theorem cell21_1207925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 4, 3].length) (baseStart_1207925 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1207925 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1207925 prefixEnd_1207925 := by exact prefixLift 1207925
  have htrace : WordTrace (prefixWord ++ tailWord_1207925) baseStart_1207925 baseEnd_1207925 := by
    simpa [prefixWord, tailWord_1207925, baseEnd_1207925] using wordTrace_append hprefix tailTrace_1207925
  have hstable : (prefixWord ++ tailWord_1207925).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1207925).length < 2 ^ (prefixWord ++ tailWord_1207925).sum := by decide
  have hdescent : baseEnd_1207925 < baseStart_1207925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1207925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208043 : List Nat := [1, 1, 1, 1, 2, 4, 2, 6, 3]
def baseStart_1208043 : Nat := 118140960795 + 1208043 * 2 ^ 59
def prefixEnd_1208043 : Nat := 4983230072969 + 3 ^ 40 * 1208043 * 2
def baseEnd_1208043 : Nat := 275691871244232115514141

theorem tailTrace_1208043 : CollatzResearch.WordTrace tailWord_1208043 prefixEnd_1208043 275691871244232115514141 := by
  unfold tailWord_1208043
  simp only [CollatzResearch.WordTrace]
  refine ⟨44060947962474003163748783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29373965308316002109165855 44060947962474003163748783)
  ·
    refine ⟨66091421943711004745623175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44060947962474003163748783 66091421943711004745623175)
    ·
      refine ⟨99137132915566507118434763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66091421943711004745623175 99137132915566507118434763)
      ·
        refine ⟨148705699373349760677652145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99137132915566507118434763 148705699373349760677652145)
        ·
          refine ⟨111529274530012320508239109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 148705699373349760677652145 111529274530012320508239109)
          ·
            refine ⟨20911738974377310095294833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 111529274530012320508239109 20911738974377310095294833)
            ·
              refine ⟨15683804230782982571471125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20911738974377310095294833 15683804230782982571471125)
              ·
                refine ⟨735178323317952308037709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15683804230782982571471125 735178323317952308037709)
                ·
                  refine ⟨275691871244232115514141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 735178323317952308037709 275691871244232115514141)
                  ·
                    rfl

theorem cell21_1208043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 6, 3].length) (baseStart_1208043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1208043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1208043 prefixEnd_1208043 := by exact prefixLift 1208043
  have htrace : WordTrace (prefixWord ++ tailWord_1208043) baseStart_1208043 baseEnd_1208043 := by
    simpa [prefixWord, tailWord_1208043, baseEnd_1208043] using wordTrace_append hprefix tailTrace_1208043
  have hstable : (prefixWord ++ tailWord_1208043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208043).length < 2 ^ (prefixWord ++ tailWord_1208043).sum := by decide
  have hdescent : baseEnd_1208043 < baseStart_1208043 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208136 : List Nat := [2, 1, 3, 1, 1, 5, 2, 3, 3]
def baseStart_1208136 : Nat := 118140960795 + 1208136 * 2 ^ 59
def prefixEnd_1208136 : Nat := 4983230072969 + 3 ^ 40 * 1208136 * 2
def baseEnd_1208136 : Nat := 275713095111284620463951

theorem tailTrace_1208136 : CollatzResearch.WordTrace tailWord_1208136 prefixEnd_1208136 275713095111284620463951 := by
  unfold tailWord_1208136
  simp only [CollatzResearch.WordTrace]
  refine ⟨22032169975568540023442131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29376226634091386697922841 22032169975568540023442131)
  ·
    refine ⟨33048254963352810035163197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22032169975568540023442131 33048254963352810035163197)
    ·
      refine ⟨12393095611257303763186199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33048254963352810035163197 12393095611257303763186199)
      ·
        refine ⟨18589643416885955644779299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12393095611257303763186199 18589643416885955644779299)
        ·
          refine ⟨27884465125328933467168949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18589643416885955644779299 27884465125328933467168949)
          ·
            refine ⟨2614168605499587512547089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27884465125328933467168949 2614168605499587512547089)
            ·
              refine ⟨1960626454124690634410317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2614168605499587512547089 1960626454124690634410317)
              ·
                refine ⟨735234920296758987903869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1960626454124690634410317 735234920296758987903869)
                ·
                  refine ⟨275713095111284620463951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 735234920296758987903869 275713095111284620463951)
                  ·
                    rfl

theorem cell21_1208136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 3, 3].length) (baseStart_1208136 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1208136 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1208136 prefixEnd_1208136 := by exact prefixLift 1208136
  have htrace : WordTrace (prefixWord ++ tailWord_1208136) baseStart_1208136 baseEnd_1208136 := by
    simpa [prefixWord, tailWord_1208136, baseEnd_1208136] using wordTrace_append hprefix tailTrace_1208136
  have hstable : (prefixWord ++ tailWord_1208136).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208136).length < 2 ^ (prefixWord ++ tailWord_1208136).sum := by decide
  have hdescent : baseEnd_1208136 < baseStart_1208136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208192 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 8]
def baseStart_1208192 : Nat := 118140960795 + 1208192 * 2 ^ 59
def prefixEnd_1208192 : Nat := 4983230072969 + 3 ^ 40 * 1208192 * 2
def baseEnd_1208192 : Nat := 275725875074240967530503

theorem tailTrace_1208192 : CollatzResearch.WordTrace tailWord_1208192 prefixEnd_1208192 275725875074240967530503 := by
  unfold tailWord_1208192
  simp only [CollatzResearch.WordTrace]
  refine ⟨22033191219467100805461415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29377588292622801073948553 22033191219467100805461415)
  ·
    refine ⟨33049786829200651208192123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22033191219467100805461415 33049786829200651208192123)
    ·
      refine ⟨49574680243800976812288185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33049786829200651208192123 49574680243800976812288185)
      ·
        refine ⟨37181010182850732609216139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49574680243800976812288185 37181010182850732609216139)
        ·
          refine ⟨55771515274276098913824209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37181010182850732609216139 55771515274276098913824209)
          ·
            refine ⟨41828636455707074185368157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55771515274276098913824209 41828636455707074185368157)
            ·
              refine ⟨15685738670890152819513059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41828636455707074185368157 15685738670890152819513059)
              ·
                refine ⟨23528608006335229229269589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15685738670890152819513059 23528608006335229229269589)
                ·
                  refine ⟨275725875074240967530503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23528608006335229229269589 275725875074240967530503)
                  ·
                    rfl

theorem cell21_1208192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_1208192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1208192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1208192 prefixEnd_1208192 := by exact prefixLift 1208192
  have htrace : WordTrace (prefixWord ++ tailWord_1208192) baseStart_1208192 baseEnd_1208192 := by
    simpa [prefixWord, tailWord_1208192, baseEnd_1208192] using wordTrace_append hprefix tailTrace_1208192
  have hstable : (prefixWord ++ tailWord_1208192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208192).length < 2 ^ (prefixWord ++ tailWord_1208192).sum := by decide
  have hdescent : baseEnd_1208192 < baseStart_1208192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208212 : List Nat := [2, 4, 2, 1, 1, 4, 1, 1, 5]
def baseStart_1208212 : Nat := 118140960795 + 1208212 * 2 ^ 59
def prefixEnd_1208212 : Nat := 4983230072969 + 3 ^ 40 * 1208212 * 2
def baseEnd_1208212 : Nat := 275730439346725377197129

theorem tailTrace_1208212 : CollatzResearch.WordTrace tailWord_1208212 prefixEnd_1208212 275730439346725377197129 := by
  unfold tailWord_1208212
  simp only [CollatzResearch.WordTrace]
  refine ⟨22033555949430872513325445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29378074599241163351100593 22033555949430872513325445)
  ·
    refine ⟨4131291740518288596248521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22033555949430872513325445 4131291740518288596248521)
    ·
      refine ⟨3098468805388716447186391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4131291740518288596248521 3098468805388716447186391)
      ·
        refine ⟨4647703208083074670779587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3098468805388716447186391 4647703208083074670779587)
        ·
          refine ⟨6971554812124612006169381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4647703208083074670779587 6971554812124612006169381)
          ·
            refine ⟨1307166527273364751156759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6971554812124612006169381 1307166527273364751156759)
            ·
              refine ⟨1960749790910047126735139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307166527273364751156759 1960749790910047126735139)
              ·
                refine ⟨2941124686365070690102709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1960749790910047126735139 2941124686365070690102709)
                ·
                  refine ⟨275730439346725377197129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2941124686365070690102709 275730439346725377197129)
                  ·
                    rfl

theorem cell21_1208212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_1208212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1208212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1208212 prefixEnd_1208212 := by exact prefixLift 1208212
  have htrace : WordTrace (prefixWord ++ tailWord_1208212) baseStart_1208212 baseEnd_1208212 := by
    simpa [prefixWord, tailWord_1208212, baseEnd_1208212] using wordTrace_append hprefix tailTrace_1208212
  have hstable : (prefixWord ++ tailWord_1208212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208212).length < 2 ^ (prefixWord ++ tailWord_1208212).sum := by decide
  have hdescent : baseEnd_1208212 < baseStart_1208212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208271 : List Nat := [1, 1, 2, 1, 1, 5, 3, 4, 3]
def baseStart_1208271 : Nat := 118140960795 + 1208271 * 2 ^ 59
def prefixEnd_1208271 : Nat := 4983230072969 + 3 ^ 40 * 1208271 * 2
def baseEnd_1208271 : Nat := 275743903950554385713675

theorem tailTrace_1208271 : CollatzResearch.WordTrace tailWord_1208271 prefixEnd_1208271 275743903950554385713675 := by
  unfold tailWord_1208271
  simp only [CollatzResearch.WordTrace]
  refine ⟨44069263805647998103048667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29379509203765332068699111 44069263805647998103048667)
  ·
    refine ⟨66103895708471997154573001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44069263805647998103048667 66103895708471997154573001)
    ·
      refine ⟨49577921781353997865929751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66103895708471997154573001 49577921781353997865929751)
      ·
        refine ⟨74366882672030996798894627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49577921781353997865929751 74366882672030996798894627)
        ·
          refine ⟨111550324008046495198341941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74366882672030996798894627 111550324008046495198341941)
          ·
            refine ⟨10457842875754358924844557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 111550324008046495198341941 10457842875754358924844557)
            ·
              refine ⟨3921691078407884596816709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10457842875754358924844557 3921691078407884596816709)
              ·
                refine ⟨735317077201478361903133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3921691078407884596816709 735317077201478361903133)
                ·
                  refine ⟨275743903950554385713675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 735317077201478361903133 275743903950554385713675)
                  ·
                    rfl

theorem cell21_1208271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 3, 4, 3].length) (baseStart_1208271 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1208271 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1208271 prefixEnd_1208271 := by exact prefixLift 1208271
  have htrace : WordTrace (prefixWord ++ tailWord_1208271) baseStart_1208271 baseEnd_1208271 := by
    simpa [prefixWord, tailWord_1208271, baseEnd_1208271] using wordTrace_append hprefix tailTrace_1208271
  have hstable : (prefixWord ++ tailWord_1208271).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208271).length < 2 ^ (prefixWord ++ tailWord_1208271).sum := by decide
  have hdescent : baseEnd_1208271 < baseStart_1208271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208274 : List Nat := [3, 2, 2, 3, 3, 1, 1, 6]
def baseStart_1208274 : Nat := 118140960795 + 1208274 * 2 ^ 59
def prefixEnd_1208274 : Nat := 4983230072969 + 3 ^ 40 * 1208274 * 2
def baseEnd_1208274 : Nat := 91914862863809015721223

theorem tailTrace_1208274 : CollatzResearch.WordTrace tailWord_1208274 prefixEnd_1208274 91914862863809015721223 := by
  unfold tailWord_1208274
  simp only [CollatzResearch.WordTrace]
  refine ⟨11017343306159282403851969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29379582149758086410271917 11017343306159282403851969)
  ·
    refine ⟨8263007479619461802888977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11017343306159282403851969 8263007479619461802888977)
    ·
      refine ⟨6197255609714596352166733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8263007479619461802888977 6197255609714596352166733)
      ·
        refine ⟨2323970853642973632062525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6197255609714596352166733 2323970853642973632062525)
        ·
          refine ⟨871489070116115112023447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2323970853642973632062525 871489070116115112023447)
          ·
            refine ⟨1307233605174172668035171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 871489070116115112023447 1307233605174172668035171)
            ·
              refine ⟨1960850407761259002052757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307233605174172668035171 1960850407761259002052757)
              ·
                refine ⟨91914862863809015721223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1960850407761259002052757 91914862863809015721223)
                ·
                  rfl

theorem cell21_1208274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 6].length) (baseStart_1208274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1208274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1208274 prefixEnd_1208274 := by exact prefixLift 1208274
  have htrace : WordTrace (prefixWord ++ tailWord_1208274) baseStart_1208274 baseEnd_1208274 := by
    simpa [prefixWord, tailWord_1208274, baseEnd_1208274] using wordTrace_append hprefix tailTrace_1208274
  have hstable : (prefixWord ++ tailWord_1208274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208274).length < 2 ^ (prefixWord ++ tailWord_1208274).sum := by decide
  have hdescent : baseEnd_1208274 < baseStart_1208274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208420 : List Nat := [2, 3, 1, 1, 2, 1, 2, 1, 8]
def baseStart_1208420 : Nat := 118140960795 + 1208420 * 2 ^ 59
def prefixEnd_1208420 : Nat := 4983230072969 + 3 ^ 40 * 1208420 * 2
def baseEnd_1208420 : Nat := 275777907780563237730037

theorem tailTrace_1208420 : CollatzResearch.WordTrace tailWord_1208420 prefixEnd_1208420 275777907780563237730037 := by
  unfold tailWord_1208420
  simp only [CollatzResearch.WordTrace]
  refine ⟨22037349141054098275111357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29383132188072131033481809 22037349141054098275111357)
  ·
    refine ⟨8264005927895286853166759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22037349141054098275111357 8264005927895286853166759)
    ·
      refine ⟨12396008891842930279750139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8264005927895286853166759 12396008891842930279750139)
      ·
        refine ⟨18594013337764395419625209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12396008891842930279750139 18594013337764395419625209)
        ·
          refine ⟨13945510003323296564718907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18594013337764395419625209 13945510003323296564718907)
          ·
            refine ⟨20918265004984944847078361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13945510003323296564718907 20918265004984944847078361)
            ·
              refine ⟨15688698753738708635308771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20918265004984944847078361 15688698753738708635308771)
              ·
                refine ⟨23533048130608062952963157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15688698753738708635308771 23533048130608062952963157)
                ·
                  refine ⟨275777907780563237730037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23533048130608062952963157 275777907780563237730037)
                  ·
                    rfl

theorem cell21_1208420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_1208420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1208420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1208420 prefixEnd_1208420 := by exact prefixLift 1208420
  have htrace : WordTrace (prefixWord ++ tailWord_1208420) baseStart_1208420 baseEnd_1208420 := by
    simpa [prefixWord, tailWord_1208420, baseEnd_1208420] using wordTrace_append hprefix tailTrace_1208420
  have hstable : (prefixWord ++ tailWord_1208420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208420).length < 2 ^ (prefixWord ++ tailWord_1208420).sum := by decide
  have hdescent : baseEnd_1208420 < baseStart_1208420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208423 : List Nat := [1, 1, 5, 1, 1, 2, 2, 5, 3]
def baseStart_1208423 : Nat := 118140960795 + 1208423 * 2 ^ 59
def prefixEnd_1208423 : Nat := 4983230072969 + 3 ^ 40 * 1208423 * 2
def baseEnd_1208423 : Nat := 275778592421435899180031

theorem tailTrace_1208423 : CollatzResearch.WordTrace tailWord_1208423 prefixEnd_1208423 275778592421435899180031 := by
  unfold tailWord_1208423
  simp only [CollatzResearch.WordTrace]
  refine ⟨44074807701097328062581923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29383205134064885375054615 44074807701097328062581923)
  ·
    refine ⟨66112211551645992093872885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44074807701097328062581923 66112211551645992093872885)
    ·
      refine ⟨6198019832966811758800583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66112211551645992093872885 6198019832966811758800583)
      ·
        refine ⟨9297029749450217638200875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6198019832966811758800583 9297029749450217638200875)
        ·
          refine ⟨13945544624175326457301313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9297029749450217638200875 13945544624175326457301313)
          ·
            refine ⟨10459158468131494842975985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13945544624175326457301313 10459158468131494842975985)
            ·
              refine ⟨7844368851098621132231989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10459158468131494842975985 7844368851098621132231989)
              ·
                refine ⟨735409579790495731146749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7844368851098621132231989 735409579790495731146749)
                ·
                  refine ⟨275778592421435899180031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 735409579790495731146749 275778592421435899180031)
                  ·
                    rfl

theorem cell21_1208423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 5, 3].length) (baseStart_1208423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1208423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1208423 prefixEnd_1208423 := by exact prefixLift 1208423
  have htrace : WordTrace (prefixWord ++ tailWord_1208423) baseStart_1208423 baseEnd_1208423 := by
    simpa [prefixWord, tailWord_1208423, baseEnd_1208423] using wordTrace_append hprefix tailTrace_1208423
  have hstable : (prefixWord ++ tailWord_1208423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208423).length < 2 ^ (prefixWord ++ tailWord_1208423).sum := by decide
  have hdescent : baseEnd_1208423 < baseStart_1208423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208451 : List Nat := [1, 1, 1, 3, 3, 3, 3, 6]
def baseStart_1208451 : Nat := 118140960795 + 1208451 * 2 ^ 59
def prefixEnd_1208451 : Nat := 4983230072969 + 3 ^ 40 * 1208451 * 2
def baseEnd_1208451 : Nat := 91928327467638024237769

theorem tailTrace_1208451 : CollatzResearch.WordTrace tailWord_1208451 prefixEnd_1208451 91928327467638024237769 := by
  unfold tailWord_1208451
  simp only [CollatzResearch.WordTrace]
  refine ⟨44075828944995888844601207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29383885963330592563067471 44075828944995888844601207)
  ·
    refine ⟨66113743417493833266901811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44075828944995888844601207 66113743417493833266901811)
    ·
      refine ⟨99170615126240749900352717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66113743417493833266901811 99170615126240749900352717)
      ·
        refine ⟨37188980672340281212632269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99170615126240749900352717 37188980672340281212632269)
        ·
          refine ⟨13945867752127605454737101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37188980672340281212632269 13945867752127605454737101)
          ·
            refine ⟨5229700407047852045526413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13945867752127605454737101 5229700407047852045526413)
            ·
              refine ⟨1961137652642944517072405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5229700407047852045526413 1961137652642944517072405)
              ·
                refine ⟨91928327467638024237769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1961137652642944517072405 91928327467638024237769)
                ·
                  rfl

theorem cell21_1208451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 3, 6].length) (baseStart_1208451 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1208451 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1208451 prefixEnd_1208451 := by exact prefixLift 1208451
  have htrace : WordTrace (prefixWord ++ tailWord_1208451) baseStart_1208451 baseEnd_1208451 := by
    simpa [prefixWord, tailWord_1208451, baseEnd_1208451] using wordTrace_append hprefix tailTrace_1208451
  have hstable : (prefixWord ++ tailWord_1208451).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208451).length < 2 ^ (prefixWord ++ tailWord_1208451).sum := by decide
  have hdescent : baseEnd_1208451 < baseStart_1208451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208533 : List Nat := [1, 3, 2, 4, 2, 2, 1, 3, 3]
def baseStart_1208533 : Nat := 118140960795 + 1208533 * 2 ^ 59
def prefixEnd_1208533 : Nat := 4983230072969 + 3 ^ 40 * 1208533 * 2
def baseEnd_1208533 : Nat := 275803695920100152346473

theorem tailTrace_1208533 : CollatzResearch.WordTrace tailWord_1208533 prefixEnd_1208533 275803695920100152346473 := by
  unfold tailWord_1208533
  simp only [CollatzResearch.WordTrace]
  refine ⟨44078819730698816849086253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29385879820465877899390835 44078819730698816849086253)
  ·
    refine ⟨16529557399012056318407345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44078819730698816849086253 16529557399012056318407345)
    ·
      refine ⟨12397168049259042238805509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16529557399012056318407345 12397168049259042238805509)
      ·
        refine ⟨2324469009236070419776033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12397168049259042238805509 2324469009236070419776033)
        ·
          refine ⟨1743351756927052814832025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2324469009236070419776033 1743351756927052814832025)
          ·
            refine ⟨1307513817695289611124019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1743351756927052814832025 1307513817695289611124019)
            ·
              refine ⟨1961270726542934416686029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1307513817695289611124019 1961270726542934416686029)
              ·
                refine ⟨735476522453600406257261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1961270726542934416686029 735476522453600406257261)
                ·
                  refine ⟨275803695920100152346473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 735476522453600406257261 275803695920100152346473)
                  ·
                    rfl

theorem cell21_1208533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3, 3].length) (baseStart_1208533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1208533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1208533 prefixEnd_1208533 := by exact prefixLift 1208533
  have htrace : WordTrace (prefixWord ++ tailWord_1208533) baseStart_1208533 baseEnd_1208533 := by
    simpa [prefixWord, tailWord_1208533, baseEnd_1208533] using wordTrace_append hprefix tailTrace_1208533
  have hstable : (prefixWord ++ tailWord_1208533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208533).length < 2 ^ (prefixWord ++ tailWord_1208533).sum := by decide
  have hdescent : baseEnd_1208533 < baseStart_1208533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208634 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 5]
def baseStart_1208634 : Nat := 118140960795 + 1208634 * 2 ^ 59
def prefixEnd_1208634 : Nat := 4983230072969 + 3 ^ 40 * 1208634 * 2
def baseEnd_1208634 : Nat := 275826745496146421162933

theorem tailTrace_1208634 : CollatzResearch.WordTrace tailWord_1208634 prefixEnd_1208634 275826745496146421162933 := by
  unfold tailWord_1208634
  simp only [CollatzResearch.WordTrace]
  refine ⟨11020625875833227774628239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29388335668888607399008637 11020625875833227774628239)
  ·
    refine ⟨16530938813749841661942359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11020625875833227774628239 16530938813749841661942359)
    ·
      refine ⟨24796408220624762492913539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16530938813749841661942359 24796408220624762492913539)
      ·
        refine ⟨37194612330937143739370309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24796408220624762492913539 37194612330937143739370309)
        ·
          refine ⟨6973989812050714451131933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37194612330937143739370309 6973989812050714451131933)
          ·
            refine ⟨2615246179519017919174475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6973989812050714451131933 2615246179519017919174475)
            ·
              refine ⟨3922869269278526878761713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2615246179519017919174475 3922869269278526878761713)
              ·
                refine ⟨2942151951958895159071285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3922869269278526878761713 2942151951958895159071285)
                ·
                  refine ⟨275826745496146421162933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2942151951958895159071285 275826745496146421162933)
                  ·
                    rfl

theorem cell21_1208634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_1208634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1208634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1208634 prefixEnd_1208634 := by exact prefixLift 1208634
  have htrace : WordTrace (prefixWord ++ tailWord_1208634) baseStart_1208634 baseEnd_1208634 := by
    simpa [prefixWord, tailWord_1208634, baseEnd_1208634] using wordTrace_append hprefix tailTrace_1208634
  have hstable : (prefixWord ++ tailWord_1208634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208634).length < 2 ^ (prefixWord ++ tailWord_1208634).sum := by decide
  have hdescent : baseEnd_1208634 < baseStart_1208634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208668 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 5]
def baseStart_1208668 : Nat := 118140960795 + 1208668 * 2 ^ 59
def prefixEnd_1208668 : Nat := 4983230072969 + 3 ^ 40 * 1208668 * 2
def baseEnd_1208668 : Nat := 275834504759369917596197

theorem tailTrace_1208668 : CollatzResearch.WordTrace tailWord_1208668 prefixEnd_1208668 275834504759369917596197 := by
  unfold tailWord_1208668
  simp only [CollatzResearch.WordTrace]
  refine ⟨22041871792604867452625329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29389162390139823270167105 22041871792604867452625329)
  ·
    refine ⟨16531403844453650589468997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22041871792604867452625329 16531403844453650589468997)
    ·
      refine ⟨3099638220835059485525437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16531403844453650589468997 3099638220835059485525437)
      ·
        refine ⟨1162364332813147307072039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3099638220835059485525437 1162364332813147307072039)
        ·
          refine ⟨1743546499219720960608059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1162364332813147307072039 1743546499219720960608059)
          ·
            refine ⟨2615319748829581440912089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1743546499219720960608059 2615319748829581440912089)
            ·
              refine ⟨1961489811622186080684067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2615319748829581440912089 1961489811622186080684067)
              ·
                refine ⟨2942234717433279121026101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1961489811622186080684067 2942234717433279121026101)
                ·
                  refine ⟨275834504759369917596197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2942234717433279121026101 275834504759369917596197)
                  ·
                    rfl

theorem cell21_1208668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 5].length) (baseStart_1208668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1208668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1208668 prefixEnd_1208668 := by exact prefixLift 1208668
  have htrace : WordTrace (prefixWord ++ tailWord_1208668) baseStart_1208668 baseEnd_1208668 := by
    simpa [prefixWord, tailWord_1208668, baseEnd_1208668] using wordTrace_append hprefix tailTrace_1208668
  have hstable : (prefixWord ++ tailWord_1208668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208668).length < 2 ^ (prefixWord ++ tailWord_1208668).sum := by decide
  have hdescent : baseEnd_1208668 < baseStart_1208668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208772 : List Nat := [2, 3, 3, 2, 3, 8]
def baseStart_1208772 : Nat := 118140960795 + 1208772 * 2 ^ 59
def prefixEnd_1208772 : Nat := 4983230072969 + 3 ^ 40 * 1208772 * 2
def baseEnd_1208772 : Nat := 10216971813936623994913

theorem tailTrace_1208772 : CollatzResearch.WordTrace tailWord_1208772 prefixEnd_1208772 10216971813936623994913 := by
  unfold tailWord_1208772
  simp only [CollatzResearch.WordTrace]
  refine ⟨22043768388416480333518285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29391691184555307111357713 22043768388416480333518285)
  ·
    refine ⟨8266413145656180125069357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22043768388416480333518285 8266413145656180125069357)
    ·
      refine ⟨3099904929621067546901009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8266413145656180125069357 3099904929621067546901009)
      ·
        refine ⟨2324928697215800660175757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3099904929621067546901009 2324928697215800660175757)
        ·
          refine ⟨871848261455925247565909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2324928697215800660175757 871848261455925247565909)
          ·
            refine ⟨10216971813936623994913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 871848261455925247565909 10216971813936623994913)
            ·
              rfl

theorem cell21_1208772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 8].length) (baseStart_1208772 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1208772 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1208772 prefixEnd_1208772 := by exact prefixLift 1208772
  have htrace : WordTrace (prefixWord ++ tailWord_1208772) baseStart_1208772 baseEnd_1208772 := by
    simpa [prefixWord, tailWord_1208772, baseEnd_1208772] using wordTrace_append hprefix tailTrace_1208772
  have hstable : (prefixWord ++ tailWord_1208772).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208772).length < 2 ^ (prefixWord ++ tailWord_1208772).sum := by decide
  have hdescent : baseEnd_1208772 < baseStart_1208772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208800 : List Nat := [2, 1, 1, 3, 1, 1, 3, 5, 4]
def baseStart_1208800 : Nat := 118140960795 + 1208800 * 2 ^ 59
def prefixEnd_1208800 : Nat := 4983230072969 + 3 ^ 40 * 1208800 * 2
def baseEnd_1208800 : Nat := 275864628957767021395927

theorem tailTrace_1208800 : CollatzResearch.WordTrace tailWord_1208800 prefixEnd_1208800 275864628957767021395927 := by
  unfold tailWord_1208800
  simp only [CollatzResearch.WordTrace]
  refine ⟨22044279010365760724527927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29392372013821014299370569 22044279010365760724527927)
  ·
    refine ⟨33066418515548641086791891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22044279010365760724527927 33066418515548641086791891)
    ·
      refine ⟨49599627773322961630187837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33066418515548641086791891 49599627773322961630187837)
      ·
        refine ⟨18599860414996110611320439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49599627773322961630187837 18599860414996110611320439)
        ·
          refine ⟨27899790622494165916980659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18599860414996110611320439 27899790622494165916980659)
          ·
            refine ⟨41849685933741248875470989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27899790622494165916980659 41849685933741248875470989)
            ·
              refine ⟨15693632225152968328301621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41849685933741248875470989 15693632225152968328301621)
              ·
                refine ⟨1471278021108090780778277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15693632225152968328301621 1471278021108090780778277)
                ·
                  refine ⟨275864628957767021395927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1471278021108090780778277 275864628957767021395927)
                  ·
                    rfl

theorem cell21_1208800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_1208800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1208800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1208800 prefixEnd_1208800 := by exact prefixLift 1208800
  have htrace : WordTrace (prefixWord ++ tailWord_1208800) baseStart_1208800 baseEnd_1208800 := by
    simpa [prefixWord, tailWord_1208800, baseEnd_1208800] using wordTrace_append hprefix tailTrace_1208800
  have hstable : (prefixWord ++ tailWord_1208800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208800).length < 2 ^ (prefixWord ++ tailWord_1208800).sum := by decide
  have hdescent : baseEnd_1208800 < baseStart_1208800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208834 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 6]
def baseStart_1208834 : Nat := 118140960795 + 1208834 * 2 ^ 59
def prefixEnd_1208834 : Nat := 4983230072969 + 3 ^ 40 * 1208834 * 2
def baseEnd_1208834 : Nat := 275872388220990517829191

theorem tailTrace_1208834 : CollatzResearch.WordTrace tailWord_1208834 prefixEnd_1208834 275872388220990517829191 := by
  unfold tailWord_1208834
  simp only [CollatzResearch.WordTrace]
  refine ⟨11022449525652086313948389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29393198735072230170529037 11022449525652086313948389)
  ·
    refine ⟨2066709286059766183865323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11022449525652086313948389 2066709286059766183865323)
    ·
      refine ⟨3100063929089649275797985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2066709286059766183865323 3100063929089649275797985)
      ·
        refine ⟨2325047946817236956848489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3100063929089649275797985 2325047946817236956848489)
        ·
          refine ⟨1743785960112927717636367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2325047946817236956848489 1743785960112927717636367)
          ·
            refine ⟨2615678940169391576454551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1743785960112927717636367 2615678940169391576454551)
            ·
              refine ⟨3923518410254087364681827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2615678940169391576454551 3923518410254087364681827)
              ·
                refine ⟨5885277615381131047022741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3923518410254087364681827 5885277615381131047022741)
                ·
                  refine ⟨275872388220990517829191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5885277615381131047022741 275872388220990517829191)
                  ·
                    rfl

theorem cell21_1208834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_1208834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1208834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1208834 prefixEnd_1208834 := by exact prefixLift 1208834
  have htrace : WordTrace (prefixWord ++ tailWord_1208834) baseStart_1208834 baseEnd_1208834 := by
    simpa [prefixWord, tailWord_1208834, baseEnd_1208834] using wordTrace_append hprefix tailTrace_1208834
  have hstable : (prefixWord ++ tailWord_1208834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208834).length < 2 ^ (prefixWord ++ tailWord_1208834).sum := by decide
  have hdescent : baseEnd_1208834 < baseStart_1208834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208890 : List Nat := [3, 1, 1, 1, 3, 3, 9]
def baseStart_1208890 : Nat := 118140960795 + 1208890 * 2 ^ 59
def prefixEnd_1208890 : Nat := 4983230072969 + 3 ^ 40 * 1208890 * 2
def baseEnd_1208890 : Nat := 30653907575994096099527

theorem tailTrace_1208890 : CollatzResearch.WordTrace tailWord_1208890 prefixEnd_1208890 30653907575994096099527 := by
  unfold tailWord_1208890
  simp only [CollatzResearch.WordTrace]
  refine ⟨11022960147601366704958031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29394560393603644546554749 11022960147601366704958031)
  ·
    refine ⟨16534440221402050057437047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11022960147601366704958031 16534440221402050057437047)
    ·
      refine ⟨24801660332103075086155571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16534440221402050057437047 24801660332103075086155571)
      ·
        refine ⟨37202490498154612629233357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24801660332103075086155571 37202490498154612629233357)
        ·
          refine ⟨13950933936807979735962509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37202490498154612629233357 13950933936807979735962509)
          ·
            refine ⟨5231600226302992400985941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13950933936807979735962509 5231600226302992400985941)
            ·
              refine ⟨30653907575994096099527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5231600226302992400985941 30653907575994096099527)
              ·
                rfl

theorem cell21_1208890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 9].length) (baseStart_1208890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1208890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1208890 prefixEnd_1208890 := by exact prefixLift 1208890
  have htrace : WordTrace (prefixWord ++ tailWord_1208890) baseStart_1208890 baseEnd_1208890 := by
    simpa [prefixWord, tailWord_1208890, baseEnd_1208890] using wordTrace_append hprefix tailTrace_1208890
  have hstable : (prefixWord ++ tailWord_1208890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208890).length < 2 ^ (prefixWord ++ tailWord_1208890).sum := by decide
  have hdescent : baseEnd_1208890 < baseStart_1208890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1208983 : List Nat := [1, 1, 3, 3, 2, 1, 5, 5]
def baseStart_1208983 : Nat := 118140960795 + 1208983 * 2 ^ 59
def prefixEnd_1208983 : Nat := 4983230072969 + 3 ^ 40 * 1208983 * 2
def baseEnd_1208983 : Nat := 91968797350333123281851

theorem tailTrace_1208983 : CollatzResearch.WordTrace tailWord_1208983 prefixEnd_1208983 91968797350333123281851 := by
  unfold tailWord_1208983
  simp only [CollatzResearch.WordTrace]
  refine ⟨44095232579068543702967603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29396821719379029135311735 44095232579068543702967603)
  ·
    refine ⟨66142848868602815554451405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44095232579068543702967603 66142848868602815554451405)
    ·
      refine ⟨24803568325726055832919277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66142848868602815554451405 24803568325726055832919277)
      ·
        refine ⟨9301338122147270937344729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24803568325726055832919277 9301338122147270937344729)
        ·
          refine ⟨6976003591610453203008547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9301338122147270937344729 6976003591610453203008547)
          ·
            refine ⟨10464005387415679804512821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6976003591610453203008547 10464005387415679804512821)
            ·
              refine ⟨981000505070219981673077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10464005387415679804512821 981000505070219981673077)
              ·
                refine ⟨91968797350333123281851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 981000505070219981673077 91968797350333123281851)
                ·
                  rfl

theorem cell21_1208983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 5, 5].length) (baseStart_1208983 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1208983 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1208983 prefixEnd_1208983 := by exact prefixLift 1208983
  have htrace : WordTrace (prefixWord ++ tailWord_1208983) baseStart_1208983 baseEnd_1208983 := by
    simpa [prefixWord, tailWord_1208983, baseEnd_1208983] using wordTrace_append hprefix tailTrace_1208983
  have hstable : (prefixWord ++ tailWord_1208983).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1208983).length < 2 ^ (prefixWord ++ tailWord_1208983).sum := by decide
  have hdescent : baseEnd_1208983 < baseStart_1208983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1208983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209059 : List Nat := [1, 1, 1, 7, 1, 3, 7]
def baseStart_1209059 : Nat := 118140960795 + 1209059 * 2 ^ 59
def prefixEnd_1209059 : Nat := 4983230072969 + 3 ^ 40 * 1209059 * 2
def baseEnd_1209059 : Nat := 30658192920715569619859

theorem tailTrace_1209059 : CollatzResearch.WordTrace tailWord_1209059 prefixEnd_1209059 30658192920715569619859 := by
  unfold tailWord_1209059
  simp only [CollatzResearch.WordTrace]
  refine ⟨44098004526793208682734231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29398669684528805788489487 44098004526793208682734231)
  ·
    refine ⟨66147006790189813024101347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44098004526793208682734231 66147006790189813024101347)
    ·
      refine ⟨99220510185284719536152021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66147006790189813024101347 99220510185284719536152021)
      ·
        refine ⟨2325480707467610614128563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 99220510185284719536152021 2325480707467610614128563)
        ·
          refine ⟨3488221061201415921192845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2325480707467610614128563 3488221061201415921192845)
          ·
            refine ⟨1308082897950530970447317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3488221061201415921192845 1308082897950530970447317)
            ·
              refine ⟨30658192920715569619859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1308082897950530970447317 30658192920715569619859)
              ·
                rfl

theorem cell21_1209059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 7].length) (baseStart_1209059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1209059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1209059 prefixEnd_1209059 := by exact prefixLift 1209059
  have htrace : WordTrace (prefixWord ++ tailWord_1209059) baseStart_1209059 baseEnd_1209059 := by
    simpa [prefixWord, tailWord_1209059, baseEnd_1209059] using wordTrace_append hprefix tailTrace_1209059
  have hstable : (prefixWord ++ tailWord_1209059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209059).length < 2 ^ (prefixWord ++ tailWord_1209059).sum := by decide
  have hdescent : baseEnd_1209059 < baseStart_1209059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209208 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 7]
def baseStart_1209208 : Nat := 118140960795 + 1209208 * 2 ^ 59
def prefixEnd_1209208 : Nat := 4983230072969 + 3 ^ 40 * 1209208 * 2
def baseEnd_1209208 : Nat := 275957740116448978595093

theorem tailTrace_1209208 : CollatzResearch.WordTrace tailWord_1209208 prefixEnd_1209208 275957740116448978595093 := by
  unfold tailWord_1209208
  simp only [CollatzResearch.WordTrace]
  refine ⟨22051719501626703564954139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29402292668835604753272185 22051719501626703564954139)
  ·
    refine ⟨33077579252440055347431209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22051719501626703564954139 33077579252440055347431209)
    ·
      refine ⟨24808184439330041510573407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33077579252440055347431209 24808184439330041510573407)
      ·
        refine ⟨37212276658995062265860111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24808184439330041510573407 37212276658995062265860111)
        ·
          refine ⟨55818414988492593398790167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37212276658995062265860111 55818414988492593398790167)
          ·
            refine ⟨83727622482738890098185251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55818414988492593398790167 83727622482738890098185251)
            ·
              refine ⟨125591433724108335147277877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 83727622482738890098185251 125591433724108335147277877)
              ·
                refine ⟨11774196911635156420057301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 125591433724108335147277877 11774196911635156420057301)
                ·
                  refine ⟨275957740116448978595093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11774196911635156420057301 275957740116448978595093)
                  ·
                    rfl

theorem cell21_1209208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_1209208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1209208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1209208 prefixEnd_1209208 := by exact prefixLift 1209208
  have htrace : WordTrace (prefixWord ++ tailWord_1209208) baseStart_1209208 baseEnd_1209208 := by
    simpa [prefixWord, tailWord_1209208, baseEnd_1209208] using wordTrace_append hprefix tailTrace_1209208
  have hstable : (prefixWord ++ tailWord_1209208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209208).length < 2 ^ (prefixWord ++ tailWord_1209208).sum := by decide
  have hdescent : baseEnd_1209208 < baseStart_1209208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209239 : List Nat := [1, 1, 3, 3, 1, 2, 1, 3, 6]
def baseStart_1209239 : Nat := 118140960795 + 1209239 * 2 ^ 59
def prefixEnd_1209239 : Nat := 4983230072969 + 3 ^ 40 * 1209239 * 2
def baseEnd_1209239 : Nat := 275964814738799813578363

theorem tailTrace_1209239 : CollatzResearch.WordTrace tailWord_1209239 prefixEnd_1209239 275964814738799813578363 := by
  unfold tailWord_1209239
  simp only [CollatzResearch.WordTrace]
  refine ⟨44104569666141099424286771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29403046444094066282857847 44104569666141099424286771)
  ·
    refine ⟨66156854499211649136430157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44104569666141099424286771 66156854499211649136430157)
    ·
      refine ⟨24808820437204368426161309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66156854499211649136430157 24808820437204368426161309)
      ·
        refine ⟨9303307663951638159810491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24808820437204368426161309 9303307663951638159810491)
        ·
          refine ⟨13954961495927457239715737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9303307663951638159810491 13954961495927457239715737)
          ·
            refine ⟨10466221121945592929786803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13954961495927457239715737 10466221121945592929786803)
            ·
              refine ⟨15699331682918389394680205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10466221121945592929786803 15699331682918389394680205)
              ·
                refine ⟨5887249381094396023005077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15699331682918389394680205 5887249381094396023005077)
                ·
                  refine ⟨275964814738799813578363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5887249381094396023005077 275964814738799813578363)
                  ·
                    rfl

theorem cell21_1209239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 6].length) (baseStart_1209239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1209239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1209239 prefixEnd_1209239 := by exact prefixLift 1209239
  have htrace : WordTrace (prefixWord ++ tailWord_1209239) baseStart_1209239 baseEnd_1209239 := by
    simpa [prefixWord, tailWord_1209239, baseEnd_1209239] using wordTrace_append hprefix tailTrace_1209239
  have hstable : (prefixWord ++ tailWord_1209239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209239).length < 2 ^ (prefixWord ++ tailWord_1209239).sum := by decide
  have hdescent : baseEnd_1209239 < baseStart_1209239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209377 : List Nat := [1, 2, 3, 2, 3, 1, 2, 2, 5]
def baseStart_1209377 : Nat := 118140960795 + 1209377 * 2 ^ 59
def prefixEnd_1209377 : Nat := 4983230072969 + 3 ^ 40 * 1209377 * 2
def baseEnd_1209377 : Nat := 275996308218942240278081

theorem tailTrace_1209377 : CollatzResearch.WordTrace tailWord_1209377 prefixEnd_1209377 275996308218942240278081 := by
  unfold tailWord_1209377
  simp only [CollatzResearch.WordTrace]
  refine ⟨44109602939641148992810385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29406401959760765995206923 44109602939641148992810385)
  ·
    refine ⟨33082202204730861744607789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44109602939641148992810385 33082202204730861744607789)
    ·
      refine ⟨12405825826774073154227921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33082202204730861744607789 12405825826774073154227921)
      ·
        refine ⟨9304369370080554865670941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12405825826774073154227921 9304369370080554865670941)
        ·
          refine ⟨3489138513780208074626603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9304369370080554865670941 3489138513780208074626603)
          ·
            refine ⟨5233707770670312111939905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3489138513780208074626603 5233707770670312111939905)
            ·
              refine ⟨3925280828002734083954929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5233707770670312111939905 3925280828002734083954929)
              ·
                refine ⟨2943960621002050562966197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3925280828002734083954929 2943960621002050562966197)
                ·
                  refine ⟨275996308218942240278081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2943960621002050562966197 275996308218942240278081)
                  ·
                    rfl

theorem cell21_1209377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_1209377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1209377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1209377 prefixEnd_1209377 := by exact prefixLift 1209377
  have htrace : WordTrace (prefixWord ++ tailWord_1209377) baseStart_1209377 baseEnd_1209377 := by
    simpa [prefixWord, tailWord_1209377, baseEnd_1209377] using wordTrace_append hprefix tailTrace_1209377
  have hstable : (prefixWord ++ tailWord_1209377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209377).length < 2 ^ (prefixWord ++ tailWord_1209377).sum := by decide
  have hdescent : baseEnd_1209377 < baseStart_1209377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209380 : List Nat := [2, 3, 1, 4, 1, 3, 2, 5]
def baseStart_1209380 : Nat := 118140960795 + 1209380 * 2 ^ 59
def prefixEnd_1209380 : Nat := 4983230072969 + 3 ^ 40 * 1209380 * 2
def baseEnd_1209380 : Nat := 91998997619938300576025

theorem tailTrace_1209380 : CollatzResearch.WordTrace tailWord_1209380 prefixEnd_1209380 91998997619938300576025 := by
  unfold tailWord_1209380
  simp only [CollatzResearch.WordTrace]
  refine ⟨22054856179315140252584797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29406474905753520336779729 22054856179315140252584797)
  ·
    refine ⟨8270571067243177594719299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22054856179315140252584797 8270571067243177594719299)
    ·
      refine ⟨12405856600864766392078949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8270571067243177594719299 12405856600864766392078949)
      ·
        refine ⟨2326098112662143698514803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12405856600864766392078949 2326098112662143698514803)
        ·
          refine ⟨3489147168993215547772205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2326098112662143698514803 3489147168993215547772205)
          ·
            refine ⟨1308430188372455830414577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3489147168993215547772205 1308430188372455830414577)
            ·
              refine ⟨981322641279341872810933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1308430188372455830414577 981322641279341872810933)
              ·
                refine ⟨91998997619938300576025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 981322641279341872810933 91998997619938300576025)
                ·
                  rfl

theorem cell21_1209380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 2, 5].length) (baseStart_1209380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1209380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1209380 prefixEnd_1209380 := by exact prefixLift 1209380
  have htrace : WordTrace (prefixWord ++ tailWord_1209380) baseStart_1209380 baseEnd_1209380 := by
    simpa [prefixWord, tailWord_1209380, baseEnd_1209380] using wordTrace_append hprefix tailTrace_1209380
  have hstable : (prefixWord ++ tailWord_1209380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209380).length < 2 ^ (prefixWord ++ tailWord_1209380).sum := by decide
  have hdescent : baseEnd_1209380 < baseStart_1209380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209422 : List Nat := [4, 1, 1, 1, 1, 3, 4, 6]
def baseStart_1209422 : Nat := 118140960795 + 1209422 * 2 ^ 59
def prefixEnd_1209422 : Nat := 4983230072969 + 3 ^ 40 * 1209422 * 2
def baseEnd_1209422 : Nat := 92002192610677387342663

theorem tailTrace_1209422 : CollatzResearch.WordTrace tailWord_1209422 prefixEnd_1209422 92002192610677387342663 := by
  unfold tailWord_1209422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5513905528059765209774815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29407496149652081118799013 5513905528059765209774815)
  ·
    refine ⟨8270858292089647814662223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5513905528059765209774815 8270858292089647814662223)
    ·
      refine ⟨12406287438134471721993335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8270858292089647814662223 12406287438134471721993335)
      ·
        refine ⟨18609431157201707582990003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12406287438134471721993335 18609431157201707582990003)
        ·
          refine ⟨27914146735802561374485005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18609431157201707582990003 27914146735802561374485005)
          ·
            refine ⟨10467805025925960515431877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27914146735802561374485005 10467805025925960515431877)
            ·
              refine ⟨1962713442361117596643477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10467805025925960515431877 1962713442361117596643477)
              ·
                refine ⟨92002192610677387342663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1962713442361117596643477 92002192610677387342663)
                ·
                  rfl

theorem cell21_1209422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_1209422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1209422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1209422 prefixEnd_1209422 := by exact prefixLift 1209422
  have htrace : WordTrace (prefixWord ++ tailWord_1209422) baseStart_1209422 baseEnd_1209422 := by
    simpa [prefixWord, tailWord_1209422, baseEnd_1209422] using wordTrace_append hprefix tailTrace_1209422
  have hstable : (prefixWord ++ tailWord_1209422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209422).length < 2 ^ (prefixWord ++ tailWord_1209422).sum := by decide
  have hdescent : baseEnd_1209422 < baseStart_1209422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209529 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 5]
def baseStart_1209529 : Nat := 118140960795 + 1209529 * 2 ^ 59
def prefixEnd_1209529 : Nat := 4983230072969 + 3 ^ 40 * 1209529 * 2
def baseEnd_1209529 : Nat := 276030996689823753744437

theorem tailTrace_1209529 : CollatzResearch.WordTrace tailWord_1209529 prefixEnd_1209529 276030996689823753744437 := by
  unfold tailWord_1209529
  simp only [CollatzResearch.WordTrace]
  refine ⟨44115146835090478952343641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29410097890060319301562427 44115146835090478952343641)
  ·
    refine ⟨33086360126317859214257731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44115146835090478952343641 33086360126317859214257731)
    ·
      refine ⟨49629540189476788821386597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33086360126317859214257731 49629540189476788821386597)
      ·
        refine ⟨9305538785526897904009987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 49629540189476788821386597 9305538785526897904009987)
        ·
          refine ⟨13958308178290346856014981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9305538785526897904009987 13958308178290346856014981)
          ·
            refine ⟨2617182783429440035502809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13958308178290346856014981 2617182783429440035502809)
            ·
              refine ⟨1962887087572080026627107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2617182783429440035502809 1962887087572080026627107)
              ·
                refine ⟨2944330631358120039940661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1962887087572080026627107 2944330631358120039940661)
                ·
                  refine ⟨276030996689823753744437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2944330631358120039940661 276030996689823753744437)
                  ·
                    rfl

theorem cell21_1209529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 5].length) (baseStart_1209529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1209529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1209529 prefixEnd_1209529 := by exact prefixLift 1209529
  have htrace : WordTrace (prefixWord ++ tailWord_1209529) baseStart_1209529 baseEnd_1209529 := by
    simpa [prefixWord, tailWord_1209529, baseEnd_1209529] using wordTrace_append hprefix tailTrace_1209529
  have hstable : (prefixWord ++ tailWord_1209529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209529).length < 2 ^ (prefixWord ++ tailWord_1209529).sum := by decide
  have hdescent : baseEnd_1209529 < baseStart_1209529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209543 : List Nat := [1, 1, 4, 1, 1, 1, 1, 7, 4]
def baseStart_1209543 : Nat := 118140960795 + 1209543 * 2 ^ 59
def prefixEnd_1209543 : Nat := 4983230072969 + 3 ^ 40 * 1209543 * 2
def baseEnd_1209543 : Nat := 276034191680562840511075

theorem tailTrace_1209543 : CollatzResearch.WordTrace tailWord_1209543 prefixEnd_1209543 276034191680562840511075 := by
  unfold tailWord_1209543
  simp only [CollatzResearch.WordTrace]
  refine ⟨44115657457039759343353283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29410438304693172895568855 44115657457039759343353283)
  ·
    refine ⟨66173486185559639015029925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44115657457039759343353283 66173486185559639015029925)
    ·
      refine ⟨12407528659792432315318111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66173486185559639015029925 12407528659792432315318111)
      ·
        refine ⟨18611292989688648472977167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12407528659792432315318111 18611292989688648472977167)
        ·
          refine ⟨27916939484532972709465751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18611292989688648472977167 27916939484532972709465751)
          ·
            refine ⟨41875409226799459064198627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27916939484532972709465751 41875409226799459064198627)
            ·
              refine ⟨62813113840199188596297941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41875409226799459064198627 62813113840199188596297941)
              ·
                refine ⟨1472182355629668482725733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 62813113840199188596297941 1472182355629668482725733)
                ·
                  refine ⟨276034191680562840511075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1472182355629668482725733 276034191680562840511075)
                  ·
                    rfl

theorem cell21_1209543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 7, 4].length) (baseStart_1209543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1209543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1209543 prefixEnd_1209543 := by exact prefixLift 1209543
  have htrace : WordTrace (prefixWord ++ tailWord_1209543) baseStart_1209543 baseEnd_1209543 := by
    simpa [prefixWord, tailWord_1209543, baseEnd_1209543] using wordTrace_append hprefix tailTrace_1209543
  have hstable : (prefixWord ++ tailWord_1209543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209543).length < 2 ^ (prefixWord ++ tailWord_1209543).sum := by decide
  have hdescent : baseEnd_1209543 < baseStart_1209543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209636 : List Nat := [2, 3, 1, 3, 1, 1, 4, 2, 4]
def baseStart_1209636 : Nat := 118140960795 + 1209636 * 2 ^ 59
def prefixEnd_1209636 : Nat := 4983230072969 + 3 ^ 40 * 1209636 * 2
def baseEnd_1209636 : Nat := 276055415547615345460885

theorem tailTrace_1209636 : CollatzResearch.WordTrace tailWord_1209636 prefixEnd_1209636 276055415547615345460885 := by
  unfold tailWord_1209636
  simp only [CollatzResearch.WordTrace]
  refine ⟨22059524722851418113244381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29412699630468557484325841 22059524722851418113244381)
  ·
    refine ⟨8272321771069281792466643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22059524722851418113244381 8272321771069281792466643)
    ·
      refine ⟨12408482656603922688699965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8272321771069281792466643 12408482656603922688699965)
      ·
        refine ⟨4653180996226471008262487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12408482656603922688699965 4653180996226471008262487)
        ·
          refine ⟨6979771494339706512393731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4653180996226471008262487 6979771494339706512393731)
          ·
            refine ⟨10469657241509559768590597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6979771494339706512393731 10469657241509559768590597)
            ·
              refine ⟨1963060732783042456610737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10469657241509559768590597 1963060732783042456610737)
              ·
                refine ⟨1472295549587281842458053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1963060732783042456610737 1472295549587281842458053)
                ·
                  refine ⟨276055415547615345460885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1472295549587281842458053 276055415547615345460885)
                  ·
                    rfl

theorem cell21_1209636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_1209636 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1209636 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1209636 prefixEnd_1209636 := by exact prefixLift 1209636
  have htrace : WordTrace (prefixWord ++ tailWord_1209636) baseStart_1209636 baseEnd_1209636 := by
    simpa [prefixWord, tailWord_1209636, baseEnd_1209636] using wordTrace_append hprefix tailTrace_1209636
  have hstable : (prefixWord ++ tailWord_1209636).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209636).length < 2 ^ (prefixWord ++ tailWord_1209636).sum := by decide
  have hdescent : baseEnd_1209636 < baseStart_1209636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209650 : List Nat := [3, 2, 1, 1, 4, 1, 3, 6]
def baseStart_1209650 : Nat := 118140960795 + 1209650 * 2 ^ 59
def prefixEnd_1209650 : Nat := 4983230072969 + 3 ^ 40 * 1209650 * 2
def baseEnd_1209650 : Nat := 92019536846118144075841

theorem tailTrace_1209650 : CollatzResearch.WordTrace tailWord_1209650 prefixEnd_1209650 92019536846118144075841 := by
  unfold tailWord_1209650
  simp only [CollatzResearch.WordTrace]
  refine ⟨11029890016913029154374601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29413040045101411078332269 11029890016913029154374601)
  ·
    refine ⟨8272417512684771865780951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11029890016913029154374601 8272417512684771865780951)
    ·
      refine ⟨12408626269027157798671427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8272417512684771865780951 12408626269027157798671427)
      ·
        refine ⟨18612939403540736698007141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12408626269027157798671427 18612939403540736698007141)
        ·
          refine ⟨3489926138163888130876339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18612939403540736698007141 3489926138163888130876339)
          ·
            refine ⟨5234889207245832196314509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3489926138163888130876339 5234889207245832196314509)
            ·
              refine ⟨1963083452717187073617941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5234889207245832196314509 1963083452717187073617941)
              ·
                refine ⟨92019536846118144075841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1963083452717187073617941 92019536846118144075841)
                ·
                  rfl

theorem cell21_1209650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_1209650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1209650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1209650 prefixEnd_1209650 := by exact prefixLift 1209650
  have htrace : WordTrace (prefixWord ++ tailWord_1209650) baseStart_1209650 baseEnd_1209650 := by
    simpa [prefixWord, tailWord_1209650, baseEnd_1209650] using wordTrace_append hprefix tailTrace_1209650
  have hstable : (prefixWord ++ tailWord_1209650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209650).length < 2 ^ (prefixWord ++ tailWord_1209650).sum := by decide
  have hdescent : baseEnd_1209650 < baseStart_1209650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209664 : List Nat := [2, 1, 1, 2, 2, 1, 5, 2, 5]
def baseStart_1209664 : Nat := 118140960795 + 1209664 * 2 ^ 59
def prefixEnd_1209664 : Nat := 4983230072969 + 3 ^ 40 * 1209664 * 2
def baseEnd_1209664 : Nat := 276061805529093518994161

theorem tailTrace_1209664 : CollatzResearch.WordTrace tailWord_1209664 prefixEnd_1209664 276061805529093518994161 := by
  unfold tailWord_1209664
  simp only [CollatzResearch.WordTrace]
  refine ⟨22060035344800698504254023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29413380459734264672338697 22060035344800698504254023)
  ·
    refine ⟨33090053017201047756381035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22060035344800698504254023 33090053017201047756381035)
    ·
      refine ⟨49635079525801571634571553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33090053017201047756381035 49635079525801571634571553)
      ·
        refine ⟨37226309644351178725928665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49635079525801571634571553 37226309644351178725928665)
        ·
          refine ⟨27919732233263384044446499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37226309644351178725928665 27919732233263384044446499)
          ·
            refine ⟨41879598349895076066669749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27919732233263384044446499 41879598349895076066669749)
            ·
              refine ⟨3926212345302663381250289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41879598349895076066669749 3926212345302663381250289)
              ·
                refine ⟨2944659258976997535937717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3926212345302663381250289 2944659258976997535937717)
                ·
                  refine ⟨276061805529093518994161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2944659258976997535937717 276061805529093518994161)
                  ·
                    rfl

theorem cell21_1209664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_1209664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1209664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1209664 prefixEnd_1209664 := by exact prefixLift 1209664
  have htrace : WordTrace (prefixWord ++ tailWord_1209664) baseStart_1209664 baseEnd_1209664 := by
    simpa [prefixWord, tailWord_1209664, baseEnd_1209664] using wordTrace_append hprefix tailTrace_1209664
  have hstable : (prefixWord ++ tailWord_1209664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209664).length < 2 ^ (prefixWord ++ tailWord_1209664).sum := by decide
  have hdescent : baseEnd_1209664 < baseStart_1209664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209698 : List Nat := [3, 3, 2, 1, 1, 1, 1, 6, 3]
def baseStart_1209698 : Nat := 118140960795 + 1209698 * 2 ^ 59
def prefixEnd_1209698 : Nat := 4983230072969 + 3 ^ 40 * 1209698 * 2
def baseEnd_1209698 : Nat := 276069564792317015427425

theorem tailTrace_1209698 : CollatzResearch.WordTrace tailWord_1209698 prefixEnd_1209698 276069564792317015427425 := by
  unfold tailWord_1209698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11030327692869555203811437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29414207180985480543497165 11030327692869555203811437)
  ·
    refine ⟨4136372884826083201429289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11030327692869555203811437 4136372884826083201429289)
    ·
      refine ⟨3102279663619562401071967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4136372884826083201429289 3102279663619562401071967)
      ·
        refine ⟨4653419495429343601607951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3102279663619562401071967 4653419495429343601607951)
        ·
          refine ⟨6980129243144015402411927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4653419495429343601607951 6980129243144015402411927)
          ·
            refine ⟨10470193864716023103617891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6980129243144015402411927 10470193864716023103617891)
            ·
              refine ⟨15705290797074034655426837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10470193864716023103617891 15705290797074034655426837)
              ·
                refine ⟨736185506112845374473133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 15705290797074034655426837 736185506112845374473133)
                ·
                  refine ⟨276069564792317015427425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 736185506112845374473133 276069564792317015427425)
                  ·
                    rfl

theorem cell21_1209698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_1209698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1209698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1209698 prefixEnd_1209698 := by exact prefixLift 1209698
  have htrace : WordTrace (prefixWord ++ tailWord_1209698) baseStart_1209698 baseEnd_1209698 := by
    simpa [prefixWord, tailWord_1209698, baseEnd_1209698] using wordTrace_append hprefix tailTrace_1209698
  have hstable : (prefixWord ++ tailWord_1209698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209698).length < 2 ^ (prefixWord ++ tailWord_1209698).sum := by decide
  have hdescent : baseEnd_1209698 < baseStart_1209698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209712 : List Nat := [2, 1, 1, 1, 4, 2, 5, 1, 4]
def baseStart_1209712 : Nat := 118140960795 + 1209712 * 2 ^ 59
def prefixEnd_1209712 : Nat := 4983230072969 + 3 ^ 40 * 1209712 * 2
def baseEnd_1209712 : Nat := 276072759783056102194063

theorem tailTrace_1209712 : CollatzResearch.WordTrace tailWord_1209712 prefixEnd_1209712 276072759783056102194063 := by
  unfold tailWord_1209712
  simp only [CollatzResearch.WordTrace]
  refine ⟨22060910696713750603127695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29414547595618334137503593 22060910696713750603127695)
  ·
    refine ⟨33091366045070625904691543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22060910696713750603127695 33091366045070625904691543)
    ·
      refine ⟨49637049067605938857037315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33091366045070625904691543 49637049067605938857037315)
      ·
        refine ⟨74455573601408908285555973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49637049067605938857037315 74455573601408908285555973)
        ·
          refine ⟨13960420050264170303541745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74455573601408908285555973 13960420050264170303541745)
          ·
            refine ⟨10470315037698127727656309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13960420050264170303541745 10470315037698127727656309)
            ·
              refine ⟨981592034784199474467779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10470315037698127727656309 981592034784199474467779)
              ·
                refine ⟨1472388052176299211701669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 981592034784199474467779 1472388052176299211701669)
                ·
                  refine ⟨276072759783056102194063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1472388052176299211701669 276072759783056102194063)
                  ·
                    rfl

theorem cell21_1209712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 5, 1, 4].length) (baseStart_1209712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1209712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1209712 prefixEnd_1209712 := by exact prefixLift 1209712
  have htrace : WordTrace (prefixWord ++ tailWord_1209712) baseStart_1209712 baseEnd_1209712 := by
    simpa [prefixWord, tailWord_1209712, baseEnd_1209712] using wordTrace_append hprefix tailTrace_1209712
  have hstable : (prefixWord ++ tailWord_1209712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209712).length < 2 ^ (prefixWord ++ tailWord_1209712).sum := by decide
  have hdescent : baseEnd_1209712 < baseStart_1209712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209757 : List Nat := [1, 4, 2, 1, 3, 1, 3, 1, 5]
def baseStart_1209757 : Nat := 118140960795 + 1209757 * 2 ^ 59
def prefixEnd_1209757 : Nat := 4983230072969 + 3 ^ 40 * 1209757 * 2
def baseEnd_1209757 : Nat := 276083029396146023943971

theorem tailTrace_1209757 : CollatzResearch.WordTrace tailWord_1209757 prefixEnd_1209757 276083029396146023943971 := by
  unfold tailWord_1209757
  simp only [CollatzResearch.WordTrace]
  refine ⟨44123462678264473891643525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29415641785509649261095683 44123462678264473891643525)
  ·
    refine ⟨8273149252174588854683161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44123462678264473891643525 8273149252174588854683161)
    ·
      refine ⟨6204861939130941641012371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8273149252174588854683161 6204861939130941641012371)
      ·
        refine ⟨9307292908696412461518557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6204861939130941641012371 9307292908696412461518557)
        ·
          refine ⟨3490234840761154673069459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9307292908696412461518557 3490234840761154673069459)
          ·
            refine ⟨5235352261141732009604189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3490234840761154673069459 5235352261141732009604189)
            ·
              refine ⟨1963257097928149503601571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5235352261141732009604189 1963257097928149503601571)
              ·
                refine ⟨2944885646892224255402357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1963257097928149503601571 2944885646892224255402357)
                ·
                  refine ⟨276083029396146023943971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2944885646892224255402357 276083029396146023943971)
                  ·
                    rfl

theorem cell21_1209757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_1209757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1209757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1209757 prefixEnd_1209757 := by exact prefixLift 1209757
  have htrace : WordTrace (prefixWord ++ tailWord_1209757) baseStart_1209757 baseEnd_1209757 := by
    simpa [prefixWord, tailWord_1209757, baseEnd_1209757] using wordTrace_append hprefix tailTrace_1209757
  have hstable : (prefixWord ++ tailWord_1209757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209757).length < 2 ^ (prefixWord ++ tailWord_1209757).sum := by decide
  have hdescent : baseEnd_1209757 < baseStart_1209757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1209937 : List Nat := [1, 2, 2, 1, 3, 2, 4, 6]
def baseStart_1209937 : Nat := 118140960795 + 1209937 * 2 ^ 59
def prefixEnd_1209937 : Nat := 4983230072969 + 3 ^ 40 * 1209937 * 2
def baseEnd_1209937 : Nat := 92041369282835236981201

theorem tailTrace_1209937 : CollatzResearch.WordTrace tailWord_1209937 prefixEnd_1209937 92041369282835236981201 := by
  unfold tailWord_1209937
  simp only [CollatzResearch.WordTrace]
  refine ⟨44130027817612364633196065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29420018545074909755464043 44130027817612364633196065)
  ·
    refine ⟨33097520863209273474897049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44130027817612364633196065 33097520863209273474897049)
    ·
      refine ⟨24823140647406955106172787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33097520863209273474897049 24823140647406955106172787)
      ·
        refine ⟨37234710971110432659259181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24823140647406955106172787 37234710971110432659259181)
        ·
          refine ⟨13963016614166412247222193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37234710971110432659259181 13963016614166412247222193)
          ·
            refine ⟨10472262460624809185416645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13963016614166412247222193 10472262460624809185416645)
            ·
              refine ⟨1963549211367151722265621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10472262460624809185416645 1963549211367151722265621)
              ·
                refine ⟨92041369282835236981201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1963549211367151722265621 92041369282835236981201)
                ·
                  rfl

theorem cell21_1209937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 4, 6].length) (baseStart_1209937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1209937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1209937 prefixEnd_1209937 := by exact prefixLift 1209937
  have htrace : WordTrace (prefixWord ++ tailWord_1209937) baseStart_1209937 baseEnd_1209937 := by
    simpa [prefixWord, tailWord_1209937, baseEnd_1209937] using wordTrace_append hprefix tailTrace_1209937
  have hstable : (prefixWord ++ tailWord_1209937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1209937).length < 2 ^ (prefixWord ++ tailWord_1209937).sum := by decide
  have hdescent : baseEnd_1209937 < baseStart_1209937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1209937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210044 : List Nat := [2, 2, 2, 3, 1, 2, 1, 3, 5]
def baseStart_1210044 : Nat := 118140960795 + 1210044 * 2 ^ 59
def prefixEnd_1210044 : Nat := 4983230072969 + 3 ^ 40 * 1210044 * 2
def baseEnd_1210044 : Nat := 276148526706297302660051

theorem tailTrace_1210044 : CollatzResearch.WordTrace tailWord_1210044 prefixEnd_1210044 276148526706297302660051 := by
  unfold tailWord_1210044
  simp only [CollatzResearch.WordTrace]
  refine ⟨22066965214112360953670593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29422620285483147938227457 22066965214112360953670593)
  ·
    refine ⟨16550223910584270715252945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22066965214112360953670593 16550223910584270715252945)
    ·
      refine ⟨12412667932938203036439709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16550223910584270715252945 12412667932938203036439709)
      ·
        refine ⟨4654750474851826138664891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12412667932938203036439709 4654750474851826138664891)
        ·
          refine ⟨6982125712277739207997337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4654750474851826138664891 6982125712277739207997337)
          ·
            refine ⟨5236594284208304405998003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6982125712277739207997337 5236594284208304405998003)
            ·
              refine ⟨7854891426312456608997005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5236594284208304405998003 7854891426312456608997005)
              ·
                refine ⟨2945584284867171228373877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7854891426312456608997005 2945584284867171228373877)
                ·
                  refine ⟨276148526706297302660051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2945584284867171228373877 276148526706297302660051)
                  ·
                    rfl

theorem cell21_1210044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_1210044 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210044 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210044 prefixEnd_1210044 := by exact prefixLift 1210044
  have htrace : WordTrace (prefixWord ++ tailWord_1210044) baseStart_1210044 baseEnd_1210044 := by
    simpa [prefixWord, tailWord_1210044, baseEnd_1210044] using wordTrace_append hprefix tailTrace_1210044
  have hstable : (prefixWord ++ tailWord_1210044).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210044).length < 2 ^ (prefixWord ++ tailWord_1210044).sum := by decide
  have hdescent : baseEnd_1210044 < baseStart_1210044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210179 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 7]
def baseStart_1210179 : Nat := 118140960795 + 1210179 * 2 ^ 59
def prefixEnd_1210179 : Nat := 4983230072969 + 3 ^ 40 * 1210179 * 2
def baseEnd_1210179 : Nat := 276179335545567067909775

theorem tailTrace_1210179 : CollatzResearch.WordTrace tailWord_1210179 prefixEnd_1210179 276179335545567067909775 := by
  unfold tailWord_1210179
  simp only [CollatzResearch.WordTrace]
  refine ⟨44138854282735639963505591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29425902855157093309003727 44138854282735639963505591)
  ·
    refine ⟨66208281424103459945258387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44138854282735639963505591 66208281424103459945258387)
    ·
      refine ⟨99312422136155189917887581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66208281424103459945258387 99312422136155189917887581)
      ·
        refine ⟨37242158301058196219207843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99312422136155189917887581 37242158301058196219207843)
        ·
          refine ⟨55863237451587294328811765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37242158301058196219207843 55863237451587294328811765)
          ·
            refine ⟨5237178511086308843326103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55863237451587294328811765 5237178511086308843326103)
            ·
              refine ⟨7855767766629463264989155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5237178511086308843326103 7855767766629463264989155)
              ·
                refine ⟨11783651649944194897483733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7855767766629463264989155 11783651649944194897483733)
                ·
                  refine ⟨276179335545567067909775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11783651649944194897483733 276179335545567067909775)
                  ·
                    rfl

theorem cell21_1210179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 7].length) (baseStart_1210179 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210179 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210179 prefixEnd_1210179 := by exact prefixLift 1210179
  have htrace : WordTrace (prefixWord ++ tailWord_1210179) baseStart_1210179 baseEnd_1210179 := by
    simpa [prefixWord, tailWord_1210179, baseEnd_1210179] using wordTrace_append hprefix tailTrace_1210179
  have hstable : (prefixWord ++ tailWord_1210179).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210179).length < 2 ^ (prefixWord ++ tailWord_1210179).sum := by decide
  have hdescent : baseEnd_1210179 < baseStart_1210179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210224 : List Nat := [2, 1, 1, 1, 4, 1, 1, 10]
def baseStart_1210224 : Nat := 118140960795 + 1210224 * 2 ^ 59
def prefixEnd_1210224 : Nat := 4983230072969 + 3 ^ 40 * 1210224 * 2
def baseEnd_1210224 : Nat := 92063201719552329886561

theorem tailTrace_1210224 : CollatzResearch.WordTrace tailWord_1210224 prefixEnd_1210224 92063201719552329886561 := by
  unfold tailWord_1210224
  simp only [CollatzResearch.WordTrace]
  refine ⟨22070247783786306324446863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29426997045048408432595817 22070247783786306324446863)
  ·
    refine ⟨33105371675679459486670295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22070247783786306324446863 33105371675679459486670295)
    ·
      refine ⟨49658057513519189230005443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33105371675679459486670295 49658057513519189230005443)
      ·
        refine ⟨74487086270278783845008165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49658057513519189230005443 74487086270278783845008165)
        ·
          refine ⟨13966328675677271970939031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74487086270278783845008165 13966328675677271970939031)
          ·
            refine ⟨20949493013515907956408547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13966328675677271970939031 20949493013515907956408547)
            ·
              refine ⟨31424239520273861934612821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20949493013515907956408547 31424239520273861934612821)
              ·
                refine ⟨92063201719552329886561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31424239520273861934612821 92063201719552329886561)
                ·
                  rfl

theorem cell21_1210224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 10].length) (baseStart_1210224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210224 prefixEnd_1210224 := by exact prefixLift 1210224
  have htrace : WordTrace (prefixWord ++ tailWord_1210224) baseStart_1210224 baseEnd_1210224 := by
    simpa [prefixWord, tailWord_1210224, baseEnd_1210224] using wordTrace_append hprefix tailTrace_1210224
  have hstable : (prefixWord ++ tailWord_1210224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210224).length < 2 ^ (prefixWord ++ tailWord_1210224).sum := by decide
  have hdescent : baseEnd_1210224 < baseStart_1210224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210247 : List Nat := [1, 1, 4, 2, 5, 1, 1, 3, 3]
def baseStart_1210247 : Nat := 118140960795 + 1210247 * 2 ^ 59
def prefixEnd_1210247 : Nat := 4983230072969 + 3 ^ 40 * 1210247 * 2
def baseEnd_1210247 : Nat := 276194854072014060776303

theorem tailTrace_1210247 : CollatzResearch.WordTrace tailWord_1210247 prefixEnd_1210247 276194854072014060776303 := by
  unfold tailWord_1210247
  simp only [CollatzResearch.WordTrace]
  refine ⟨44141334446489287576980995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29427556297659525051320663 44141334446489287576980995)
  ·
    refine ⟨66212001669733931365471493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44141334446489287576980995 66212001669733931365471493)
    ·
      refine ⟨12414750313075112131025905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66212001669733931365471493 12414750313075112131025905)
      ·
        refine ⟨9311062734806334098269429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12414750313075112131025905 9311062734806334098269429)
        ·
          refine ⟨872912131388093821712759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9311062734806334098269429 872912131388093821712759)
          ·
            refine ⟨1309368197082140732569139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 872912131388093821712759 1309368197082140732569139)
            ·
              refine ⟨1964052295623211098853709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1309368197082140732569139 1964052295623211098853709)
              ·
                refine ⟨736519610858704162070141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1964052295623211098853709 736519610858704162070141)
                ·
                  refine ⟨276194854072014060776303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 736519610858704162070141 276194854072014060776303)
                  ·
                    rfl

theorem cell21_1210247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 3, 3].length) (baseStart_1210247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210247 prefixEnd_1210247 := by exact prefixLift 1210247
  have htrace : WordTrace (prefixWord ++ tailWord_1210247) baseStart_1210247 baseEnd_1210247 := by
    simpa [prefixWord, tailWord_1210247, baseEnd_1210247] using wordTrace_append hprefix tailTrace_1210247
  have hstable : (prefixWord ++ tailWord_1210247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210247).length < 2 ^ (prefixWord ++ tailWord_1210247).sum := by decide
  have hdescent : baseEnd_1210247 < baseStart_1210247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210258 : List Nat := [3, 2, 3, 2, 1, 3, 7]
def baseStart_1210258 : Nat := 118140960795 + 1210258 * 2 ^ 59
def prefixEnd_1210258 : Nat := 4983230072969 + 3 ^ 40 * 1210258 * 2
def baseEnd_1210258 : Nat := 30688596046875609565883

theorem tailTrace_1210258 : CollatzResearch.WordTrace tailWord_1210258 prefixEnd_1210258 30688596046875609565883 := by
  unfold tailWord_1210258
  simp only [CollatzResearch.WordTrace]
  refine ⟨11035433912362359113907857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29427823766299624303754285 11035433912362359113907857)
  ·
    refine ⟨8276575434271769335430893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11035433912362359113907857 8276575434271769335430893)
    ·
      refine ⟨3103715787851913500786585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8276575434271769335430893 3103715787851913500786585)
      ·
        refine ⟨2327786840888935125589939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3103715787851913500786585 2327786840888935125589939)
        ·
          refine ⟨3491680261333402688384909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2327786840888935125589939 3491680261333402688384909)
          ·
            refine ⟨1309380098000026008144341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3491680261333402688384909 1309380098000026008144341)
            ·
              refine ⟨30688596046875609565883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1309380098000026008144341 30688596046875609565883)
              ·
                rfl

theorem cell21_1210258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 7].length) (baseStart_1210258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210258 prefixEnd_1210258 := by exact prefixLift 1210258
  have htrace : WordTrace (prefixWord ++ tailWord_1210258) baseStart_1210258 baseEnd_1210258 := by
    simpa [prefixWord, tailWord_1210258, baseEnd_1210258] using wordTrace_append hprefix tailTrace_1210258
  have hstable : (prefixWord ++ tailWord_1210258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210258).length < 2 ^ (prefixWord ++ tailWord_1210258).sum := by decide
  have hdescent : baseEnd_1210258 < baseStart_1210258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210376 : List Nat := [2, 1, 3, 2, 1, 2, 10]
def baseStart_1210376 : Nat := 118140960795 + 1210376 * 2 ^ 59
def prefixEnd_1210376 : Nat := 4983230072969 + 3 ^ 40 * 1210376 * 2
def baseEnd_1210376 : Nat := 30691588181059833680671

theorem tailTrace_1210376 : CollatzResearch.WordTrace tailWord_1210376 prefixEnd_1210376 30691588181059833680671 := by
  unfold tailWord_1210376
  simp only [CollatzResearch.WordTrace]
  refine ⟨22073019731510971304213491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29430692975347961738951321 22073019731510971304213491)
  ·
    refine ⟨33109529597266456956320237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22073019731510971304213491 33109529597266456956320237)
    ·
      refine ⟨12416073598974921358620089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33109529597266456956320237 12416073598974921358620089)
      ·
        refine ⟨9312055199231191018965067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12416073598974921358620089 9312055199231191018965067)
        ·
          refine ⟨13968082798846786528447601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9312055199231191018965067 13968082798846786528447601)
          ·
            refine ⟨10476062099135089896335701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13968082798846786528447601 10476062099135089896335701)
            ·
              refine ⟨30691588181059833680671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10476062099135089896335701 30691588181059833680671)
              ·
                rfl

theorem cell21_1210376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 10].length) (baseStart_1210376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210376 prefixEnd_1210376 := by exact prefixLift 1210376
  have htrace : WordTrace (prefixWord ++ tailWord_1210376) baseStart_1210376 baseEnd_1210376 := by
    simpa [prefixWord, tailWord_1210376, baseEnd_1210376] using wordTrace_append hprefix tailTrace_1210376
  have hstable : (prefixWord ++ tailWord_1210376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210376).length < 2 ^ (prefixWord ++ tailWord_1210376).sum := by decide
  have hdescent : baseEnd_1210376 < baseStart_1210376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210396 : List Nat := [2, 2, 3, 1, 3, 2, 3, 1, 4]
def baseStart_1210396 : Nat := 118140960795 + 1210396 * 2 ^ 59
def prefixEnd_1210396 : Nat := 4983230072969 + 3 ^ 40 * 1210396 * 2
def baseEnd_1210396 : Nat := 276228857902022912792665

theorem tailTrace_1210396 : CollatzResearch.WordTrace tailWord_1210396 prefixEnd_1210396 276228857902022912792665 := by
  unfold tailWord_1210396
  simp only [CollatzResearch.WordTrace]
  refine ⟨22073384461474743012077521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29431179281966324016103361 22073384461474743012077521)
  ·
    refine ⟨16555038346106057259058141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22073384461474743012077521 16555038346106057259058141)
    ·
      refine ⟨6208139379789771472146803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16555038346106057259058141 6208139379789771472146803)
      ·
        refine ⟨9312209069684657208220205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6208139379789771472146803 9312209069684657208220205)
        ·
          refine ⟨3492078401131746453082577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9312209069684657208220205 3492078401131746453082577)
          ·
            refine ⟨2619058800848809839811933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3492078401131746453082577 2619058800848809839811933)
            ·
              refine ⟨982147050318303689929475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2619058800848809839811933 982147050318303689929475)
              ·
                refine ⟨1473220575477455534894213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982147050318303689929475 1473220575477455534894213)
                ·
                  refine ⟨276228857902022912792665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1473220575477455534894213 276228857902022912792665)
                  ·
                    rfl

theorem cell21_1210396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 3, 1, 4].length) (baseStart_1210396 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210396 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210396 prefixEnd_1210396 := by exact prefixLift 1210396
  have htrace : WordTrace (prefixWord ++ tailWord_1210396) baseStart_1210396 baseEnd_1210396 := by
    simpa [prefixWord, tailWord_1210396, baseEnd_1210396] using wordTrace_append hprefix tailTrace_1210396
  have hstable : (prefixWord ++ tailWord_1210396).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210396).length < 2 ^ (prefixWord ++ tailWord_1210396).sum := by decide
  have hdescent : baseEnd_1210396 < baseStart_1210396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210410 : List Nat := [3, 1, 4, 1, 2, 1, 4, 5]
def baseStart_1210410 : Nat := 118140960795 + 1210410 * 2 ^ 59
def prefixEnd_1210410 : Nat := 4983230072969 + 3 ^ 40 * 1210410 * 2
def baseEnd_1210410 : Nat := 92077350964253999853101

theorem tailTrace_1210410 : CollatzResearch.WordTrace tailWord_1210410 prefixEnd_1210410 92077350964253999853101 := by
  unfold tailWord_1210410
  simp only [CollatzResearch.WordTrace]
  refine ⟨11036819886224691603791171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29431519696599177610109789 11036819886224691603791171)
  ·
    refine ⟨16555229829337037405686757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11036819886224691603791171 16555229829337037405686757)
    ·
      refine ⟨3104105593000694513566267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16555229829337037405686757 3104105593000694513566267)
      ·
        refine ⟨4656158389501041770349401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3104105593000694513566267 4656158389501041770349401)
        ·
          refine ⟨3492118792125781327762051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4656158389501041770349401 3492118792125781327762051)
          ·
            refine ⟨5238178188188671991643077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3492118792125781327762051 5238178188188671991643077)
            ·
              refine ⟨982158410285375998433077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5238178188188671991643077 982158410285375998433077)
              ·
                refine ⟨92077350964253999853101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 982158410285375998433077 92077350964253999853101)
                ·
                  rfl

theorem cell21_1210410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_1210410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210410 prefixEnd_1210410 := by exact prefixLift 1210410
  have htrace : WordTrace (prefixWord ++ tailWord_1210410) baseStart_1210410 baseEnd_1210410 := by
    simpa [prefixWord, tailWord_1210410, baseEnd_1210410] using wordTrace_append hprefix tailTrace_1210410
  have hstable : (prefixWord ++ tailWord_1210410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210410).length < 2 ^ (prefixWord ++ tailWord_1210410).sum := by decide
  have hdescent : baseEnd_1210410 < baseStart_1210410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210441 : List Nat := [1, 2, 1, 1, 2, 2, 7, 2, 3]
def baseStart_1210441 : Nat := 118140960795 + 1210441 * 2 ^ 59
def prefixEnd_1210441 : Nat := 4983230072969 + 3 ^ 40 * 1210441 * 2
def baseEnd_1210441 : Nat := 276239127515112834542573

theorem tailTrace_1210441 : CollatzResearch.WordTrace tailWord_1210441 prefixEnd_1210441 276239127515112834542573 := by
  unfold tailWord_1210441
  simp only [CollatzResearch.WordTrace]
  refine ⟨44148410207786458709543177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29432273471857639139695451 44148410207786458709543177)
  ·
    refine ⟨33111307655839844032157383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44148410207786458709543177 33111307655839844032157383)
    ·
      refine ⟨49666961483759766048236075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33111307655839844032157383 49666961483759766048236075)
      ·
        refine ⟨74500442225639649072354113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49666961483759766048236075 74500442225639649072354113)
        ·
          refine ⟨55875331669229736804265585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74500442225639649072354113 55875331669229736804265585)
          ·
            refine ⟨41906498751922302603199189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55875331669229736804265585 41906498751922302603199189)
            ·
              refine ⟨982183564498178967262481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 41906498751922302603199189 982183564498178967262481)
              ·
                refine ⟨736637673373634225446861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982183564498178967262481 736637673373634225446861)
                ·
                  refine ⟨276239127515112834542573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 736637673373634225446861 276239127515112834542573)
                  ·
                    rfl

theorem cell21_1210441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 3].length) (baseStart_1210441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210441 prefixEnd_1210441 := by exact prefixLift 1210441
  have htrace : WordTrace (prefixWord ++ tailWord_1210441) baseStart_1210441 baseEnd_1210441 := by
    simpa [prefixWord, tailWord_1210441, baseEnd_1210441] using wordTrace_append hprefix tailTrace_1210441
  have hstable : (prefixWord ++ tailWord_1210441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210441).length < 2 ^ (prefixWord ++ tailWord_1210441).sum := by decide
  have hdescent : baseEnd_1210441 < baseStart_1210441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210455 : List Nat := [1, 1, 3, 2, 2, 1, 6, 1, 4]
def baseStart_1210455 : Nat := 118140960795 + 1210455 * 2 ^ 59
def prefixEnd_1210455 : Nat := 4983230072969 + 3 ^ 40 * 1210455 * 2
def baseEnd_1210455 : Nat := 276242322505851921309211

theorem tailTrace_1210455 : CollatzResearch.WordTrace tailWord_1210455 prefixEnd_1210455 276242322505851921309211 := by
  unfold tailWord_1210455
  simp only [CollatzResearch.WordTrace]
  refine ⟨44148920829735739100552819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29432613886490492733701879 44148920829735739100552819)
  ·
    refine ⟨66223381244603608650829229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44148920829735739100552819 66223381244603608650829229)
    ·
      refine ⟨24833767966726353244060961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66223381244603608650829229 24833767966726353244060961)
      ·
        refine ⟨18625325975044764933045721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24833767966726353244060961 18625325975044764933045721)
        ·
          refine ⟨13968994481283573699784291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18625325975044764933045721 13968994481283573699784291)
          ·
            refine ⟨20953491721925360549676437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13968994481283573699784291 20953491721925360549676437)
            ·
              refine ⟨982194924465251275766083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 20953491721925360549676437 982194924465251275766083)
              ·
                refine ⟨1473292386697876913649125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 982194924465251275766083 1473292386697876913649125)
                ·
                  refine ⟨276242322505851921309211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1473292386697876913649125 276242322505851921309211)
                  ·
                    rfl

theorem cell21_1210455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 6, 1, 4].length) (baseStart_1210455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210455 prefixEnd_1210455 := by exact prefixLift 1210455
  have htrace : WordTrace (prefixWord ++ tailWord_1210455) baseStart_1210455 baseEnd_1210455 := by
    simpa [prefixWord, tailWord_1210455, baseEnd_1210455] using wordTrace_append hprefix tailTrace_1210455
  have hstable : (prefixWord ++ tailWord_1210455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210455).length < 2 ^ (prefixWord ++ tailWord_1210455).sum := by decide
  have hdescent : baseEnd_1210455 < baseStart_1210455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210545 : List Nat := [1, 2, 2, 5, 2, 1, 8]
def baseStart_1210545 : Nat := 118140960795 + 1210545 * 2 ^ 59
def prefixEnd_1210545 : Nat := 4983230072969 + 3 ^ 40 * 1210545 * 2
def baseEnd_1210545 : Nat := 30695873525781307201003

theorem tailTrace_1210545 : CollatzResearch.WordTrace tailWord_1210545 prefixEnd_1210545 30695873525781307201003 := by
  unfold tailWord_1210545
  simp only [CollatzResearch.WordTrace]
  refine ⟨44152203399409684471329089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29434802266273122980886059 44152203399409684471329089)
  ·
    refine ⟨33114152549557263353496817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44152203399409684471329089 33114152549557263353496817)
    ·
      refine ⟨24835614412167947515122613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33114152549557263353496817 24835614412167947515122613)
      ·
        refine ⟨2328338851140745079542745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24835614412167947515122613 2328338851140745079542745)
        ·
          refine ⟨1746254138355558809657059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2328338851140745079542745 1746254138355558809657059)
          ·
            refine ⟨2619381207533338214485589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746254138355558809657059 2619381207533338214485589)
            ·
              refine ⟨30695873525781307201003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2619381207533338214485589 30695873525781307201003)
              ·
                rfl

theorem cell21_1210545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 8].length) (baseStart_1210545 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210545 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210545 prefixEnd_1210545 := by exact prefixLift 1210545
  have htrace : WordTrace (prefixWord ++ tailWord_1210545) baseStart_1210545 baseEnd_1210545 := by
    simpa [prefixWord, tailWord_1210545, baseEnd_1210545] using wordTrace_append hprefix tailTrace_1210545
  have hstable : (prefixWord ++ tailWord_1210545).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210545).length < 2 ^ (prefixWord ++ tailWord_1210545).sum := by decide
  have hdescent : baseEnd_1210545 < baseStart_1210545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210610 : List Nat := [3, 2, 1, 3, 2, 2, 3, 2, 3]
def baseStart_1210610 : Nat := 118140960795 + 1210610 * 2 ^ 59
def prefixEnd_1210610 : Nat := 4983230072969 + 3 ^ 40 * 1210610 * 2
def baseEnd_1210610 : Nat := 276277695617606096225561

theorem tailTrace_1210610 : CollatzResearch.WordTrace tailWord_1210610 prefixEnd_1210610 276277695617606096225561 := by
  unfold tailWord_1210610
  simp only [CollatzResearch.WordTrace]
  refine ⟨11038643536043550143111321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29436382762782800381630189 11038643536043550143111321)
  ·
    refine ⟨8278982652032662607333491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11038643536043550143111321 8278982652032662607333491)
    ·
      refine ⟨12418473978048993911000237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8278982652032662607333491 12418473978048993911000237)
      ·
        refine ⟨4656927741768372716625089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12418473978048993911000237 4656927741768372716625089)
        ·
          refine ⟨3492695806326279537468817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4656927741768372716625089 3492695806326279537468817)
          ·
            refine ⟨2619521854744709653101613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3492695806326279537468817 2619521854744709653101613)
            ·
              refine ⟨982320695529266119913105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2619521854744709653101613 982320695529266119913105)
              ·
                refine ⟨736740521646949589934829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982320695529266119913105 736740521646949589934829)
                ·
                  refine ⟨276277695617606096225561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 736740521646949589934829 276277695617606096225561)
                  ·
                    rfl

theorem cell21_1210610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_1210610 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210610 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210610 prefixEnd_1210610 := by exact prefixLift 1210610
  have htrace : WordTrace (prefixWord ++ tailWord_1210610) baseStart_1210610 baseEnd_1210610 := by
    simpa [prefixWord, tailWord_1210610, baseEnd_1210610] using wordTrace_append hprefix tailTrace_1210610
  have hstable : (prefixWord ++ tailWord_1210610).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210610).length < 2 ^ (prefixWord ++ tailWord_1210610).sum := by decide
  have hdescent : baseEnd_1210610 < baseStart_1210610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210652 : List Nat := [2, 2, 3, 1, 1, 1, 1, 7, 3]
def baseStart_1210652 : Nat := 118140960795 + 1210652 * 2 ^ 59
def prefixEnd_1210652 : Nat := 4983230072969 + 3 ^ 40 * 1210652 * 2
def baseEnd_1210652 : Nat := 276287280589823356525475

theorem tailTrace_1210652 : CollatzResearch.WordTrace tailWord_1210652 prefixEnd_1210652 276287280589823356525475 := by
  unfold tailWord_1210652
  simp only [CollatzResearch.WordTrace]
  refine ⟨22078053005011020872737105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29437404006681361163649473 22078053005011020872737105)
  ·
    refine ⟨16558539753758265654552829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22078053005011020872737105 16558539753758265654552829)
    ·
      refine ⟨6209452407659349620457311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16558539753758265654552829 6209452407659349620457311)
      ·
        refine ⟨9314178611489024430685967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6209452407659349620457311 9314178611489024430685967)
        ·
          refine ⟨13971267917233536646028951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9314178611489024430685967 13971267917233536646028951)
          ·
            refine ⟨20956901875850304969043427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13971267917233536646028951 20956901875850304969043427)
            ·
              refine ⟨31435352813775457453565141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20956901875850304969043427 31435352813775457453565141)
              ·
                refine ⟨736766081572862284067933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 31435352813775457453565141 736766081572862284067933)
                ·
                  refine ⟨276287280589823356525475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 736766081572862284067933 276287280589823356525475)
                  ·
                    rfl

theorem cell21_1210652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 7, 3].length) (baseStart_1210652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210652 prefixEnd_1210652 := by exact prefixLift 1210652
  have htrace : WordTrace (prefixWord ++ tailWord_1210652) baseStart_1210652 baseEnd_1210652 := by
    simpa [prefixWord, tailWord_1210652, baseEnd_1210652] using wordTrace_append hprefix tailTrace_1210652
  have hstable : (prefixWord ++ tailWord_1210652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210652).length < 2 ^ (prefixWord ++ tailWord_1210652).sum := by decide
  have hdescent : baseEnd_1210652 < baseStart_1210652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210680 : List Nat := [2, 1, 2, 1, 3, 1, 5, 6]
def baseStart_1210680 : Nat := 118140960795 + 1210680 * 2 ^ 59
def prefixEnd_1210680 : Nat := 4983230072969 + 3 ^ 40 * 1210680 * 2
def baseEnd_1210680 : Nat := 92097890190433843352917

theorem tailTrace_1210680 : CollatzResearch.WordTrace tailWord_1210680 prefixEnd_1210680 92097890190433843352917 := by
  unfold tailWord_1210680
  simp only [CollatzResearch.WordTrace]
  refine ⟨22078563626960301263746747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29438084835947068351662329 22078563626960301263746747)
  ·
    refine ⟨33117845440440451895620121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22078563626960301263746747 33117845440440451895620121)
    ·
      refine ⟨24838384080330338921715091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33117845440440451895620121 24838384080330338921715091)
      ·
        refine ⟨37257576120495508382572637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24838384080330338921715091 37257576120495508382572637)
        ·
          refine ⟨13971591045185815643464739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37257576120495508382572637 13971591045185815643464739)
          ·
            refine ⟨20957386567778723465197109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13971591045185815643464739 20957386567778723465197109)
            ·
              refine ⟨1964754990729255324862229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20957386567778723465197109 1964754990729255324862229)
              ·
                refine ⟨92097890190433843352917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1964754990729255324862229 92097890190433843352917)
                ·
                  rfl

theorem cell21_1210680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 6].length) (baseStart_1210680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210680 prefixEnd_1210680 := by exact prefixLift 1210680
  have htrace : WordTrace (prefixWord ++ tailWord_1210680) baseStart_1210680 baseEnd_1210680 := by
    simpa [prefixWord, tailWord_1210680, baseEnd_1210680] using wordTrace_append hprefix tailTrace_1210680
  have hstable : (prefixWord ++ tailWord_1210680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210680).length < 2 ^ (prefixWord ++ tailWord_1210680).sum := by decide
  have hdescent : baseEnd_1210680 < baseStart_1210680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210728 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 5]
def baseStart_1210728 : Nat := 118140960795 + 1210728 * 2 ^ 59
def prefixEnd_1210728 : Nat := 4983230072969 + 3 ^ 40 * 1210728 * 2
def baseEnd_1210728 : Nat := 276304624825264113258653

theorem tailTrace_1210728 : CollatzResearch.WordTrace tailWord_1210728 prefixEnd_1210728 276304624825264113258653 := by
  unfold tailWord_1210728
  simp only [CollatzResearch.WordTrace]
  refine ⟨22079438978873353362620419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29439251971831137816827225 22079438978873353362620419)
  ·
    refine ⟨33119158468310030043930629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22079438978873353362620419 33119158468310030043930629)
    ·
      refine ⟨6209842212808130633236993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33119158468310030043930629 6209842212808130633236993)
      ·
        refine ⟨4657381659606097974927745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6209842212808130633236993 4657381659606097974927745)
        ·
          refine ⟨3493036244704573481195809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4657381659606097974927745 3493036244704573481195809)
          ·
            refine ⟨2619777183528430110896857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3493036244704573481195809 2619777183528430110896857)
            ·
              refine ⟨1964832887646322583172643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2619777183528430110896857 1964832887646322583172643)
              ·
                refine ⟨2947249331469483874758965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1964832887646322583172643 2947249331469483874758965)
                ·
                  refine ⟨276304624825264113258653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2947249331469483874758965 276304624825264113258653)
                  ·
                    rfl

theorem cell21_1210728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_1210728 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210728 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210728 prefixEnd_1210728 := by exact prefixLift 1210728
  have htrace : WordTrace (prefixWord ++ tailWord_1210728) baseStart_1210728 baseEnd_1210728 := by
    simpa [prefixWord, tailWord_1210728, baseEnd_1210728] using wordTrace_append hprefix tailTrace_1210728
  have hstable : (prefixWord ++ tailWord_1210728).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210728).length < 2 ^ (prefixWord ++ tailWord_1210728).sum := by decide
  have hdescent : baseEnd_1210728 < baseStart_1210728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210756 : List Nat := [2, 3, 2, 1, 1, 2, 3, 7]
def baseStart_1210756 : Nat := 118140960795 + 1210756 * 2 ^ 59
def prefixEnd_1210756 : Nat := 4983230072969 + 3 ^ 40 * 1210756 * 2
def baseEnd_1210756 : Nat := 92103671602247428930643

theorem tailTrace_1210756 : CollatzResearch.WordTrace tailWord_1210756 prefixEnd_1210756 92103671602247428930643 := by
  unfold tailWord_1210756
  simp only [CollatzResearch.WordTrace]
  refine ⟨22079949600822633753630061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29439932801096845004840081 22079949600822633753630061)
  ·
    refine ⟨8279981100308487657611273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22079949600822633753630061 8279981100308487657611273)
    ·
      refine ⟨6209985825231365743208455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8279981100308487657611273 6209985825231365743208455)
      ·
        refine ⟨9314978737847048614812683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6209985825231365743208455 9314978737847048614812683)
        ·
          refine ⟨13972468106770572922219025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9314978737847048614812683 13972468106770572922219025)
          ·
            refine ⟨10479351080077929691664269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13972468106770572922219025 10479351080077929691664269)
            ·
              refine ⟨3929756655029223634374101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10479351080077929691664269 3929756655029223634374101)
              ·
                refine ⟨92103671602247428930643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3929756655029223634374101 92103671602247428930643)
                ·
                  rfl

theorem cell21_1210756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 7].length) (baseStart_1210756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210756 prefixEnd_1210756 := by exact prefixLift 1210756
  have htrace : WordTrace (prefixWord ++ tailWord_1210756) baseStart_1210756 baseEnd_1210756 := by
    simpa [prefixWord, tailWord_1210756, baseEnd_1210756] using wordTrace_append hprefix tailTrace_1210756
  have hstable : (prefixWord ++ tailWord_1210756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210756).length < 2 ^ (prefixWord ++ tailWord_1210756).sum := by decide
  have hdescent : baseEnd_1210756 < baseStart_1210756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210787 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 5]
def baseStart_1210787 : Nat := 118140960795 + 1210787 * 2 ^ 59
def prefixEnd_1210787 : Nat := 4983230072969 + 3 ^ 40 * 1210787 * 2
def baseEnd_1210787 : Nat := 276318089429093121775199

theorem tailTrace_1210787 : CollatzResearch.WordTrace tailWord_1210787 prefixEnd_1210787 276318089429093121775199 := by
  unfold tailWord_1210787
  simp only [CollatzResearch.WordTrace]
  refine ⟨44161029864532959801638615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29440686576355306534425743 44161029864532959801638615)
  ·
    refine ⟨66241544796799439702457923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44161029864532959801638615 66241544796799439702457923)
    ·
      refine ⟨99362317195199159553686885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66241544796799439702457923 99362317195199159553686885)
      ·
        refine ⟨18630434474099842416316291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99362317195199159553686885 18630434474099842416316291)
        ·
          refine ⟨27945651711149763624474437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18630434474099842416316291 27945651711149763624474437)
          ·
            refine ⟨5239809695840580679588957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27945651711149763624474437 5239809695840580679588957)
            ·
              refine ⟨1964928635940217754845859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5239809695840580679588957 1964928635940217754845859)
              ·
                refine ⟨2947392953910326632268789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1964928635940217754845859 2947392953910326632268789)
                ·
                  refine ⟨276318089429093121775199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2947392953910326632268789 276318089429093121775199)
                  ·
                    rfl

theorem cell21_1210787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 5].length) (baseStart_1210787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210787 prefixEnd_1210787 := by exact prefixLift 1210787
  have htrace : WordTrace (prefixWord ++ tailWord_1210787) baseStart_1210787 baseEnd_1210787 := by
    simpa [prefixWord, tailWord_1210787, baseEnd_1210787] using wordTrace_append hprefix tailTrace_1210787
  have hstable : (prefixWord ++ tailWord_1210787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210787).length < 2 ^ (prefixWord ++ tailWord_1210787).sum := by decide
  have hdescent : baseEnd_1210787 < baseStart_1210787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210866 : List Nat := [3, 2, 1, 4, 2, 1, 3, 5]
def baseStart_1210866 : Nat := 118140960795 + 1210866 * 2 ^ 59
def prefixEnd_1210866 : Nat := 4983230072969 + 3 ^ 40 * 1210866 * 2
def baseEnd_1210866 : Nat := 92112039435135513319457

theorem tailTrace_1210866 : CollatzResearch.WordTrace tailWord_1210866 prefixEnd_1210866 92112039435135513319457 := by
  unfold tailWord_1210866
  simp only [CollatzResearch.WordTrace]
  refine ⟨11040977807811689073441113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29442607487497837529176301 11040977807811689073441113)
  ·
    refine ⟨8280733355858766805080835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11040977807811689073441113 8280733355858766805080835)
    ·
      refine ⟨12421100033788150207621253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8280733355858766805080835 12421100033788150207621253)
      ·
        refine ⟨2328956256335278163928985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12421100033788150207621253 2328956256335278163928985)
        ·
          refine ⟨1746717192251458622946739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2328956256335278163928985 1746717192251458622946739)
          ·
            refine ⟨2620075788377187934420109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746717192251458622946739 2620075788377187934420109)
            ·
              refine ⟨982528420641445475407541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2620075788377187934420109 982528420641445475407541)
              ·
                refine ⟨92112039435135513319457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 982528420641445475407541 92112039435135513319457)
                ·
                  rfl

theorem cell21_1210866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 5].length) (baseStart_1210866 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210866 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210866 prefixEnd_1210866 := by exact prefixLift 1210866
  have htrace : WordTrace (prefixWord ++ tailWord_1210866) baseStart_1210866 baseEnd_1210866 := by
    simpa [prefixWord, tailWord_1210866, baseEnd_1210866] using wordTrace_append hprefix tailTrace_1210866
  have hstable : (prefixWord ++ tailWord_1210866).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210866).length < 2 ^ (prefixWord ++ tailWord_1210866).sum := by decide
  have hdescent : baseEnd_1210866 < baseStart_1210866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210877 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 6]
def baseStart_1210877 : Nat := 118140960795 + 1210877 * 2 ^ 59
def prefixEnd_1210877 : Nat := 4983230072969 + 3 ^ 40 * 1210877 * 2
def baseEnd_1210877 : Nat := 276338628655272965275015

theorem tailTrace_1210877 : CollatzResearch.WordTrace tailWord_1210877 prefixEnd_1210877 276338628655272965275015 := by
  unfold tailWord_1210877
  simp only [CollatzResearch.WordTrace]
  refine ⟨44164312434206905172414885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29442874956137936781609923 44164312434206905172414885)
  ·
    refine ⟨8280808581413794719827791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44164312434206905172414885 8280808581413794719827791)
    ·
      refine ⟨12421212872120692079741687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8280808581413794719827791 12421212872120692079741687)
      ·
        refine ⟨18631819308181038119612531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12421212872120692079741687 18631819308181038119612531)
        ·
          refine ⟨27947728962271557179418797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18631819308181038119612531 27947728962271557179418797)
          ·
            refine ⟨10480398360851833942282049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27947728962271557179418797 10480398360851833942282049)
            ·
              refine ⟨7860298770638875456711537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10480398360851833942282049 7860298770638875456711537)
              ·
                refine ⟨5895224077979156592533653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7860298770638875456711537 5895224077979156592533653)
                ·
                  refine ⟨276338628655272965275015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5895224077979156592533653 276338628655272965275015)
                  ·
                    rfl

theorem cell21_1210877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 6].length) (baseStart_1210877 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210877 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210877 prefixEnd_1210877 := by exact prefixLift 1210877
  have htrace : WordTrace (prefixWord ++ tailWord_1210877) baseStart_1210877 baseEnd_1210877 := by
    simpa [prefixWord, tailWord_1210877, baseEnd_1210877] using wordTrace_append hprefix tailTrace_1210877
  have hstable : (prefixWord ++ tailWord_1210877).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210877).length < 2 ^ (prefixWord ++ tailWord_1210877).sum := by decide
  have hdescent : baseEnd_1210877 < baseStart_1210877 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210886 : List Nat := [6, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1210886 : Nat := 118140960795 + 1210886 * 2 ^ 59
def prefixEnd_1210886 : Nat := 4983230072969 + 3 ^ 40 * 1210886 * 2
def baseEnd_1210886 : Nat := 276340682577890949624997

theorem tailTrace_1210886 : CollatzResearch.WordTrace tailWord_1210886 prefixEnd_1210886 276340682577890949624997 := by
  unfold tailWord_1210886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1380145021599196865921641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 29443093794116199806328341 1380145021599196865921641)
  ·
    refine ⟨1035108766199397649441231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1380145021599196865921641 1035108766199397649441231)
    ·
      refine ⟨1552663149299096474161847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1035108766199397649441231 1552663149299096474161847)
      ·
        refine ⟨2328994723948644711242771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1552663149299096474161847 2328994723948644711242771)
        ·
          refine ⟨3493492085922967066864157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2328994723948644711242771 3493492085922967066864157)
          ·
            refine ⟨1310059532221112650074059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3493492085922967066864157 1310059532221112650074059)
            ·
              refine ⟨1965089298331668975111089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1310059532221112650074059 1965089298331668975111089)
              ·
                refine ⟨1473816973748751731333317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1965089298331668975111089 1473816973748751731333317)
                ·
                  refine ⟨276340682577890949624997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1473816973748751731333317 276340682577890949624997)
                  ·
                    rfl

theorem cell21_1210886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1210886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210886 prefixEnd_1210886 := by exact prefixLift 1210886
  have htrace : WordTrace (prefixWord ++ tailWord_1210886) baseStart_1210886 baseEnd_1210886 := by
    simpa [prefixWord, tailWord_1210886, baseEnd_1210886] using wordTrace_append hprefix tailTrace_1210886
  have hstable : (prefixWord ++ tailWord_1210886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210886).length < 2 ^ (prefixWord ++ tailWord_1210886).sum := by decide
  have hdescent : baseEnd_1210886 < baseStart_1210886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210894 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 6]
def baseStart_1210894 : Nat := 118140960795 + 1210894 * 2 ^ 59
def prefixEnd_1210894 : Nat := 4983230072969 + 3 ^ 40 * 1210894 * 2
def baseEnd_1210894 : Nat := 276342508286884713491647

theorem tailTrace_1210894 : CollatzResearch.WordTrace tailWord_1210894 prefixEnd_1210894 276342508286884713491647 := by
  unfold tailWord_1210894
  simp only [CollatzResearch.WordTrace]
  refine ⟨5520616559393164634472967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29443288316763544717189157 5520616559393164634472967)
  ·
    refine ⟨8280924839089746951709451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5520616559393164634472967 8280924839089746951709451)
    ·
      refine ⟨12421387258634620427564177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8280924839089746951709451 12421387258634620427564177)
      ·
        refine ⟨9316040443975965320673133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12421387258634620427564177 9316040443975965320673133)
        ·
          refine ⟨3493515166490986995252425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9316040443975965320673133 3493515166490986995252425)
          ·
            refine ⟨2620136374868240246439319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3493515166490986995252425 2620136374868240246439319)
            ·
              refine ⟨3930204562302360369658979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2620136374868240246439319 3930204562302360369658979)
              ·
                refine ⟨5895306843453540554488469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3930204562302360369658979 5895306843453540554488469)
                ·
                  refine ⟨276342508286884713491647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5895306843453540554488469 276342508286884713491647)
                  ·
                    rfl

theorem cell21_1210894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 6].length) (baseStart_1210894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210894 prefixEnd_1210894 := by exact prefixLift 1210894
  have htrace : WordTrace (prefixWord ++ tailWord_1210894) baseStart_1210894 baseEnd_1210894 := by
    simpa [prefixWord, tailWord_1210894, baseEnd_1210894] using wordTrace_append hprefix tailTrace_1210894
  have hstable : (prefixWord ++ tailWord_1210894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210894).length < 2 ^ (prefixWord ++ tailWord_1210894).sum := by decide
  have hdescent : baseEnd_1210894 < baseStart_1210894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210942 : List Nat := [4, 2, 1, 4, 1, 2, 7]
def baseStart_1210942 : Nat := 118140960795 + 1210942 * 2 ^ 59
def prefixEnd_1210942 : Nat := 4983230072969 + 3 ^ 40 * 1210942 * 2
def baseEnd_1210942 : Nat := 30705940282316366299061

theorem tailTrace_1210942 : CollatzResearch.WordTrace tailWord_1210942 prefixEnd_1210942 30705940282316366299061 := by
  unfold tailWord_1210942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5520835397371427659191385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29444455452647614182354053 5520835397371427659191385)
  ·
    refine ⟨4140626548028570744393539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5520835397371427659191385 4140626548028570744393539)
    ·
      refine ⟨6210939822042856116590309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4140626548028570744393539 6210939822042856116590309)
      ·
        refine ⟨1164551216633035521860683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6210939822042856116590309 1164551216633035521860683)
        ·
          refine ⟨1746826824949553282791025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164551216633035521860683 1746826824949553282791025)
          ·
            refine ⟨1310120118712164962093269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1746826824949553282791025 1310120118712164962093269)
            ·
              refine ⟨30705940282316366299061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1310120118712164962093269 30705940282316366299061)
              ·
                rfl

theorem cell21_1210942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 7].length) (baseStart_1210942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210942 prefixEnd_1210942 := by exact prefixLift 1210942
  have htrace : WordTrace (prefixWord ++ tailWord_1210942) baseStart_1210942 baseEnd_1210942 := by
    simpa [prefixWord, tailWord_1210942, baseEnd_1210942] using wordTrace_append hprefix tailTrace_1210942
  have hstable : (prefixWord ++ tailWord_1210942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210942).length < 2 ^ (prefixWord ++ tailWord_1210942).sum := by decide
  have hdescent : baseEnd_1210942 < baseStart_1210942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1210948 : List Nat := [2, 3, 5, 1, 1, 1, 3, 2, 3]
def baseStart_1210948 : Nat := 118140960795 + 1210948 * 2 ^ 59
def prefixEnd_1210948 : Nat := 4983230072969 + 3 ^ 40 * 1210948 * 2
def baseEnd_1210948 : Nat := 276354831822592619591537

theorem tailTrace_1210948 : CollatzResearch.WordTrace tailWord_1210948 prefixEnd_1210948 276354831822592619591537 := by
  unfold tailWord_1210948
  simp only [CollatzResearch.WordTrace]
  refine ⟨22083451008474842149124749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29444601344633122865499665 22083451008474842149124749)
  ·
    refine ⟨8281294128178065805921781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22083451008474842149124749 8281294128178065805921781)
    ·
      refine ⟨776371324516693669305167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8281294128178065805921781 776371324516693669305167)
      ·
        refine ⟨1164556986775040503957751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 776371324516693669305167 1164556986775040503957751)
        ·
          refine ⟨1746835480162560755936627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1164556986775040503957751 1746835480162560755936627)
          ·
            refine ⟨2620253220243841133904941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1746835480162560755936627 2620253220243841133904941)
            ·
              refine ⟨982594957591440425214353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2620253220243841133904941 982594957591440425214353)
              ·
                refine ⟨736946218193580318910765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982594957591440425214353 736946218193580318910765)
                ·
                  refine ⟨276354831822592619591537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 736946218193580318910765 276354831822592619591537)
                  ·
                    rfl

theorem cell21_1210948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_1210948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1210948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1210948 prefixEnd_1210948 := by exact prefixLift 1210948
  have htrace : WordTrace (prefixWord ++ tailWord_1210948) baseStart_1210948 baseEnd_1210948 := by
    simpa [prefixWord, tailWord_1210948, baseEnd_1210948] using wordTrace_append hprefix tailTrace_1210948
  have hstable : (prefixWord ++ tailWord_1210948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1210948).length < 2 ^ (prefixWord ++ tailWord_1210948).sum := by decide
  have hdescent : baseEnd_1210948 < baseStart_1210948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1210948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211018 : List Nat := [3, 1, 2, 3, 4, 1, 1, 6]
def baseStart_1211018 : Nat := 118140960795 + 1211018 * 2 ^ 59
def prefixEnd_1211018 : Nat := 4983230072969 + 3 ^ 40 * 1211018 * 2
def baseEnd_1211018 : Nat := 92123602258762684474909

theorem tailTrace_1211018 : CollatzResearch.WordTrace tailWord_1211018 prefixEnd_1211018 92123602258762684474909 := by
  unfold tailWord_1211018
  simp only [CollatzResearch.WordTrace]
  refine ⟨11042363781674021563324427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29446303417797390835531805 11042363781674021563324427)
  ·
    refine ⟨16563545672511032344986641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11042363781674021563324427 16563545672511032344986641)
    ·
      refine ⟨12422659254383274258739981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16563545672511032344986641 12422659254383274258739981)
      ·
        refine ⟨4658497220393727847027493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12422659254383274258739981 4658497220393727847027493)
        ·
          refine ⟨873468228823823971317655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4658497220393727847027493 873468228823823971317655)
          ·
            refine ⟨1310202343235735956976483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873468228823823971317655 1310202343235735956976483)
            ·
              refine ⟨1965303514853603935464725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1310202343235735956976483 1965303514853603935464725)
              ·
                refine ⟨92123602258762684474909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1965303514853603935464725 92123602258762684474909)
                ·
                  rfl

theorem cell21_1211018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_1211018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211018 prefixEnd_1211018 := by exact prefixLift 1211018
  have htrace : WordTrace (prefixWord ++ tailWord_1211018) baseStart_1211018 baseEnd_1211018 := by
    simpa [prefixWord, tailWord_1211018, baseEnd_1211018] using wordTrace_append hprefix tailTrace_1211018
  have hstable : (prefixWord ++ tailWord_1211018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211018).length < 2 ^ (prefixWord ++ tailWord_1211018).sum := by decide
  have hdescent : baseEnd_1211018 < baseStart_1211018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211063 : List Nat := [1, 1, 3, 1, 6, 2, 1, 2, 4]
def baseStart_1211063 : Nat := 118140960795 + 1211063 * 2 ^ 59
def prefixEnd_1211063 : Nat := 4983230072969 + 3 ^ 40 * 1211063 * 2
def baseEnd_1211063 : Nat := 276381076389377975174635

theorem tailTrace_1211063 : CollatzResearch.WordTrace tailWord_1211063 prefixEnd_1211063 276381076389377975174635 := by
  unfold tailWord_1211063
  simp only [CollatzResearch.WordTrace]
  refine ⟨44171096411533058938685843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29447397607688705959123895 44171096411533058938685843)
  ·
    refine ⟨66256644617299588408028765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44171096411533058938685843 66256644617299588408028765)
    ·
      refine ⟨24846241731487345653010787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66256644617299588408028765 24846241731487345653010787)
      ·
        refine ⟨37269362597231018479516181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24846241731487345653010787 37269362597231018479516181)
        ·
          refine ⟨1747001371745203991227321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 37269362597231018479516181 1747001371745203991227321)
          ·
            refine ⟨1310251028808902993420491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1747001371745203991227321 1310251028808902993420491)
            ·
              refine ⟨1965376543213354490130737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1310251028808902993420491 1965376543213354490130737)
              ·
                refine ⟨1474032407410015867598053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1965376543213354490130737 1474032407410015867598053)
                ·
                  refine ⟨276381076389377975174635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1474032407410015867598053 276381076389377975174635)
                  ·
                    rfl

theorem cell21_1211063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 2, 1, 2, 4].length) (baseStart_1211063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211063 prefixEnd_1211063 := by exact prefixLift 1211063
  have htrace : WordTrace (prefixWord ++ tailWord_1211063) baseStart_1211063 baseEnd_1211063 := by
    simpa [prefixWord, tailWord_1211063, baseEnd_1211063] using wordTrace_append hprefix tailTrace_1211063
  have hstable : (prefixWord ++ tailWord_1211063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211063).length < 2 ^ (prefixWord ++ tailWord_1211063).sum := by decide
  have hdescent : baseEnd_1211063 < baseStart_1211063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211105 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 6]
def baseStart_1211105 : Nat := 118140960795 + 1211105 * 2 ^ 59
def prefixEnd_1211105 : Nat := 4983230072969 + 3 ^ 40 * 1211105 * 2
def baseEnd_1211105 : Nat := 276390661361595235474549

theorem tailTrace_1211105 : CollatzResearch.WordTrace tailWord_1211105 prefixEnd_1211105 276390661361595235474549 := by
  unfold tailWord_1211105
  simp only [CollatzResearch.WordTrace]
  refine ⟨44172628277380900111714769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29448418851587266741143179 44172628277380900111714769)
  ·
    refine ⟨33129471208035675083786077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44172628277380900111714769 33129471208035675083786077)
    ·
      refine ⟨12423551703013378156419779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33129471208035675083786077 12423551703013378156419779)
      ·
        refine ⟨18635327554520067234629669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12423551703013378156419779 18635327554520067234629669)
        ·
          refine ⟨3494123916472512606493063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18635327554520067234629669 3494123916472512606493063)
          ·
            refine ⟨5241185874708768909739595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3494123916472512606493063 5241185874708768909739595)
            ·
              refine ⟨7861778812063153364609393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5241185874708768909739595 7861778812063153364609393)
              ·
                refine ⟨5896334109047365023457045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7861778812063153364609393 5896334109047365023457045)
                ·
                  refine ⟨276390661361595235474549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5896334109047365023457045 276390661361595235474549)
                  ·
                    rfl

theorem cell21_1211105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 6].length) (baseStart_1211105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211105 prefixEnd_1211105 := by exact prefixLift 1211105
  have htrace : WordTrace (prefixWord ++ tailWord_1211105) baseStart_1211105 baseEnd_1211105 := by
    simpa [prefixWord, tailWord_1211105, baseEnd_1211105] using wordTrace_append hprefix tailTrace_1211105
  have hstable : (prefixWord ++ tailWord_1211105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211105).length < 2 ^ (prefixWord ++ tailWord_1211105).sum := by decide
  have hdescent : baseEnd_1211105 < baseStart_1211105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211108 : List Nat := [2, 3, 1, 1, 1, 4, 3, 3, 3]
def baseStart_1211108 : Nat := 118140960795 + 1211108 * 2 ^ 59
def prefixEnd_1211108 : Nat := 4983230072969 + 3 ^ 40 * 1211108 * 2
def baseEnd_1211108 : Nat := 276391346002467896924543

theorem tailTrace_1211108 : CollatzResearch.WordTrace tailWord_1211108 prefixEnd_1211108 276391346002467896924543 := by
  unfold tailWord_1211108
  simp only [CollatzResearch.WordTrace]
  refine ⟨22086368848185015812036989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29448491797580021082715985 22086368848185015812036989)
  ·
    refine ⟨8282388318069380929513871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22086368848185015812036989 8282388318069380929513871)
    ·
      refine ⟨12423582477104071394270807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8282388318069380929513871 12423582477104071394270807)
      ·
        refine ⟨18635373715656107091406211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12423582477104071394270807 18635373715656107091406211)
        ·
          refine ⟨27953060573484160637109317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18635373715656107091406211 27953060573484160637109317)
          ·
            refine ⟨5241198857528280119457997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27953060573484160637109317 5241198857528280119457997)
            ·
              refine ⟨1965449571573105044796749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5241198857528280119457997 1965449571573105044796749)
              ·
                refine ⟨737043589339914391798781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1965449571573105044796749 737043589339914391798781)
                ·
                  refine ⟨276391346002467896924543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737043589339914391798781 276391346002467896924543)
                  ·
                    rfl

theorem cell21_1211108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_1211108 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211108 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211108 prefixEnd_1211108 := by exact prefixLift 1211108
  have htrace : WordTrace (prefixWord ++ tailWord_1211108) baseStart_1211108 baseEnd_1211108 := by
    simpa [prefixWord, tailWord_1211108, baseEnd_1211108] using wordTrace_append hprefix tailTrace_1211108
  have hstable : (prefixWord ++ tailWord_1211108).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211108).length < 2 ^ (prefixWord ++ tailWord_1211108).sum := by decide
  have hdescent : baseEnd_1211108 < baseStart_1211108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211119 : List Nat := [1, 1, 2, 1, 5, 2, 9]
def baseStart_1211119 : Nat := 118140960795 + 1211119 * 2 ^ 59
def prefixEnd_1211119 : Nat := 4983230072969 + 3 ^ 40 * 1211119 * 2
def baseEnd_1211119 : Nat := 30710428483592702471243

theorem tailTrace_1211119 : CollatzResearch.WordTrace tailWord_1211119 prefixEnd_1211119 30710428483592702471243 := by
  unfold tailWord_1211119
  simp only [CollatzResearch.WordTrace]
  refine ⟨44173138899330180502724411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29448759266220120335149607 44173138899330180502724411)
  ·
    refine ⟨66259708348995270754086617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44173138899330180502724411 66259708348995270754086617)
    ·
      refine ⟨49694781261746453065564963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66259708348995270754086617 49694781261746453065564963)
      ·
        refine ⟨74542171892619679598347445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49694781261746453065564963 74542171892619679598347445)
        ·
          refine ⟨6988328614933094962345073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74542171892619679598347445 6988328614933094962345073)
          ·
            refine ⟨5241246461199821221758805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6988328614933094962345073 5241246461199821221758805)
            ·
              refine ⟨30710428483592702471243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5241246461199821221758805 30710428483592702471243)
              ·
                rfl

theorem cell21_1211119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 9].length) (baseStart_1211119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211119 prefixEnd_1211119 := by exact prefixLift 1211119
  have htrace : WordTrace (prefixWord ++ tailWord_1211119) baseStart_1211119 baseEnd_1211119 := by
    simpa [prefixWord, tailWord_1211119, baseEnd_1211119] using wordTrace_append hprefix tailTrace_1211119
  have hstable : (prefixWord ++ tailWord_1211119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211119).length < 2 ^ (prefixWord ++ tailWord_1211119).sum := by decide
  have hdescent : baseEnd_1211119 < baseStart_1211119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211150 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 7]
def baseStart_1211150 : Nat := 118140960795 + 1211150 * 2 ^ 59
def prefixEnd_1211150 : Nat := 4983230072969 + 3 ^ 40 * 1211150 * 2
def baseEnd_1211150 : Nat := 276400930974685157224457

theorem tailTrace_1211150 : CollatzResearch.WordTrace tailWord_1211150 prefixEnd_1211150 276400930974685157224457 := by
  unfold tailWord_1211150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5521783695277234099637863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29449513041478581864735269 5521783695277234099637863)
  ·
    refine ⟨8282675542915851149456795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5521783695277234099637863 8282675542915851149456795)
    ·
      refine ⟨12424013314373776724185193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8282675542915851149456795 12424013314373776724185193)
      ·
        refine ⟨9318009985780332543138895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12424013314373776724185193 9318009985780332543138895)
        ·
          refine ⟨13977014978670498814708343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9318009985780332543138895 13977014978670498814708343)
          ·
            refine ⟨20965522468005748222062515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13977014978670498814708343 20965522468005748222062515)
            ·
              refine ⟨31448283702008622333093773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20965522468005748222062515 31448283702008622333093773)
              ·
                refine ⟨11793106388253233374910165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31448283702008622333093773 11793106388253233374910165)
                ·
                  refine ⟨276400930974685157224457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11793106388253233374910165 276400930974685157224457)
                  ·
                    rfl

theorem cell21_1211150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_1211150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211150 prefixEnd_1211150 := by exact prefixLift 1211150
  have htrace : WordTrace (prefixWord ++ tailWord_1211150) baseStart_1211150 baseEnd_1211150 := by
    simpa [prefixWord, tailWord_1211150, baseEnd_1211150] using wordTrace_append hprefix tailTrace_1211150
  have hstable : (prefixWord ++ tailWord_1211150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211150).length < 2 ^ (prefixWord ++ tailWord_1211150).sum := by decide
  have hdescent : baseEnd_1211150 < baseStart_1211150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211243 : List Nat := [1, 1, 1, 1, 2, 2, 6, 4, 3]
def baseStart_1211243 : Nat := 118140960795 + 1211243 * 2 ^ 59
def prefixEnd_1211243 : Nat := 4983230072969 + 3 ^ 40 * 1211243 * 2
def baseEnd_1211243 : Nat := 276422154841737662174267

theorem tailTrace_1211243 : CollatzResearch.WordTrace tailWord_1211243 prefixEnd_1211243 276422154841737662174267 := by
  unfold tailWord_1211243
  simp only [CollatzResearch.WordTrace]
  refine ⟨44177661550880949680238383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29451774367253966453492255 44177661550880949680238383)
  ·
    refine ⟨66266492326321424520357575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44177661550880949680238383 66266492326321424520357575)
    ·
      refine ⟨99399738489482136780536363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66266492326321424520357575 99399738489482136780536363)
      ·
        refine ⟨149099607734223205170804545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 99399738489482136780536363 149099607734223205170804545)
        ·
          refine ⟨111824705800667403878103409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 149099607734223205170804545 111824705800667403878103409)
          ·
            refine ⟨83868529350500552908577557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 111824705800667403878103409 83868529350500552908577557)
            ·
              refine ⟨3931337313304713417589573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 83868529350500552908577557 3931337313304713417589573)
              ·
                refine ⟨737125746244633765798045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3931337313304713417589573 737125746244633765798045)
                ·
                  refine ⟨276422154841737662174267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737125746244633765798045 276422154841737662174267)
                  ·
                    rfl

theorem cell21_1211243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 6, 4, 3].length) (baseStart_1211243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211243 prefixEnd_1211243 := by exact prefixLift 1211243
  have htrace : WordTrace (prefixWord ++ tailWord_1211243) baseStart_1211243 baseEnd_1211243 := by
    simpa [prefixWord, tailWord_1211243, baseEnd_1211243] using wordTrace_append hprefix tailTrace_1211243
  have hstable : (prefixWord ++ tailWord_1211243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211243).length < 2 ^ (prefixWord ++ tailWord_1211243).sum := by decide
  have hdescent : baseEnd_1211243 < baseStart_1211243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211353 : List Nat := [1, 2, 1, 2, 5, 3, 2, 2, 3]
def baseStart_1211353 : Nat := 118140960795 + 1211353 * 2 ^ 59
def prefixEnd_1211353 : Nat := 4983230072969 + 3 ^ 40 * 1211353 * 2
def baseEnd_1211353 : Nat := 276447258340401915340709

theorem tailTrace_1211353 : CollatzResearch.WordTrace tailWord_1211353 prefixEnd_1211353 276447258340401915340709 := by
  unfold tailWord_1211353
  simp only [CollatzResearch.WordTrace]
  refine ⟨44181673580482438466742713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29454449053654958977828475 44181673580482438466742713)
  ·
    refine ⟨33136255185361828850057035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44181673580482438466742713 33136255185361828850057035)
    ·
      refine ⟨49704382778042743275085553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33136255185361828850057035 49704382778042743275085553)
      ·
        refine ⟨37278287083532057456314165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49704382778042743275085553 37278287083532057456314165)
        ·
          refine ⟨3494839414081130386529453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37278287083532057456314165 3494839414081130386529453)
          ·
            refine ⟨1310564780280423894948545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3494839414081130386529453 1310564780280423894948545)
            ·
              refine ⟨982923585210317921211409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1310564780280423894948545 982923585210317921211409)
              ·
                refine ⟨737192688907738440908557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 982923585210317921211409 737192688907738440908557)
                ·
                  refine ⟨276447258340401915340709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737192688907738440908557 276447258340401915340709)
                  ·
                    rfl

theorem cell21_1211353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 3].length) (baseStart_1211353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211353 prefixEnd_1211353 := by exact prefixLift 1211353
  have htrace : WordTrace (prefixWord ++ tailWord_1211353) baseStart_1211353 baseEnd_1211353 := by
    simpa [prefixWord, tailWord_1211353, baseEnd_1211353] using wordTrace_append hprefix tailTrace_1211353
  have hstable : (prefixWord ++ tailWord_1211353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211353).length < 2 ^ (prefixWord ++ tailWord_1211353).sum := by decide
  have hdescent : baseEnd_1211353 < baseStart_1211353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211457 : List Nat := [1, 2, 5, 1, 4, 1, 7]
def baseStart_1211457 : Nat := 118140960795 + 1211457 * 2 ^ 59
def prefixEnd_1211457 : Nat := 4983230072969 + 3 ^ 40 * 1211457 * 2
def baseEnd_1211457 : Nat := 30718999173035649511907

theorem tailTrace_1211457 : CollatzResearch.WordTrace tailWord_1211457 prefixEnd_1211457 30718999173035649511907 := by
  unfold tailWord_1211457
  simp only [CollatzResearch.WordTrace]
  refine ⟨44185466772105664228528625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29456977848070442819019083 44185466772105664228528625)
  ·
    refine ⟨33139100079079248171396469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44185466772105664228528625 33139100079079248171396469)
    ·
      refine ⟨3106790632413679516068419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 33139100079079248171396469 3106790632413679516068419)
      ·
        refine ⟨4660185948620519274102629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3106790632413679516068419 4660185948620519274102629)
        ·
          refine ⟨873784865366347363894243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4660185948620519274102629 873784865366347363894243)
          ·
            refine ⟨1310677298049521045841365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 873784865366347363894243 1310677298049521045841365)
            ·
              refine ⟨30718999173035649511907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1310677298049521045841365 30718999173035649511907)
              ·
                rfl

theorem cell21_1211457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 7].length) (baseStart_1211457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211457 prefixEnd_1211457 := by exact prefixLift 1211457
  have htrace : WordTrace (prefixWord ++ tailWord_1211457) baseStart_1211457 baseEnd_1211457 := by
    simpa [prefixWord, tailWord_1211457, baseEnd_1211457] using wordTrace_append hprefix tailTrace_1211457
  have hstable : (prefixWord ++ tailWord_1211457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211457).length < 2 ^ (prefixWord ++ tailWord_1211457).sum := by decide
  have hdescent : baseEnd_1211457 < baseStart_1211457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211530 : List Nat := [3, 1, 2, 3, 1, 1, 2, 3, 5]
def baseStart_1211530 : Nat := 118140960795 + 1211530 * 2 ^ 59
def prefixEnd_1211530 : Nat := 4983230072969 + 3 ^ 40 * 1211530 * 2
def baseEnd_1211530 : Nat := 276487652151888940890347

theorem tailTrace_1211530 : CollatzResearch.WordTrace tailWord_1211530 prefixEnd_1211530 276487652151888940890347 := by
  unfold tailWord_1211530
  simp only [CollatzResearch.WordTrace]
  refine ⟨11047032325210299423984011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29458752867227465130624029 11047032325210299423984011)
  ·
    refine ⟨16570548487815449135976017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11047032325210299423984011 16570548487815449135976017)
    ·
      refine ⟨12427911365861586851982013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16570548487815449135976017 12427911365861586851982013)
      ·
        refine ⟨4660466762198095069493255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12427911365861586851982013 4660466762198095069493255)
        ·
          refine ⟨6990700143297142604239883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4660466762198095069493255 6990700143297142604239883)
          ·
            refine ⟨10486050214945713906359825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6990700143297142604239883 10486050214945713906359825)
            ·
              refine ⟨7864537661209285429769869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10486050214945713906359825 7864537661209285429769869)
              ·
                refine ⟨2949201622953482036163701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7864537661209285429769869 2949201622953482036163701)
                ·
                  refine ⟨276487652151888940890347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2949201622953482036163701 276487652151888940890347)
                  ·
                    rfl

theorem cell21_1211530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_1211530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211530 prefixEnd_1211530 := by exact prefixLift 1211530
  have htrace : WordTrace (prefixWord ++ tailWord_1211530) baseStart_1211530 baseEnd_1211530 := by
    simpa [prefixWord, tailWord_1211530, baseEnd_1211530] using wordTrace_append hprefix tailTrace_1211530
  have hstable : (prefixWord ++ tailWord_1211530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211530).length < 2 ^ (prefixWord ++ tailWord_1211530).sum := by decide
  have hdescent : baseEnd_1211530 < baseStart_1211530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211620 : List Nat := [2, 3, 1, 1, 1, 2, 3, 2, 6]
def baseStart_1211620 : Nat := 118140960795 + 1211620 * 2 ^ 59
def prefixEnd_1211620 : Nat := 4983230072969 + 3 ^ 40 * 1211620 * 2
def baseEnd_1211620 : Nat := 276508191378068784390163

theorem tailTrace_1211620 : CollatzResearch.WordTrace tailWord_1211620 prefixEnd_1211620 276508191378068784390163 := by
  unfold tailWord_1211620
  simp only [CollatzResearch.WordTrace]
  refine ⟨22095705935257571533356157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29460941247010095377808209 22095705935257571533356157)
  ·
    refine ⟨8285889725721589325008559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22095705935257571533356157 8285889725721589325008559)
    ·
      refine ⟨12428834588582383987512839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8285889725721589325008559 12428834588582383987512839)
      ·
        refine ⟨18643251882873575981269259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12428834588582383987512839 18643251882873575981269259)
        ·
          refine ⟨27964877824310363971903889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18643251882873575981269259 27964877824310363971903889)
          ·
            refine ⟨20973658368232772978927917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27964877824310363971903889 20973658368232772978927917)
            ·
              refine ⟨7865121888087289867097969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20973658368232772978927917 7865121888087289867097969)
              ·
                refine ⟨5898841416065467400323477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7865121888087289867097969 5898841416065467400323477)
                ·
                  refine ⟨276508191378068784390163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5898841416065467400323477 276508191378068784390163)
                  ·
                    rfl

theorem cell21_1211620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_1211620 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211620 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211620 prefixEnd_1211620 := by exact prefixLift 1211620
  have htrace : WordTrace (prefixWord ++ tailWord_1211620) baseStart_1211620 baseEnd_1211620 := by
    simpa [prefixWord, tailWord_1211620, baseEnd_1211620] using wordTrace_append hprefix tailTrace_1211620
  have hstable : (prefixWord ++ tailWord_1211620).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211620).length < 2 ^ (prefixWord ++ tailWord_1211620).sum := by decide
  have hdescent : baseEnd_1211620 < baseStart_1211620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211651 : List Nat := [1, 1, 1, 3, 2, 5, 2, 6]
def baseStart_1211651 : Nat := 118140960795 + 1211651 * 2 ^ 59
def prefixEnd_1211651 : Nat := 4983230072969 + 3 ^ 40 * 1211651 * 2
def baseEnd_1211651 : Nat := 92171755333473206457811

theorem tailTrace_1211651 : CollatzResearch.WordTrace tailWord_1211651 prefixEnd_1211651 92171755333473206457811 := by
  unfold tailWord_1211651
  simp only [CollatzResearch.WordTrace]
  refine ⟨44192542533402835361090807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29461695022268556907393871 44192542533402835361090807)
  ·
    refine ⟨66288813800104253041636211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44192542533402835361090807 66288813800104253041636211)
    ·
      refine ⟨99433220700156379562454317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66288813800104253041636211 99433220700156379562454317)
      ·
        refine ⟨37287457762558642335920369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 99433220700156379562454317 37287457762558642335920369)
        ·
          refine ⟨27965593321918981751940277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37287457762558642335920369 27965593321918981751940277)
          ·
            refine ⟨2621774373929904539244401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27965593321918981751940277 2621774373929904539244401)
            ·
              refine ⟨1966330780447428404433301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2621774373929904539244401 1966330780447428404433301)
              ·
                refine ⟨92171755333473206457811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1966330780447428404433301 92171755333473206457811)
                ·
                  rfl

theorem cell21_1211651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 6].length) (baseStart_1211651 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211651 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211651 prefixEnd_1211651 := by exact prefixLift 1211651
  have htrace : WordTrace (prefixWord ++ tailWord_1211651) baseStart_1211651 baseEnd_1211651 := by
    simpa [prefixWord, tailWord_1211651, baseEnd_1211651] using wordTrace_append hprefix tailTrace_1211651
  have hstable : (prefixWord ++ tailWord_1211651).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211651).length < 2 ^ (prefixWord ++ tailWord_1211651).sum := by decide
  have hdescent : baseEnd_1211651 < baseStart_1211651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211665 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 7]
def baseStart_1211665 : Nat := 118140960795 + 1211665 * 2 ^ 59
def prefixEnd_1211665 : Nat := 4983230072969 + 3 ^ 40 * 1211665 * 2
def baseEnd_1211665 : Nat := 276518460991158706140071

theorem tailTrace_1211665 : CollatzResearch.WordTrace tailWord_1211665 prefixEnd_1211665 276518460991158706140071 := by
  unfold tailWord_1211665
  simp only [CollatzResearch.WordTrace]
  refine ⟨44193053155352115752100449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29462035436901410501400299 44193053155352115752100449)
  ·
    refine ⟨33144789866514086814075337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44193053155352115752100449 33144789866514086814075337)
    ·
      refine ⟨24858592399885565110556503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33144789866514086814075337 24858592399885565110556503)
      ·
        refine ⟨37287888599828347665834755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24858592399885565110556503 37287888599828347665834755)
        ·
          refine ⟨55931832899742521498752133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37287888599828347665834755 55931832899742521498752133)
          ·
            refine ⟨10487218668701722781016025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55931832899742521498752133 10487218668701722781016025)
            ·
              refine ⟨7865414001526292085762019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10487218668701722781016025 7865414001526292085762019)
              ·
                refine ⟨11798121002289438128643029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7865414001526292085762019 11798121002289438128643029)
                ·
                  refine ⟨276518460991158706140071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11798121002289438128643029 276518460991158706140071)
                  ·
                    rfl

theorem cell21_1211665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 7].length) (baseStart_1211665 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211665 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211665 prefixEnd_1211665 := by exact prefixLift 1211665
  have htrace : WordTrace (prefixWord ++ tailWord_1211665) baseStart_1211665 baseEnd_1211665 := by
    simpa [prefixWord, tailWord_1211665, baseEnd_1211665] using wordTrace_append hprefix tailTrace_1211665
  have hstable : (prefixWord ++ tailWord_1211665).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211665).length < 2 ^ (prefixWord ++ tailWord_1211665).sum := by decide
  have hdescent : baseEnd_1211665 < baseStart_1211665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211699 : List Nat := [1, 1, 1, 2, 5, 3, 1, 4, 3]
def baseStart_1211699 : Nat := 118140960795 + 1211699 * 2 ^ 59
def prefixEnd_1211699 : Nat := 4983230072969 + 3 ^ 40 * 1211699 * 2
def baseEnd_1211699 : Nat := 276526220254382202573335

theorem tailTrace_1211699 : CollatzResearch.WordTrace tailWord_1211699 prefixEnd_1211699 276526220254382202573335 := by
  unfold tailWord_1211699
  simp only [CollatzResearch.WordTrace]
  refine ⟨44194293237228939558838151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29462862158152626372558767 44194293237228939558838151)
  ·
    refine ⟨66291439855843409338257227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44194293237228939558838151 66291439855843409338257227)
    ·
      refine ⟨99437159783765114007385841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66291439855843409338257227 99437159783765114007385841)
      ·
        refine ⟨74577869837823835505539381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99437159783765114007385841 74577869837823835505539381)
        ·
          refine ⟨6991675297295984578644317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 74577869837823835505539381 6991675297295984578644317)
          ·
            refine ⟨2621878236485994216991619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6991675297295984578644317 2621878236485994216991619)
            ·
              refine ⟨3932817354728991325487429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2621878236485994216991619 3932817354728991325487429)
              ·
                refine ⟨737403254011685873528893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3932817354728991325487429 737403254011685873528893)
                ·
                  refine ⟨276526220254382202573335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737403254011685873528893 276526220254382202573335)
                  ·
                    rfl

theorem cell21_1211699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 4, 3].length) (baseStart_1211699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211699 prefixEnd_1211699 := by exact prefixLift 1211699
  have htrace : WordTrace (prefixWord ++ tailWord_1211699) baseStart_1211699 baseEnd_1211699 := by
    simpa [prefixWord, tailWord_1211699, baseEnd_1211699] using wordTrace_append hprefix tailTrace_1211699
  have hstable : (prefixWord ++ tailWord_1211699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211699).length < 2 ^ (prefixWord ++ tailWord_1211699).sum := by decide
  have hdescent : baseEnd_1211699 < baseStart_1211699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211702 : List Nat := [5, 1, 2, 3, 1, 2, 1, 6]
def baseStart_1211702 : Nat := 118140960795 + 1211702 * 2 ^ 59
def prefixEnd_1211702 : Nat := 4983230072969 + 3 ^ 40 * 1211702 * 2
def baseEnd_1211702 : Nat := 92175634965084954674443

theorem tailTrace_1211702 : CollatzResearch.WordTrace tailWord_1211702 prefixEnd_1211702 92175634965084954674443 := by
  unfold tailWord_1211702
  simp only [CollatzResearch.WordTrace]
  refine ⟨2762150166013629441949835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29462935104145380714131573 2762150166013629441949835)
  ·
    refine ⟨4143225249020444162924753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2762150166013629441949835 4143225249020444162924753)
    ·
      refine ⟨3107418936765333122193565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4143225249020444162924753 3107418936765333122193565)
      ·
        refine ⟨1165282101286999920822587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3107418936765333122193565 1165282101286999920822587)
        ·
          refine ⟨1747923151930499881233881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1165282101286999920822587 1747923151930499881233881)
          ·
            refine ⟨1310942363947874910925411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1747923151930499881233881 1310942363947874910925411)
            ·
              refine ⟨1966413545921812366388117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1310942363947874910925411 1966413545921812366388117)
              ·
                refine ⟨92175634965084954674443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1966413545921812366388117 92175634965084954674443)
                ·
                  rfl

theorem cell21_1211702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_1211702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211702 prefixEnd_1211702 := by exact prefixLift 1211702
  have htrace : WordTrace (prefixWord ++ tailWord_1211702) baseStart_1211702 baseEnd_1211702 := by
    simpa [prefixWord, tailWord_1211702, baseEnd_1211702] using wordTrace_append hprefix tailTrace_1211702
  have hstable : (prefixWord ++ tailWord_1211702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211702).length < 2 ^ (prefixWord ++ tailWord_1211702).sum := by decide
  have hdescent : baseEnd_1211702 < baseStart_1211702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211778 : List Nat := [3, 4, 2, 1, 1, 3, 2, 5]
def baseStart_1211778 : Nat := 118140960795 + 1211778 * 2 ^ 59
def prefixEnd_1211778 : Nat := 4983230072969 + 3 ^ 40 * 1211778 * 2
def baseEnd_1211778 : Nat := 92181416376898540252169

theorem tailTrace_1211778 : CollatzResearch.WordTrace tailWord_1211778 prefixEnd_1211778 92181416376898540252169 := by
  unfold tailWord_1211778
  simp only [CollatzResearch.WordTrace]
  refine ⟨11049293650985684012740997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29464783069295157367309325 11049293650985684012740997)
  ·
    refine ⟨2071742559559815752388937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11049293650985684012740997 2071742559559815752388937)
    ·
      refine ⟨1553806919669861814291703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2071742559559815752388937 1553806919669861814291703)
      ·
        refine ⟨2330710379504792721437555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1553806919669861814291703 2330710379504792721437555)
        ·
          refine ⟨3496065569257189082156333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2330710379504792721437555 3496065569257189082156333)
          ·
            refine ⟨1311024588471445905808625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3496065569257189082156333 1311024588471445905808625)
            ·
              refine ⟨983268441353584429356469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1311024588471445905808625 983268441353584429356469)
              ·
                refine ⟨92181416376898540252169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 983268441353584429356469 92181416376898540252169)
                ·
                  rfl

theorem cell21_1211778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_1211778 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211778 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211778 prefixEnd_1211778 := by exact prefixLift 1211778
  have htrace : WordTrace (prefixWord ++ tailWord_1211778) baseStart_1211778 baseEnd_1211778 := by
    simpa [prefixWord, tailWord_1211778, baseEnd_1211778] using wordTrace_append hprefix tailTrace_1211778
  have hstable : (prefixWord ++ tailWord_1211778).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211778).length < 2 ^ (prefixWord ++ tailWord_1211778).sum := by decide
  have hdescent : baseEnd_1211778 < baseStart_1211778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211865 : List Nat := [1, 2, 1, 2, 4, 3, 2, 2, 4]
def baseStart_1211865 : Nat := 118140960795 + 1211865 * 2 ^ 59
def prefixEnd_1211865 : Nat := 4983230072969 + 3 ^ 40 * 1211865 * 2
def baseEnd_1211865 : Nat := 276564103716002802806329

theorem tailTrace_1211865 : CollatzResearch.WordTrace tailWord_1211865 prefixEnd_1211865 276564103716002802806329 := by
  unfold tailWord_1211865
  simp only [CollatzResearch.WordTrace]
  refine ⟨44200347754627549909381049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29466898503085033272920699 44200347754627549909381049)
  ·
    refine ⟨33150260815970662432035787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44200347754627549909381049 33150260815970662432035787)
    ·
      refine ⟨49725391223955993648053681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33150260815970662432035787 49725391223955993648053681)
      ·
        refine ⟨37294043417966995236040261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49725391223955993648053681 37294043417966995236040261)
        ·
          refine ⟨6992633140868811606757549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37294043417966995236040261 6992633140868811606757549)
          ·
            refine ⟨2622237427825804352534081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6992633140868811606757549 2622237427825804352534081)
            ·
              refine ⟨1966678070869353264400561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2622237427825804352534081 1966678070869353264400561)
              ·
                refine ⟨1475008553152014948300421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1966678070869353264400561 1475008553152014948300421)
                ·
                  refine ⟨276564103716002802806329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1475008553152014948300421 276564103716002802806329)
                  ·
                    rfl

theorem cell21_1211865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 4].length) (baseStart_1211865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211865 prefixEnd_1211865 := by exact prefixLift 1211865
  have htrace : WordTrace (prefixWord ++ tailWord_1211865) baseStart_1211865 baseEnd_1211865 := by
    simpa [prefixWord, tailWord_1211865, baseEnd_1211865] using wordTrace_append hprefix tailTrace_1211865
  have hstable : (prefixWord ++ tailWord_1211865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211865).length < 2 ^ (prefixWord ++ tailWord_1211865).sum := by decide
  have hdescent : baseEnd_1211865 < baseStart_1211865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211879 : List Nat := [1, 1, 5, 2, 1, 2, 3, 6]
def baseStart_1211879 : Nat := 118140960795 + 1211879 * 2 ^ 59
def prefixEnd_1211879 : Nat := 4983230072969 + 3 ^ 40 * 1211879 * 2
def baseEnd_1211879 : Nat := 92189099568913963190989

theorem tailTrace_1211879 : CollatzResearch.WordTrace tailWord_1211879 prefixEnd_1211879 92189099568913963190989 := by
  unfold tailWord_1211879
  simp only [CollatzResearch.WordTrace]
  refine ⟨44200858376576830300390691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29467238917717886866927127 44200858376576830300390691)
  ·
    refine ⟨66301287564865245450586037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44200858376576830300390691 66301287564865245450586037)
    ·
      refine ⟨6215745709206116760992441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66301287564865245450586037 6215745709206116760992441)
      ·
        refine ⟨4661809281904587570744331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6215745709206116760992441 4661809281904587570744331)
        ·
          refine ⟨6992713922856881356116497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4661809281904587570744331 6992713922856881356116497)
          ·
            refine ⟨5244535442142661017087373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6992713922856881356116497 5244535442142661017087373)
            ·
              refine ⟨1966700790803497881407765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5244535442142661017087373 1966700790803497881407765)
              ·
                refine ⟨92189099568913963190989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1966700790803497881407765 92189099568913963190989)
                ·
                  rfl

theorem cell21_1211879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 6].length) (baseStart_1211879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211879 prefixEnd_1211879 := by exact prefixLift 1211879
  have htrace : WordTrace (prefixWord ++ tailWord_1211879) baseStart_1211879 baseEnd_1211879 := by
    simpa [prefixWord, tailWord_1211879, baseEnd_1211879] using wordTrace_append hprefix tailTrace_1211879
  have hstable : (prefixWord ++ tailWord_1211879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211879).length < 2 ^ (prefixWord ++ tailWord_1211879).sum := by decide
  have hdescent : baseEnd_1211879 < baseStart_1211879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211955 : List Nat := [1, 1, 1, 2, 4, 3, 4, 5]
def baseStart_1211955 : Nat := 118140960795 + 1211955 * 2 ^ 59
def prefixEnd_1211955 : Nat := 4983230072969 + 3 ^ 40 * 1211955 * 2
def baseEnd_1211955 : Nat := 92194880980727548768715

theorem tailTrace_1211955 : CollatzResearch.WordTrace tailWord_1211955 prefixEnd_1211955 92194880980727548768715 := by
  unfold tailWord_1211955
  simp only [CollatzResearch.WordTrace]
  refine ⟨44203630324301495280157319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29469086882867663520104879 44203630324301495280157319)
  ·
    refine ⟨66305445486452242920235979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44203630324301495280157319 66305445486452242920235979)
    ·
      refine ⟨99458168229678364380353969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66305445486452242920235979 99458168229678364380353969)
      ·
        refine ⟨74593626172258773285265477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99458168229678364380353969 74593626172258773285265477)
        ·
          refine ⟨13986304907298519990987277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 74593626172258773285265477 13986304907298519990987277)
          ·
            refine ⟨5244864340236944996620229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13986304907298519990987277 5244864340236944996620229)
            ·
              refine ⟨983412063794427186866293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5244864340236944996620229 983412063794427186866293)
              ·
                refine ⟨92194880980727548768715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 983412063794427186866293 92194880980727548768715)
                ·
                  rfl

theorem cell21_1211955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 5].length) (baseStart_1211955 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211955 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211955 prefixEnd_1211955 := by exact prefixLift 1211955
  have htrace : WordTrace (prefixWord ++ tailWord_1211955) baseStart_1211955 baseEnd_1211955 := by
    simpa [prefixWord, tailWord_1211955, baseEnd_1211955] using wordTrace_append hprefix tailTrace_1211955
  have hstable : (prefixWord ++ tailWord_1211955).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211955).length < 2 ^ (prefixWord ++ tailWord_1211955).sum := by decide
  have hdescent : baseEnd_1211955 < baseStart_1211955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1211986 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 5]
def baseStart_1211986 : Nat := 118140960795 + 1211986 * 2 ^ 59
def prefixEnd_1211986 : Nat := 4983230072969 + 3 ^ 40 * 1211986 * 2
def baseEnd_1211986 : Nat := 276591717564533481289415

theorem tailTrace_1211986 : CollatzResearch.WordTrace tailWord_1211986 prefixEnd_1211986 276591717564533481289415 := by
  unfold tailWord_1211986
  simp only [CollatzResearch.WordTrace]
  refine ⟨11051190246797296893633953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29469840658126125049690541 11051190246797296893633953)
  ·
    refine ⟨8288392685097972670225465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11051190246797296893633953 8288392685097972670225465)
    ·
      refine ⟨6216294513823479502669099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8288392685097972670225465 6216294513823479502669099)
      ·
        refine ⟨9324441770735219254003649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6216294513823479502669099 9324441770735219254003649)
        ·
          refine ⟨6993331328051414440502737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9324441770735219254003649 6993331328051414440502737)
          ·
            refine ⟨5244998496038560830377053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6993331328051414440502737 5244998496038560830377053)
            ·
              refine ⟨1966874436014460311391395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5244998496038560830377053 1966874436014460311391395)
              ·
                refine ⟨2950311654021690467087093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1966874436014460311391395 2950311654021690467087093)
                ·
                  refine ⟨276591717564533481289415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2950311654021690467087093 276591717564533481289415)
                  ·
                    rfl

theorem cell21_1211986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_1211986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1211986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1211986 prefixEnd_1211986 := by exact prefixLift 1211986
  have htrace : WordTrace (prefixWord ++ tailWord_1211986) baseStart_1211986 baseEnd_1211986 := by
    simpa [prefixWord, tailWord_1211986, baseEnd_1211986] using wordTrace_append hprefix tailTrace_1211986
  have hstable : (prefixWord ++ tailWord_1211986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1211986).length < 2 ^ (prefixWord ++ tailWord_1211986).sum := by decide
  have hdescent : baseEnd_1211986 < baseStart_1211986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1211986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212062 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 7]
def baseStart_1212062 : Nat := 118140960795 + 1212062 * 2 ^ 59
def prefixEnd_1212062 : Nat := 4983230072969 + 3 ^ 40 * 1212062 * 2
def baseEnd_1212062 : Nat := 276609061799974238022593

theorem tailTrace_1212062 : CollatzResearch.WordTrace tailWord_1212062 prefixEnd_1212062 276609061799974238022593 := by
  unfold tailWord_1212062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5525941616864231569287805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29471688623275901702868293 5525941616864231569287805)
  ·
    refine ⟨2072228106324086838482927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5525941616864231569287805 2072228106324086838482927)
    ·
      refine ⟨3108342159486130257724391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2072228106324086838482927 3108342159486130257724391)
      ·
        refine ⟨4662513239229195386586587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3108342159486130257724391 4662513239229195386586587)
        ·
          refine ⟨6993769858843793079879881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4662513239229195386586587 6993769858843793079879881)
          ·
            refine ⟨5245327394132844809909911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6993769858843793079879881 5245327394132844809909911)
            ·
              refine ⟨7867991091199267214864867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5245327394132844809909911 7867991091199267214864867)
              ·
                refine ⟨11801986636798900822297301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7867991091199267214864867 11801986636798900822297301)
                ·
                  refine ⟨276609061799974238022593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11801986636798900822297301 276609061799974238022593)
                  ·
                    rfl

theorem cell21_1212062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_1212062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212062 prefixEnd_1212062 := by exact prefixLift 1212062
  have htrace : WordTrace (prefixWord ++ tailWord_1212062) baseStart_1212062 baseEnd_1212062 := by
    simpa [prefixWord, tailWord_1212062, baseEnd_1212062] using wordTrace_append hprefix tailTrace_1212062
  have hstable : (prefixWord ++ tailWord_1212062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212062).length < 2 ^ (prefixWord ++ tailWord_1212062).sum := by decide
  have hdescent : baseEnd_1212062 < baseStart_1212062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212090 : List Nat := [3, 1, 1, 1, 2, 5, 8]
def baseStart_1212090 : Nat := 118140960795 + 1212090 * 2 ^ 59
def prefixEnd_1212090 : Nat := 4983230072969 + 3 ^ 40 * 1212090 * 2
def baseEnd_1212090 : Nat := 30735050197939156839541

theorem tailTrace_1212090 : CollatzResearch.WordTrace tailWord_1212090 prefixEnd_1212090 30735050197939156839541 := by
  unfold tailWord_1212090
  simp only [CollatzResearch.WordTrace]
  refine ⟨11052138544703103334080431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29472369452541608890881149 11052138544703103334080431)
  ·
    refine ⟨16578207817054655001120647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11052138544703103334080431 16578207817054655001120647)
    ·
      refine ⟨24867311725581982501680971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16578207817054655001120647 24867311725581982501680971)
      ·
        refine ⟨37300967588372973752521457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24867311725581982501680971 37300967588372973752521457)
        ·
          refine ⟨27975725691279730314391093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37300967588372973752521457 27975725691279730314391093)
          ·
            refine ⟨2622724283557474716974165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27975725691279730314391093 2622724283557474716974165)
            ·
              refine ⟨30735050197939156839541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2622724283557474716974165 30735050197939156839541)
              ·
                rfl

theorem cell21_1212090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 8].length) (baseStart_1212090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212090 prefixEnd_1212090 := by exact prefixLift 1212090
  have htrace : WordTrace (prefixWord ++ tailWord_1212090) baseStart_1212090 baseEnd_1212090 := by
    simpa [prefixWord, tailWord_1212090, baseEnd_1212090] using wordTrace_append hprefix tailTrace_1212090
  have hstable : (prefixWord ++ tailWord_1212090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212090).length < 2 ^ (prefixWord ++ tailWord_1212090).sum := by decide
  have hdescent : baseEnd_1212090 < baseStart_1212090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212121 : List Nat := [1, 2, 1, 2, 3, 3, 2, 2, 5]
def baseStart_1212121 : Nat := 118140960795 + 1212121 * 2 ^ 59
def prefixEnd_1212121 : Nat := 4983230072969 + 3 ^ 40 * 1212121 * 2
def baseEnd_1212121 : Nat := 276622526403803246539139

theorem tailTrace_1212121 : CollatzResearch.WordTrace tailWord_1212121 prefixEnd_1212121 276622526403803246539139 := by
  unfold tailWord_1212121
  simp only [CollatzResearch.WordTrace]
  refine ⟨44209684841700105630700217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29473123227800070420466811 44209684841700105630700217)
  ·
    refine ⟨33157263631275079223025163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44209684841700105630700217 33157263631275079223025163)
    ·
      refine ⟨49735895446912618834537745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33157263631275079223025163 49735895446912618834537745)
      ·
        refine ⟨37301921585184464125903309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49735895446912618834537745 37301921585184464125903309)
        ·
          refine ⟨13988220594444174047213741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37301921585184464125903309 13988220594444174047213741)
          ·
            refine ⟨5245582722916565267705153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13988220594444174047213741 5245582722916565267705153)
            ·
              refine ⟨3934187042187423950778865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5245582722916565267705153 3934187042187423950778865)
              ·
                refine ⟨2950640281640567963084149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3934187042187423950778865 2950640281640567963084149)
                ·
                  refine ⟨276622526403803246539139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2950640281640567963084149 276622526403803246539139)
                  ·
                    rfl

theorem cell21_1212121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_1212121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212121 prefixEnd_1212121 := by exact prefixLift 1212121
  have htrace : WordTrace (prefixWord ++ tailWord_1212121) baseStart_1212121 baseEnd_1212121 := by
    simpa [prefixWord, tailWord_1212121, baseEnd_1212121] using wordTrace_append hprefix tailTrace_1212121
  have hstable : (prefixWord ++ tailWord_1212121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212121).length < 2 ^ (prefixWord ++ tailWord_1212121).sum := by decide
  have hdescent : baseEnd_1212121 < baseStart_1212121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212124 : List Nat := [2, 2, 5, 1, 2, 1, 1, 7]
def baseStart_1212124 : Nat := 118140960795 + 1212124 * 2 ^ 59
def prefixEnd_1212124 : Nat := 4983230072969 + 3 ^ 40 * 1212124 * 2
def baseEnd_1212124 : Nat := 92207737014891969329711

theorem tailTrace_1212124 : CollatzResearch.WordTrace tailWord_1212124 prefixEnd_1212124 92207737014891969329711 := by
  unfold tailWord_1212124
  simp only [CollatzResearch.WordTrace]
  refine ⟨22104897130344618571529713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29473196173792824762039617 22104897130344618571529713)
  ·
    refine ⟨16578672847758463928647285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22104897130344618571529713 16578672847758463928647285)
    ·
      refine ⟨1554250579477355993310683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 16578672847758463928647285 1554250579477355993310683)
      ·
        refine ⟨2331375869216033989966025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1554250579477355993310683 2331375869216033989966025)
        ·
          refine ⟨1748531901912025492474519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2331375869216033989966025 1748531901912025492474519)
          ·
            refine ⟨2622797852868038238711779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1748531901912025492474519 2622797852868038238711779)
            ·
              refine ⟨3934196779302057358067669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2622797852868038238711779 3934196779302057358067669)
              ·
                refine ⟨92207737014891969329711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3934196779302057358067669 92207737014891969329711)
                ·
                  rfl

theorem cell21_1212124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 7].length) (baseStart_1212124 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212124 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212124 prefixEnd_1212124 := by exact prefixLift 1212124
  have htrace : WordTrace (prefixWord ++ tailWord_1212124) baseStart_1212124 baseEnd_1212124 := by
    simpa [prefixWord, tailWord_1212124, baseEnd_1212124] using wordTrace_append hprefix tailTrace_1212124
  have hstable : (prefixWord ++ tailWord_1212124).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212124).length < 2 ^ (prefixWord ++ tailWord_1212124).sum := by decide
  have hdescent : baseEnd_1212124 < baseStart_1212124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212206 : List Nat := [4, 1, 3, 2, 3, 1, 2, 2, 3]
def baseStart_1212206 : Nat := 118140960795 + 1212206 * 2 ^ 59
def prefixEnd_1212206 : Nat := 4983230072969 + 3 ^ 40 * 1212206 * 2
def baseEnd_1212206 : Nat := 276641924561861987622299

theorem tailTrace_1212206 : CollatzResearch.WordTrace tailWord_1212206 prefixEnd_1212206 276641924561861987622299 := by
  unfold tailWord_1212206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5526598130799020643443059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29475190030928110098362981 5526598130799020643443059)
  ·
    refine ⟨8289897196198530965164589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5526598130799020643443059 8289897196198530965164589)
    ·
      refine ⟨3108711448574449111936721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8289897196198530965164589 3108711448574449111936721)
      ·
        refine ⟨2331533586430836833952541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3108711448574449111936721 2331533586430836833952541)
        ·
          refine ⟨874325094911563812732203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2331533586430836833952541 874325094911563812732203)
          ·
            refine ⟨1311487642367345719098305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874325094911563812732203 1311487642367345719098305)
            ·
              refine ⟨983615731775509289323729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1311487642367345719098305 983615731775509289323729)
              ·
                refine ⟨737711798831631966992797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 983615731775509289323729 737711798831631966992797)
                ·
                  refine ⟨276641924561861987622299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737711798831631966992797 276641924561861987622299)
                  ·
                    rfl

theorem cell21_1212206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_1212206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212206 prefixEnd_1212206 := by exact prefixLift 1212206
  have htrace : WordTrace (prefixWord ++ tailWord_1212206) baseStart_1212206 baseEnd_1212206 := by
    simpa [prefixWord, tailWord_1212206, baseEnd_1212206] using wordTrace_append hprefix tailTrace_1212206
  have hstable : (prefixWord ++ tailWord_1212206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212206).length < 2 ^ (prefixWord ++ tailWord_1212206).sum := by decide
  have hdescent : baseEnd_1212206 < baseStart_1212206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212217 : List Nat := [1, 2, 1, 7, 2, 1, 1, 6]
def baseStart_1212217 : Nat := 118140960795 + 1212217 * 2 ^ 59
def prefixEnd_1212217 : Nat := 4983230072969 + 3 ^ 40 * 1212217 * 2
def baseEnd_1212217 : Nat := 92214811637242804312981

theorem tailTrace_1212217 : CollatzResearch.WordTrace tailWord_1212217 prefixEnd_1212217 92214811637242804312981 := by
  unfold tailWord_1212217
  simp only [CollatzResearch.WordTrace]
  refine ⟨44213186249352314026194905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29475457499568209350796603 44213186249352314026194905)
  ·
    refine ⟨33159889687014235519646179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44213186249352314026194905 33159889687014235519646179)
    ·
      refine ⟨49739834530521353279469269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33159889687014235519646179 49739834530521353279469269)
      ·
        refine ⟨1165777371809094217487561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 49739834530521353279469269 1165777371809094217487561)
        ·
          refine ⟨874333028856820663115671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1165777371809094217487561 874333028856820663115671)
          ·
            refine ⟨1311499543285230994673507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874333028856820663115671 1311499543285230994673507)
            ·
              refine ⟨1967249314927846492010261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1311499543285230994673507 1967249314927846492010261)
              ·
                refine ⟨92214811637242804312981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1967249314927846492010261 92214811637242804312981)
                ·
                  rfl

theorem cell21_1212217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 6].length) (baseStart_1212217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212217 prefixEnd_1212217 := by exact prefixLift 1212217
  have htrace : WordTrace (prefixWord ++ tailWord_1212217) baseStart_1212217 baseEnd_1212217 := by
    simpa [prefixWord, tailWord_1212217, baseEnd_1212217] using wordTrace_append hprefix tailTrace_1212217
  have hstable : (prefixWord ++ tailWord_1212217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212217).length < 2 ^ (prefixWord ++ tailWord_1212217).sum := by decide
  have hdescent : baseEnd_1212217 < baseStart_1212217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212273 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 5]
def baseStart_1212273 : Nat := 118140960795 + 1212273 * 2 ^ 59
def prefixEnd_1212273 : Nat := 4983230072969 + 3 ^ 40 * 1212273 * 2
def baseEnd_1212273 : Nat := 276657214874684760005495

theorem tailTrace_1212273 : CollatzResearch.WordTrace tailWord_1212273 prefixEnd_1212273 276657214874684760005495 := by
  unfold tailWord_1212273
  simp only [CollatzResearch.WordTrace]
  refine ⟨44215228737149435590233473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29476819158099623726822315 44215228737149435590233473)
  ·
    refine ⟨33161421552862076692675105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44215228737149435590233473 33161421552862076692675105)
    ·
      refine ⟨24871066164646557519506329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33161421552862076692675105 24871066164646557519506329)
      ·
        refine ⟨18653299623484918139629747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24871066164646557519506329 18653299623484918139629747)
        ·
          refine ⟨27979949435227377209444621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18653299623484918139629747 27979949435227377209444621)
          ·
            refine ⟨10492481038210266453541733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27979949435227377209444621 10492481038210266453541733)
            ·
              refine ⟨1967340194664424960039075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10492481038210266453541733 1967340194664424960039075)
              ·
                refine ⟨2951010291996637440058613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1967340194664424960039075 2951010291996637440058613)
                ·
                  refine ⟨276657214874684760005495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2951010291996637440058613 276657214874684760005495)
                  ·
                    rfl

theorem cell21_1212273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 5].length) (baseStart_1212273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212273 prefixEnd_1212273 := by exact prefixLift 1212273
  have htrace : WordTrace (prefixWord ++ tailWord_1212273) baseStart_1212273 baseEnd_1212273 := by
    simpa [prefixWord, tailWord_1212273, baseEnd_1212273] using wordTrace_append hprefix tailTrace_1212273
  have hstable : (prefixWord ++ tailWord_1212273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212273).length < 2 ^ (prefixWord ++ tailWord_1212273).sum := by decide
  have hdescent : baseEnd_1212273 < baseStart_1212273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212310 : List Nat := [5, 3, 1, 1, 3, 1, 7]
def baseStart_1212310 : Nat := 118140960795 + 1212310 * 2 ^ 59
def prefixEnd_1212310 : Nat := 4983230072969 + 3 ^ 40 * 1212310 * 2
def baseEnd_1212310 : Nat := 30740628753197879765417

theorem tailTrace_1212310 : CollatzResearch.WordTrace tailWord_1212310 prefixEnd_1212310 30740628753197879765417 := by
  unfold tailWord_1212310
  simp only [CollatzResearch.WordTrace]
  refine ⟨2763536139875961931833149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 29477718825343593939553589 2763536139875961931833149)
  ·
    refine ⟨1036326052453485724437431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2763536139875961931833149 1036326052453485724437431)
    ·
      refine ⟨1554489078680228586656147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1036326052453485724437431 1554489078680228586656147)
      ·
        refine ⟨2331733618020342879984221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1554489078680228586656147 2331733618020342879984221)
        ·
          refine ⟨874400106757628579994083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2331733618020342879984221 874400106757628579994083)
          ·
            refine ⟨1311600160136442869991125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 874400106757628579994083 1311600160136442869991125)
            ·
              refine ⟨30740628753197879765417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1311600160136442869991125 30740628753197879765417)
              ·
                rfl

theorem cell21_1212310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 7].length) (baseStart_1212310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212310 prefixEnd_1212310 := by exact prefixLift 1212310
  have htrace : WordTrace (prefixWord ++ tailWord_1212310) baseStart_1212310 baseEnd_1212310 := by
    simpa [prefixWord, tailWord_1212310, baseEnd_1212310] using wordTrace_append hprefix tailTrace_1212310
  have hstable : (prefixWord ++ tailWord_1212310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212310).length < 2 ^ (prefixWord ++ tailWord_1212310).sum := by decide
  have hdescent : baseEnd_1212310 < baseStart_1212310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212366 : List Nat := [4, 1, 1, 1, 2, 2, 2, 5, 3]
def baseStart_1212366 : Nat := 118140960795 + 1212366 * 2 ^ 59
def prefixEnd_1212366 : Nat := 4983230072969 + 3 ^ 40 * 1212366 * 2
def baseEnd_1212366 : Nat := 276678438741737264955305

theorem tailTrace_1212366 : CollatzResearch.WordTrace tailWord_1212366 prefixEnd_1212366 276678438741737264955305 := by
  unfold tailWord_1212366
  simp only [CollatzResearch.WordTrace]
  refine ⟨5527327590726564059171119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29479080483875008315579301 5527327590726564059171119)
  ·
    refine ⟨8290991386089846088756679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5527327590726564059171119 8290991386089846088756679)
    ·
      refine ⟨12436487079134769133135019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8290991386089846088756679 12436487079134769133135019)
      ·
        refine ⟨18654730618702153699702529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12436487079134769133135019 18654730618702153699702529)
        ·
          refine ⟨13991047964026615274776897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18654730618702153699702529 13991047964026615274776897)
          ·
            refine ⟨10493285973019961456082673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13991047964026615274776897 10493285973019961456082673)
            ·
              refine ⟨7869964479764971092062005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10493285973019961456082673 7869964479764971092062005)
              ·
                refine ⟨737809169977966039880813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7869964479764971092062005 737809169977966039880813)
                ·
                  refine ⟨276678438741737264955305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737809169977966039880813 276678438741737264955305)
                  ·
                    rfl

theorem cell21_1212366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 3].length) (baseStart_1212366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212366 prefixEnd_1212366 := by exact prefixLift 1212366
  have htrace : WordTrace (prefixWord ++ tailWord_1212366) baseStart_1212366 baseEnd_1212366 := by
    simpa [prefixWord, tailWord_1212366, baseEnd_1212366] using wordTrace_append hprefix tailTrace_1212366
  have hstable : (prefixWord ++ tailWord_1212366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212366).length < 2 ^ (prefixWord ++ tailWord_1212366).sum := by decide
  have hdescent : baseEnd_1212366 < baseStart_1212366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212377 : List Nat := [1, 2, 1, 2, 15]
def baseStart_1212377 : Nat := 118140960795 + 1212377 * 2 ^ 59
def prefixEnd_1212377 : Nat := 4983230072969 + 3 ^ 40 * 1212377 * 2
def baseEnd_1212377 : Nat := 3415814186316094941629

theorem tailTrace_1212377 : CollatzResearch.WordTrace tailWord_1212377 prefixEnd_1212377 3415814186316094941629 := by
  unfold tailWord_1212377
  simp only [CollatzResearch.WordTrace]
  refine ⟨44219021928772661352019385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29479347952515107568012923 44219021928772661352019385)
  ·
    refine ⟨33164266446579496014014539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44219021928772661352019385 33164266446579496014014539)
    ·
      refine ⟨49746399669869244021021809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33164266446579496014014539 49746399669869244021021809)
      ·
        refine ⟨37309799752401933015766357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49746399669869244021021809 37309799752401933015766357)
        ·
          refine ⟨3415814186316094941629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 37309799752401933015766357 3415814186316094941629)
          ·
            rfl

theorem cell21_1212377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 15].length) (baseStart_1212377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212377 prefixEnd_1212377 := by exact prefixLift 1212377
  have htrace : WordTrace (prefixWord ++ tailWord_1212377) baseStart_1212377 baseEnd_1212377 := by
    simpa [prefixWord, tailWord_1212377, baseEnd_1212377] using wordTrace_append hprefix tailTrace_1212377
  have hstable : (prefixWord ++ tailWord_1212377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212377).length < 2 ^ (prefixWord ++ tailWord_1212377).sum := by decide
  have hdescent : baseEnd_1212377 < baseStart_1212377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212383 : List Nat := [1, 1, 2, 3, 4, 1, 4, 2, 3]
def baseStart_1212383 : Nat := 118140960795 + 1212383 * 2 ^ 59
def prefixEnd_1212383 : Nat := 4983230072969 + 3 ^ 40 * 1212383 * 2
def baseEnd_1212383 : Nat := 276682318373349013171937

theorem tailTrace_1212383 : CollatzResearch.WordTrace tailWord_1212383 prefixEnd_1212383 276682318373349013171937 := by
  unfold tailWord_1212383
  simp only [CollatzResearch.WordTrace]
  refine ⟨44219240766750924376737803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29479493844500616251158535 44219240766750924376737803)
  ·
    refine ⟨66328861150126386565106705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44219240766750924376737803 66328861150126386565106705)
    ·
      refine ⟨49746645862594789923830029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66328861150126386565106705 49746645862594789923830029)
      ·
        refine ⟨18654992198473046221436261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49746645862594789923830029 18654992198473046221436261)
        ·
          refine ⟨3497811037213696166519299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18654992198473046221436261 3497811037213696166519299)
          ·
            refine ⟨5246716555820544249778949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3497811037213696166519299 5246716555820544249778949)
            ·
              refine ⟨983759354216352046833553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5246716555820544249778949 983759354216352046833553)
              ·
                refine ⟨737819515662264035125165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 983759354216352046833553 737819515662264035125165)
                ·
                  refine ⟨276682318373349013171937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737819515662264035125165 276682318373349013171937)
                  ·
                    rfl

theorem cell21_1212383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 4, 2, 3].length) (baseStart_1212383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212383 prefixEnd_1212383 := by exact prefixLift 1212383
  have htrace : WordTrace (prefixWord ++ tailWord_1212383) baseStart_1212383 baseEnd_1212383 := by
    simpa [prefixWord, tailWord_1212383, baseEnd_1212383] using wordTrace_append hprefix tailTrace_1212383
  have hstable : (prefixWord ++ tailWord_1212383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212383).length < 2 ^ (prefixWord ++ tailWord_1212383).sum := by decide
  have hdescent : baseEnd_1212383 < baseStart_1212383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212408 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 7]
def baseStart_1212408 : Nat := 118140960795 + 1212408 * 2 ^ 59
def prefixEnd_1212408 : Nat := 4983230072969 + 3 ^ 40 * 1212408 * 2
def baseEnd_1212408 : Nat := 276688023713954525255219

theorem tailTrace_1212408 : CollatzResearch.WordTrace tailWord_1212408 prefixEnd_1212408 276688023713954525255219 := by
  unfold tailWord_1212408
  simp only [CollatzResearch.WordTrace]
  refine ⟨22110076295830176823198939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29480101727773569097598585 22110076295830176823198939)
  ·
    refine ⟨33165114443745265234798409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22110076295830176823198939 33165114443745265234798409)
    ·
      refine ⟨24873835832808948926098807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33165114443745265234798409 24873835832808948926098807)
      ·
        refine ⟨37310753749213423389148211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24873835832808948926098807 37310753749213423389148211)
        ·
          refine ⟨55966130623820135083722317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37310753749213423389148211 55966130623820135083722317)
          ·
            refine ⟨20987298983932550656395869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55966130623820135083722317 20987298983932550656395869)
            ·
              refine ⟨7870237118974706496148451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20987298983932550656395869 7870237118974706496148451)
              ·
                refine ⟨11805355678462059744222677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7870237118974706496148451 11805355678462059744222677)
                ·
                  refine ⟨276688023713954525255219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11805355678462059744222677 276688023713954525255219)
                  ·
                    rfl

theorem cell21_1212408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 7].length) (baseStart_1212408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212408 prefixEnd_1212408 := by exact prefixLift 1212408
  have htrace : WordTrace (prefixWord ++ tailWord_1212408) baseStart_1212408 baseEnd_1212408 := by
    simpa [prefixWord, tailWord_1212408, baseEnd_1212408] using wordTrace_append hprefix tailTrace_1212408
  have hstable : (prefixWord ++ tailWord_1212408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212408).length < 2 ^ (prefixWord ++ tailWord_1212408).sum := by decide
  have hdescent : baseEnd_1212408 < baseStart_1212408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212442 : List Nat := [3, 1, 1, 3, 1, 3, 2, 4, 3]
def baseStart_1212442 : Nat := 118140960795 + 1212442 * 2 ^ 59
def prefixEnd_1212442 : Nat := 4983230072969 + 3 ^ 40 * 1212442 * 2
def baseEnd_1212442 : Nat := 276695782977178021688483

theorem tailTrace_1212442 : CollatzResearch.WordTrace tailWord_1212442 prefixEnd_1212442 276695782977178021688483 := by
  unfold tailWord_1212442
  simp only [CollatzResearch.WordTrace]
  refine ⟨11055348168384294363283895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29480928449024784968757053 11055348168384294363283895)
  ·
    refine ⟨16583022252576441544925843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11055348168384294363283895 16583022252576441544925843)
    ·
      refine ⟨24874533378864662317388765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16583022252576441544925843 24874533378864662317388765)
      ·
        refine ⟨9327950017074248369020787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24874533378864662317388765 9327950017074248369020787)
        ·
          refine ⟨13991925025611372553531181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9327950017074248369020787 13991925025611372553531181)
          ·
            refine ⟨5246971884604264707574193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13991925025611372553531181 5246971884604264707574193)
            ·
              refine ⟨3935228913453198530680645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5246971884604264707574193 3935228913453198530680645)
              ·
                refine ⟨737855421272474724502621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3935228913453198530680645 737855421272474724502621)
                ·
                  refine ⟨276695782977178021688483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737855421272474724502621 276695782977178021688483)
                  ·
                    rfl

theorem cell21_1212442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 2, 4, 3].length) (baseStart_1212442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212442 prefixEnd_1212442 := by exact prefixLift 1212442
  have htrace : WordTrace (prefixWord ++ tailWord_1212442) baseStart_1212442 baseEnd_1212442 := by
    simpa [prefixWord, tailWord_1212442, baseEnd_1212442] using wordTrace_append hprefix tailTrace_1212442
  have hstable : (prefixWord ++ tailWord_1212442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212442).length < 2 ^ (prefixWord ++ tailWord_1212442).sum := by decide
  have hdescent : baseEnd_1212442 < baseStart_1212442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212501 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 5]
def baseStart_1212501 : Nat := 118140960795 + 1212501 * 2 ^ 59
def prefixEnd_1212501 : Nat := 4983230072969 + 3 ^ 40 * 1212501 * 2
def baseEnd_1212501 : Nat := 276709247581007030205029

theorem tailTrace_1212501 : CollatzResearch.WordTrace tailWord_1212501 prefixEnd_1212501 276709247581007030205029 := by
  unfold tailWord_1212501
  simp only [CollatzResearch.WordTrace]
  refine ⟨44223544580323430529533357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29482363053548953686355571 44223544580323430529533357)
  ·
    refine ⟨16583829217621286448575009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44223544580323430529533357 16583829217621286448575009)
    ·
      refine ⟨12437871913215964836431257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16583829217621286448575009 12437871913215964836431257)
      ·
        refine ⟨9328403934911973627323443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12437871913215964836431257 9328403934911973627323443)
        ·
          refine ⟨13992605902367960440985165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9328403934911973627323443 13992605902367960440985165)
          ·
            refine ⟨5247227213387985165369437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13992605902367960440985165 5247227213387985165369437)
            ·
              refine ⟨1967710205020494437013539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5247227213387985165369437 1967710205020494437013539)
              ·
                refine ⟨2951565307530741655520309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1967710205020494437013539 2951565307530741655520309)
                ·
                  refine ⟨276709247581007030205029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2951565307530741655520309 276709247581007030205029)
                  ·
                    rfl

theorem cell21_1212501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 5].length) (baseStart_1212501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212501 prefixEnd_1212501 := by exact prefixLift 1212501
  have htrace : WordTrace (prefixWord ++ tailWord_1212501) baseStart_1212501 baseEnd_1212501 := by
    simpa [prefixWord, tailWord_1212501, baseEnd_1212501] using wordTrace_append hprefix tailTrace_1212501
  have hstable : (prefixWord ++ tailWord_1212501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212501).length < 2 ^ (prefixWord ++ tailWord_1212501).sum := by decide
  have hdescent : baseEnd_1212501 < baseStart_1212501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212529 : List Nat := [1, 2, 2, 2, 1, 1, 3, 9]
def baseStart_1212529 : Nat := 118140960795 + 1212529 * 2 ^ 59
def prefixEnd_1212529 : Nat := 4983230072969 + 3 ^ 40 * 1212529 * 2
def baseEnd_1212529 : Nat := 92238545854161734579435

theorem tailTrace_1212529 : CollatzResearch.WordTrace tailWord_1212529 prefixEnd_1212529 92238545854161734579435 := by
  unfold tailWord_1212529
  simp only [CollatzResearch.WordTrace]
  refine ⟨44224565824221991311552641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29483043882814660874368427 44224565824221991311552641)
  ·
    refine ⟨33168424368166493483664481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44224565824221991311552641 33168424368166493483664481)
    ·
      refine ⟨24876318276124870112748361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33168424368166493483664481 24876318276124870112748361)
      ·
        refine ⟨18657238707093652584561271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24876318276124870112748361 18657238707093652584561271)
        ·
          refine ⟨27985858060640478876841907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18657238707093652584561271 27985858060640478876841907)
          ·
            refine ⟨41978787090960718315262861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27985858060640478876841907 41978787090960718315262861)
            ·
              refine ⟨15742045159110269368223573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41978787090960718315262861 15742045159110269368223573)
              ·
                refine ⟨92238545854161734579435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15742045159110269368223573 92238545854161734579435)
                ·
                  rfl

theorem cell21_1212529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 9].length) (baseStart_1212529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212529 prefixEnd_1212529 := by exact prefixLift 1212529
  have htrace : WordTrace (prefixWord ++ tailWord_1212529) baseStart_1212529 baseEnd_1212529 := by
    simpa [prefixWord, tailWord_1212529, baseEnd_1212529] using wordTrace_append hprefix tailTrace_1212529
  have hstable : (prefixWord ++ tailWord_1212529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212529).length < 2 ^ (prefixWord ++ tailWord_1212529).sum := by decide
  have hdescent : baseEnd_1212529 < baseStart_1212529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212552 : List Nat := [2, 1, 3, 4, 1, 3, 2, 2, 3]
def baseStart_1212552 : Nat := 118140960795 + 1212552 * 2 ^ 59
def prefixEnd_1212552 : Nat := 4983230072969 + 3 ^ 40 * 1212552 * 2
def baseEnd_1212552 : Nat := 276720886475842274854925

theorem tailTrace_1212552 : CollatzResearch.WordTrace tailWord_1212552 prefixEnd_1212552 276720886475842274854925 := by
  unfold tailWord_1212552
  simp only [CollatzResearch.WordTrace]
  refine ⟨22112702351569333119819955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29483603135425777493093273 22112702351569333119819955)
  ·
    refine ⟨33169053527353999679729933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22112702351569333119819955 33169053527353999679729933)
    ·
      refine ⟨12438395072757749879898725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33169053527353999679729933 12438395072757749879898725)
      ·
        refine ⟨2332199076142078102481011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12438395072757749879898725 2332199076142078102481011)
        ·
          refine ⟨3498298614213117153721517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2332199076142078102481011 3498298614213117153721517)
          ·
            refine ⟨1311861980329918932645569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3498298614213117153721517 1311861980329918932645569)
            ·
              refine ⟨983896485247439199484177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1311861980329918932645569 983896485247439199484177)
              ·
                refine ⟨737922363935579399613133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 983896485247439199484177 737922363935579399613133)
                ·
                  refine ⟨276720886475842274854925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737922363935579399613133 276720886475842274854925)
                  ·
                    rfl

theorem cell21_1212552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 3].length) (baseStart_1212552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212552 prefixEnd_1212552 := by exact prefixLift 1212552
  have htrace : WordTrace (prefixWord ++ tailWord_1212552) baseStart_1212552 baseEnd_1212552 := by
    simpa [prefixWord, tailWord_1212552, baseEnd_1212552] using wordTrace_append hprefix tailTrace_1212552
  have hstable : (prefixWord ++ tailWord_1212552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212552).length < 2 ^ (prefixWord ++ tailWord_1212552).sum := by decide
  have hdescent : baseEnd_1212552 < baseStart_1212552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212560 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 5]
def baseStart_1212560 : Nat := 118140960795 + 1212560 * 2 ^ 59
def prefixEnd_1212560 : Nat := 4983230072969 + 3 ^ 40 * 1212560 * 2
def baseEnd_1212560 : Nat := 276722712184836038721575

theorem tailTrace_1212560 : CollatzResearch.WordTrace tailWord_1212560 prefixEnd_1212560 276722712184836038721575 := by
  unfold tailWord_1212560
  simp only [CollatzResearch.WordTrace]
  refine ⟨22112848243554841802965567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29483797658073122403954089 22112848243554841802965567)
  ·
    refine ⟨33169272365332262704448351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22112848243554841802965567 33169272365332262704448351)
    ·
      refine ⟨49753908547998394056672527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33169272365332262704448351 49753908547998394056672527)
      ·
        refine ⟨74630862821997591085008791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49753908547998394056672527 74630862821997591085008791)
        ·
          refine ⟨111946294232996386627513187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74630862821997591085008791 111946294232996386627513187)
          ·
            refine ⟨167919441349494579941269781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 111946294232996386627513187 167919441349494579941269781)
            ·
              refine ⟨7871223813257558434747021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 167919441349494579941269781 7871223813257558434747021)
              ·
                refine ⟨2951708929971584413030133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7871223813257558434747021 2951708929971584413030133)
                ·
                  refine ⟨276722712184836038721575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2951708929971584413030133 276722712184836038721575)
                  ·
                    rfl

theorem cell21_1212560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 5].length) (baseStart_1212560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212560 prefixEnd_1212560 := by exact prefixLift 1212560
  have htrace : WordTrace (prefixWord ++ tailWord_1212560) baseStart_1212560 baseEnd_1212560 := by
    simpa [prefixWord, tailWord_1212560, baseEnd_1212560] using wordTrace_append hprefix tailTrace_1212560
  have hstable : (prefixWord ++ tailWord_1212560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212560).length < 2 ^ (prefixWord ++ tailWord_1212560).sum := by decide
  have hdescent : baseEnd_1212560 < baseStart_1212560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212577 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 5]
def baseStart_1212577 : Nat := 118140960795 + 1212577 * 2 ^ 59
def prefixEnd_1212577 : Nat := 4983230072969 + 3 ^ 40 * 1212577 * 2
def baseEnd_1212577 : Nat := 276726591816447786938207

theorem tailTrace_1212577 : CollatzResearch.WordTrace tailWord_1212577 prefixEnd_1212577 276726591816447786938207 := by
  unfold tailWord_1212577
  simp only [CollatzResearch.WordTrace]
  refine ⟨44226316528048095509299985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29484211018698730339533323 44226316528048095509299985)
  ·
    refine ⟨33169737396036071631974989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44226316528048095509299985 33169737396036071631974989)
    ·
      refine ⟨12438651523513526861990621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33169737396036071631974989 12438651523513526861990621)
      ·
        refine ⟨4664494321317572573246483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12438651523513526861990621 4664494321317572573246483)
        ·
          refine ⟨6996741481976358859869725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4664494321317572573246483 6996741481976358859869725)
          ·
            refine ⟨2623778055741134572451147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6996741481976358859869725 2623778055741134572451147)
            ·
              refine ⟨3935667083611701858676721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2623778055741134572451147 3935667083611701858676721)
              ·
                refine ⟨2951750312708776394007541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3935667083611701858676721 2951750312708776394007541)
                ·
                  refine ⟨276726591816447786938207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2951750312708776394007541 276726591816447786938207)
                  ·
                    rfl

theorem cell21_1212577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_1212577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212577 prefixEnd_1212577 := by exact prefixLift 1212577
  have htrace : WordTrace (prefixWord ++ tailWord_1212577) baseStart_1212577 baseEnd_1212577 := by
    simpa [prefixWord, tailWord_1212577, baseEnd_1212577] using wordTrace_append hprefix tailTrace_1212577
  have hstable : (prefixWord ++ tailWord_1212577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212577).length < 2 ^ (prefixWord ++ tailWord_1212577).sum := by decide
  have hdescent : baseEnd_1212577 < baseStart_1212577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212594 : List Nat := [3, 2, 1, 1, 1, 3, 4, 3, 3]
def baseStart_1212594 : Nat := 118140960795 + 1212594 * 2 ^ 59
def prefixEnd_1212594 : Nat := 4983230072969 + 3 ^ 40 * 1212594 * 2
def baseEnd_1212594 : Nat := 276730471448059535154839

theorem tailTrace_1212594 : CollatzResearch.WordTrace tailWord_1212594 prefixEnd_1212594 276730471448059535154839 := by
  unfold tailWord_1212594
  simp only [CollatzResearch.WordTrace]
  refine ⟨11056734142246626853167209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29484624379324338275112557 11056734142246626853167209)
  ·
    refine ⟨8292550606684970139875407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11056734142246626853167209 8292550606684970139875407)
    ·
      refine ⟨12438825910027455209813111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8292550606684970139875407 12438825910027455209813111)
      ·
        refine ⟨18658238865041182814719667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12438825910027455209813111 18658238865041182814719667)
        ·
          refine ⟨27987358297561774222079501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18658238865041182814719667 27987358297561774222079501)
          ·
            refine ⟨10495259361585665333279813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27987358297561774222079501 10495259361585665333279813)
            ·
              refine ⟨1967861130297312249989965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10495259361585665333279813 1967861130297312249989965)
              ·
                refine ⟨737947923861492093746237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1967861130297312249989965 737947923861492093746237)
                ·
                  refine ⟨276730471448059535154839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 737947923861492093746237 276730471448059535154839)
                  ·
                    rfl

theorem cell21_1212594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_1212594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212594 prefixEnd_1212594 := by exact prefixLift 1212594
  have htrace : WordTrace (prefixWord ++ tailWord_1212594) baseStart_1212594 baseEnd_1212594 := by
    simpa [prefixWord, tailWord_1212594, baseEnd_1212594] using wordTrace_append hprefix tailTrace_1212594
  have hstable : (prefixWord ++ tailWord_1212594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212594).length < 2 ^ (prefixWord ++ tailWord_1212594).sum := by decide
  have hdescent : baseEnd_1212594 < baseStart_1212594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212608 : List Nat := [2, 1, 1, 2, 5, 1, 3, 2, 4]
def baseStart_1212608 : Nat := 118140960795 + 1212608 * 2 ^ 59
def prefixEnd_1212608 : Nat := 4983230072969 + 3 ^ 40 * 1212608 * 2
def baseEnd_1212608 : Nat := 276733666438798621921477

theorem tailTrace_1212608 : CollatzResearch.WordTrace tailWord_1212608 prefixEnd_1212608 276733666438798621921477 := by
  unfold tailWord_1212608
  simp only [CollatzResearch.WordTrace]
  refine ⟨22113723595467893901839239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29484964793957191869118985 22113723595467893901839239)
  ·
    refine ⟨33170585393201840852758859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22113723595467893901839239 33170585393201840852758859)
    ·
      refine ⟨49755878089802761279138289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33170585393201840852758859 49755878089802761279138289)
      ·
        refine ⟨37316908567352070959353717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49755878089802761279138289 37316908567352070959353717)
        ·
          refine ⟨3498460178189256652439411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37316908567352070959353717 3498460178189256652439411)
          ·
            refine ⟨5247690267283884978659117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3498460178189256652439411 5247690267283884978659117)
            ·
              refine ⟨1967883850231456866997169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5247690267283884978659117 1967883850231456866997169)
              ·
                refine ⟨1475912887673592650247877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1967883850231456866997169 1475912887673592650247877)
                ·
                  refine ⟨276733666438798621921477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1475912887673592650247877 276733666438798621921477)
                  ·
                    rfl

theorem cell21_1212608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_1212608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212608 prefixEnd_1212608 := by exact prefixLift 1212608
  have htrace : WordTrace (prefixWord ++ tailWord_1212608) baseStart_1212608 baseEnd_1212608 := by
    simpa [prefixWord, tailWord_1212608, baseEnd_1212608] using wordTrace_append hprefix tailTrace_1212608
  have hstable : (prefixWord ++ tailWord_1212608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212608).length < 2 ^ (prefixWord ++ tailWord_1212608).sum := by decide
  have hdescent : baseEnd_1212608 < baseStart_1212608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212681 : List Nat := [1, 2, 1, 1, 3, 4, 1, 8]
def baseStart_1212681 : Nat := 118140960795 + 1212681 * 2 ^ 59
def prefixEnd_1212681 : Nat := 4983230072969 + 3 ^ 40 * 1212681 * 2
def baseEnd_1212681 : Nat := 92250108677788905734887

theorem tailTrace_1212681 : CollatzResearch.WordTrace tailWord_1212681 prefixEnd_1212681 92250108677788905734887 := by
  unfold tailWord_1212681
  simp only [CollatzResearch.WordTrace]
  refine ⟨44230109719671321271085897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29486739813114214180723931 44230109719671321271085897)
  ·
    refine ⟨33172582289753490953314423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44230109719671321271085897 33172582289753490953314423)
    ·
      refine ⟨49758873434630236429971635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33172582289753490953314423 49758873434630236429971635)
      ·
        refine ⟨74638310151945354644957453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49758873434630236429971635 74638310151945354644957453)
        ·
          refine ⟨27989366306979507991859045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 74638310151945354644957453 27989366306979507991859045)
          ·
            refine ⟨5248006182558657748473571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27989366306979507991859045 5248006182558657748473571)
            ·
              refine ⟨7872009273837986622710357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5248006182558657748473571 7872009273837986622710357)
              ·
                refine ⟨92250108677788905734887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7872009273837986622710357 92250108677788905734887)
                ·
                  rfl

theorem cell21_1212681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 8].length) (baseStart_1212681 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212681 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212681 prefixEnd_1212681 := by exact prefixLift 1212681
  have htrace : WordTrace (prefixWord ++ tailWord_1212681) baseStart_1212681 baseEnd_1212681 := by
    simpa [prefixWord, tailWord_1212681, baseEnd_1212681] using wordTrace_append hprefix tailTrace_1212681
  have hstable : (prefixWord ++ tailWord_1212681).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212681).length < 2 ^ (prefixWord ++ tailWord_1212681).sum := by decide
  have hdescent : baseEnd_1212681 < baseStart_1212681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212718 : List Nat := [4, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_1212718 : Nat := 118140960795 + 1212718 * 2 ^ 59
def prefixEnd_1212718 : Nat := 4983230072969 + 3 ^ 40 * 1212718 * 2
def baseEnd_1212718 : Nat := 276758769937462875087919

theorem tailTrace_1212718 : CollatzResearch.WordTrace tailWord_1212718 prefixEnd_1212718 276758769937462875087919 := by
  unfold tailWord_1212718
  simp only [CollatzResearch.WordTrace]
  refine ⟨5528932402567159573772851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29487639480358184393455205 5528932402567159573772851)
  ·
    refine ⟨8293398603850739360659277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5528932402567159573772851 8293398603850739360659277)
    ·
      refine ⟨3110024476444027260247229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8293398603850739360659277 3110024476444027260247229)
      ·
        refine ⟨1166259178666510222592711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3110024476444027260247229 1166259178666510222592711)
        ·
          refine ⟨1749388767999765333889067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1166259178666510222592711 1749388767999765333889067)
          ·
            refine ⟨2624083151999648000833601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1749388767999765333889067 2624083151999648000833601)
            ·
              refine ⟨1968062363999736000625201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2624083151999648000833601 1968062363999736000625201)
              ·
                refine ⟨1476046772999802000468901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1968062363999736000625201 1476046772999802000468901)
                ·
                  refine ⟨276758769937462875087919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1476046772999802000468901 276758769937462875087919)
                  ·
                    rfl

theorem cell21_1212718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_1212718 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212718 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212718 prefixEnd_1212718 := by exact prefixLift 1212718
  have htrace : WordTrace (prefixWord ++ tailWord_1212718) baseStart_1212718 baseEnd_1212718 := by
    simpa [prefixWord, tailWord_1212718, baseEnd_1212718] using wordTrace_append hprefix tailTrace_1212718
  have hstable : (prefixWord ++ tailWord_1212718).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212718).length < 2 ^ (prefixWord ++ tailWord_1212718).sum := by decide
  have hdescent : baseEnd_1212718 < baseStart_1212718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212743 : List Nat := [1, 1, 4, 1, 2, 2, 1, 5, 4]
def baseStart_1212743 : Nat := 118140960795 + 1212743 * 2 ^ 59
def prefixEnd_1212743 : Nat := 4983230072969 + 3 ^ 40 * 1212743 * 2
def baseEnd_1212743 : Nat := 276764475278068387171201

theorem tailTrace_1212743 : CollatzResearch.WordTrace tailWord_1212743 prefixEnd_1212743 276764475278068387171201 := by
  unfold tailWord_1212743
  simp only [CollatzResearch.WordTrace]
  refine ⟨44232371045446705859842883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29488247363631137239895255 44232371045446705859842883)
  ·
    refine ⟨66348556568170058789764325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44232371045446705859842883 66348556568170058789764325)
    ·
      refine ⟨12440354356531886023080811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66348556568170058789764325 12440354356531886023080811)
      ·
        refine ⟨18660531534797829034621217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12440354356531886023080811 18660531534797829034621217)
        ·
          refine ⟨13995398651098371775965913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18660531534797829034621217 13995398651098371775965913)
          ·
            refine ⟨10496548988323778831974435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13995398651098371775965913 10496548988323778831974435)
            ·
              refine ⟨15744823482485668247961653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10496548988323778831974435 15744823482485668247961653)
              ·
                refine ⟨1476077201483031398246405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15744823482485668247961653 1476077201483031398246405)
                ·
                  refine ⟨276764475278068387171201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1476077201483031398246405 276764475278068387171201)
                  ·
                    rfl

theorem cell21_1212743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 5, 4].length) (baseStart_1212743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212743 prefixEnd_1212743 := by exact prefixLift 1212743
  have htrace : WordTrace (prefixWord ++ tailWord_1212743) baseStart_1212743 baseEnd_1212743 := by
    simpa [prefixWord, tailWord_1212743, baseEnd_1212743] using wordTrace_append hprefix tailTrace_1212743
  have hstable : (prefixWord ++ tailWord_1212743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212743).length < 2 ^ (prefixWord ++ tailWord_1212743).sum := by decide
  have hdescent : baseEnd_1212743 < baseStart_1212743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212839 : List Nat := [1, 1, 6, 1, 1, 3, 3, 2, 3]
def baseStart_1212839 : Nat := 118140960795 + 1212839 * 2 ^ 59
def prefixEnd_1212839 : Nat := 4983230072969 + 3 ^ 40 * 1212839 * 2
def baseEnd_1212839 : Nat := 276786383785993553571005

theorem tailTrace_1212839 : CollatzResearch.WordTrace tailWord_1212839 prefixEnd_1212839 276786383785993553571005 := by
  unfold tailWord_1212839
  simp only [CollatzResearch.WordTrace]
  refine ⟨44235872453098914255337571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29490581635399276170225047 44235872453098914255337571)
  ·
    refine ⟨66353808679648371383006357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44235872453098914255337571 66353808679648371383006357)
    ·
      refine ⟨3110334781858517408578423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66353808679648371383006357 3110334781858517408578423)
      ·
        refine ⟨4665502172787776112867635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3110334781858517408578423 4665502172787776112867635)
        ·
          refine ⟨6998253259181664169301453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4665502172787776112867635 6998253259181664169301453)
          ·
            refine ⟨2624344972193124063488045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6998253259181664169301453 2624344972193124063488045)
            ·
              refine ⟨984129364572421523808017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2624344972193124063488045 984129364572421523808017)
              ·
                refine ⟨738097023429316142856013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 984129364572421523808017 738097023429316142856013)
                ·
                  refine ⟨276786383785993553571005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 738097023429316142856013 276786383785993553571005)
                  ·
                    rfl

theorem cell21_1212839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 3].length) (baseStart_1212839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212839 prefixEnd_1212839 := by exact prefixLift 1212839
  have htrace : WordTrace (prefixWord ++ tailWord_1212839) baseStart_1212839 baseEnd_1212839 := by
    simpa [prefixWord, tailWord_1212839, baseEnd_1212839] using wordTrace_append hprefix tailTrace_1212839
  have hstable : (prefixWord ++ tailWord_1212839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212839).length < 2 ^ (prefixWord ++ tailWord_1212839).sum := by decide
  have hdescent : baseEnd_1212839 < baseStart_1212839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212895 : List Nat := [1, 1, 2, 3, 3, 2, 1, 4, 4]
def baseStart_1212895 : Nat := 118140960795 + 1212895 * 2 ^ 59
def prefixEnd_1212895 : Nat := 4983230072969 + 3 ^ 40 * 1212895 * 2
def baseEnd_1212895 : Nat := 276799163748949900637557

theorem tailTrace_1212895 : CollatzResearch.WordTrace tailWord_1212895 prefixEnd_1212895 276799163748949900637557 := by
  unfold tailWord_1212895
  simp only [CollatzResearch.WordTrace]
  refine ⟨44237914940896035819376139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29491943293930690546250759 44237914940896035819376139)
  ·
    refine ⟨66356872411344053729064209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44237914940896035819376139 66356872411344053729064209)
    ·
      refine ⟨49767654308508040296798157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66356872411344053729064209 49767654308508040296798157)
      ·
        refine ⟨18662870365690515111299309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49767654308508040296798157 18662870365690515111299309)
        ·
          refine ⟨6998576387133943166737241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18662870365690515111299309 6998576387133943166737241)
          ·
            refine ⟨5248932290350457375052931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6998576387133943166737241 5248932290350457375052931)
            ·
              refine ⟨7873398435525686062579397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5248932290350457375052931 7873398435525686062579397)
              ·
                refine ⟨1476262206661066136733637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7873398435525686062579397 1476262206661066136733637)
                ·
                  refine ⟨276799163748949900637557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1476262206661066136733637 276799163748949900637557)
                  ·
                    rfl

theorem cell21_1212895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 4].length) (baseStart_1212895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212895 prefixEnd_1212895 := by exact prefixLift 1212895
  have htrace : WordTrace (prefixWord ++ tailWord_1212895) baseStart_1212895 baseEnd_1212895 := by
    simpa [prefixWord, tailWord_1212895, baseEnd_1212895] using wordTrace_append hprefix tailTrace_1212895
  have hstable : (prefixWord ++ tailWord_1212895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212895).length < 2 ^ (prefixWord ++ tailWord_1212895).sum := by decide
  have hdescent : baseEnd_1212895 < baseStart_1212895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212957 : List Nat := [1, 4, 2, 2, 1, 3, 2, 1, 5]
def baseStart_1212957 : Nat := 118140960795 + 1212957 * 2 ^ 59
def prefixEnd_1212957 : Nat := 4983230072969 + 3 ^ 40 * 1212957 * 2
def baseEnd_1212957 : Nat := 276813312993651570604097

theorem tailTrace_1212957 : CollatzResearch.WordTrace tailWord_1212957 prefixEnd_1212957 276813312993651570604097 := by
  unfold tailWord_1212957
  simp only [CollatzResearch.WordTrace]
  refine ⟨44240176266671420408133125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29493450844447613605422083 44240176266671420408133125)
  ·
    refine ⟨8295033050000891326524961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44240176266671420408133125 8295033050000891326524961)
    ·
      refine ⟨6221274787500668494893721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8295033050000891326524961 6221274787500668494893721)
      ·
        refine ⟨4665956090625501371170291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6221274787500668494893721 4665956090625501371170291)
        ·
          refine ⟨6998934135938252056755437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4665956090625501371170291 6998934135938252056755437)
          ·
            refine ⟨2624600300976844521283289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6998934135938252056755437 2624600300976844521283289)
            ·
              refine ⟨1968450225732633390962467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2624600300976844521283289 1968450225732633390962467)
              ·
                refine ⟨2952675338598950086443701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1968450225732633390962467 2952675338598950086443701)
                ·
                  refine ⟨276813312993651570604097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2952675338598950086443701 276813312993651570604097)
                  ·
                    rfl

theorem cell21_1212957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_1212957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212957 prefixEnd_1212957 := by exact prefixLift 1212957
  have htrace : WordTrace (prefixWord ++ tailWord_1212957) baseStart_1212957 baseEnd_1212957 := by
    simpa [prefixWord, tailWord_1212957, baseEnd_1212957] using wordTrace_append hprefix tailTrace_1212957
  have hstable : (prefixWord ++ tailWord_1212957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212957).length < 2 ^ (prefixWord ++ tailWord_1212957).sum := by decide
  have hdescent : baseEnd_1212957 < baseStart_1212957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1212985 : List Nat := [1, 2, 1, 5, 1, 1, 3, 7]
def baseStart_1212985 : Nat := 118140960795 + 1212985 * 2 ^ 59
def prefixEnd_1212985 : Nat := 4983230072969 + 3 ^ 40 * 1212985 * 2
def baseEnd_1212985 : Nat := 92273234325043248045791

theorem tailTrace_1212985 : CollatzResearch.WordTrace tailWord_1212985 prefixEnd_1212985 92273234325043248045791 := by
  unfold tailWord_1212985
  simp only [CollatzResearch.WordTrace]
  refine ⟨44241197510569981190152409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29494131673713320793434939 44241197510569981190152409)
  ·
    refine ⟨33180898132927485892614307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44241197510569981190152409 33180898132927485892614307)
    ·
      refine ⟨49771347199391228838921461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33180898132927485892614307 49771347199391228838921461)
      ·
        refine ⟨4666063799942927703648887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49771347199391228838921461 4666063799942927703648887)
        ·
          refine ⟨6999095699914391555473331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4666063799942927703648887 6999095699914391555473331)
          ·
            refine ⟨10498643549871587333209997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6999095699914391555473331 10498643549871587333209997)
            ·
              refine ⟨3936991331201845249953749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10498643549871587333209997 3936991331201845249953749)
              ·
                refine ⟨92273234325043248045791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3936991331201845249953749 92273234325043248045791)
                ·
                  rfl

theorem cell21_1212985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 7].length) (baseStart_1212985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1212985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1212985 prefixEnd_1212985 := by exact prefixLift 1212985
  have htrace : WordTrace (prefixWord ++ tailWord_1212985) baseStart_1212985 baseEnd_1212985 := by
    simpa [prefixWord, tailWord_1212985, baseEnd_1212985] using wordTrace_append hprefix tailTrace_1212985
  have hstable : (prefixWord ++ tailWord_1212985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1212985).length < 2 ^ (prefixWord ++ tailWord_1212985).sum := by decide
  have hdescent : baseEnd_1212985 < baseStart_1212985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1212985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213016 : List Nat := [2, 1, 2, 2, 1, 2, 5, 1, 5]
def baseStart_1213016 : Nat := 118140960795 + 1213016 * 2 ^ 59
def prefixEnd_1213016 : Nat := 4983230072969 + 3 ^ 40 * 1213016 * 2
def baseEnd_1213016 : Nat := 276826777597480579120643

theorem tailTrace_1213016 : CollatzResearch.WordTrace tailWord_1213016 prefixEnd_1213016 276826777597480579120643 := by
  unfold tailWord_1213016
  simp only [CollatzResearch.WordTrace]
  refine ⟨22121164086728836742265451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29494885448971782323020601 22121164086728836742265451)
  ·
    refine ⟨33181746130093255113398177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22121164086728836742265451 33181746130093255113398177)
    ·
      refine ⟨24886309597569941335048633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33181746130093255113398177 24886309597569941335048633)
      ·
        refine ⟨18664732198177456001286475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24886309597569941335048633 18664732198177456001286475)
        ·
          refine ⟨27997098297266184001929713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18664732198177456001286475 27997098297266184001929713)
          ·
            refine ⟨20997823722949638001447285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27997098297266184001929713 20997823722949638001447285)
            ·
              refine ⟨1968545974026528562635683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20997823722949638001447285 1968545974026528562635683)
              ·
                refine ⟨2952818961039792843953525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1968545974026528562635683 2952818961039792843953525)
                ·
                  refine ⟨276826777597480579120643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2952818961039792843953525 276826777597480579120643)
                  ·
                    rfl

theorem cell21_1213016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 5, 1, 5].length) (baseStart_1213016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213016 prefixEnd_1213016 := by exact prefixLift 1213016
  have htrace : WordTrace (prefixWord ++ tailWord_1213016) baseStart_1213016 baseEnd_1213016 := by
    simpa [prefixWord, tailWord_1213016, baseEnd_1213016] using wordTrace_append hprefix tailTrace_1213016
  have hstable : (prefixWord ++ tailWord_1213016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213016).length < 2 ^ (prefixWord ++ tailWord_1213016).sum := by decide
  have hdescent : baseEnd_1213016 < baseStart_1213016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213092 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 5]
def baseStart_1213092 : Nat := 118140960795 + 1213092 * 2 ^ 59
def prefixEnd_1213092 : Nat := 4983230072969 + 3 ^ 40 * 1213092 * 2
def baseEnd_1213092 : Nat := 276844121832921335853821

theorem tailTrace_1213092 : CollatzResearch.WordTrace tailWord_1213092 prefixEnd_1213092 276844121832921335853821 := by
  unfold tailWord_1213092
  simp only [CollatzResearch.WordTrace]
  refine ⟨22122550060591169232148765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29496733414121558976198353 22122550060591169232148765)
  ·
    refine ⟨8295956272721688462055787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22122550060591169232148765 8295956272721688462055787)
    ·
      refine ⟨12443934409082532693083681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8295956272721688462055787 12443934409082532693083681)
      ·
        refine ⟨9332950806811899519812761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12443934409082532693083681 9332950806811899519812761)
        ·
          refine ⟨6999713105108924639859571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9332950806811899519812761 6999713105108924639859571)
          ·
            refine ⟨10499569657663386959789357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6999713105108924639859571 10499569657663386959789357)
            ·
              refine ⟨3937338621623770109921009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10499569657663386959789357 3937338621623770109921009)
              ·
                refine ⟨2953003966217827582440757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3937338621623770109921009 2953003966217827582440757)
                ·
                  refine ⟨276844121832921335853821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2953003966217827582440757 276844121832921335853821)
                  ·
                    rfl

theorem cell21_1213092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_1213092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213092 prefixEnd_1213092 := by exact prefixLift 1213092
  have htrace : WordTrace (prefixWord ++ tailWord_1213092) baseStart_1213092 baseEnd_1213092 := by
    simpa [prefixWord, tailWord_1213092, baseEnd_1213092] using wordTrace_append hprefix tailTrace_1213092
  have hstable : (prefixWord ++ tailWord_1213092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213092).length < 2 ^ (prefixWord ++ tailWord_1213092).sum := by decide
  have hdescent : baseEnd_1213092 < baseStart_1213092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213106 : List Nat := [3, 2, 1, 1, 1, 2, 1, 4, 6]
def baseStart_1213106 : Nat := 118140960795 + 1213106 * 2 ^ 59
def prefixEnd_1213106 : Nat := 4983230072969 + 3 ^ 40 * 1213106 * 2
def baseEnd_1213106 : Nat := 276847316823660422620459

theorem tailTrace_1213106 : CollatzResearch.WordTrace tailWord_1213106 prefixEnd_1213106 276847316823660422620459 := by
  unfold tailWord_1213106
  simp only [CollatzResearch.WordTrace]
  refine ⟨11061402685782904713826793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29497073828754412570204781 11061402685782904713826793)
  ·
    refine ⟨8296052014337178535370095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11061402685782904713826793 8296052014337178535370095)
    ·
      refine ⟨12444078021505767803055143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8296052014337178535370095 12444078021505767803055143)
      ·
        refine ⟨18666117032258651704582715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12444078021505767803055143 18666117032258651704582715)
        ·
          refine ⟨27999175548387977556874073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18666117032258651704582715 27999175548387977556874073)
          ·
            refine ⟨20999381661290983167655555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27999175548387977556874073 20999381661290983167655555)
            ·
              refine ⟨31499072491936474751483333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20999381661290983167655555 31499072491936474751483333)
              ·
                refine ⟨5906076092238089015903125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31499072491936474751483333 5906076092238089015903125)
                ·
                  refine ⟨276847316823660422620459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5906076092238089015903125 276847316823660422620459)
                  ·
                    rfl

theorem cell21_1213106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_1213106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213106 prefixEnd_1213106 := by exact prefixLift 1213106
  have htrace : WordTrace (prefixWord ++ tailWord_1213106) baseStart_1213106 baseEnd_1213106 := by
    simpa [prefixWord, tailWord_1213106, baseEnd_1213106] using wordTrace_append hprefix tailTrace_1213106
  have hstable : (prefixWord ++ tailWord_1213106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213106).length < 2 ^ (prefixWord ++ tailWord_1213106).sum := by decide
  have hdescent : baseEnd_1213106 < baseStart_1213106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213236 : List Nat := [2, 5, 1, 1, 3, 2, 2, 2, 3]
def baseStart_1213236 : Nat := 118140960795 + 1213236 * 2 ^ 59
def prefixEnd_1213236 : Nat := 4983230072969 + 3 ^ 40 * 1213236 * 2
def baseEnd_1213236 : Nat := 276876984594809085453527

theorem tailTrace_1213236 : CollatzResearch.WordTrace tailWord_1213236 prefixEnd_1213236 276876984594809085453527 := by
  unfold tailWord_1213236
  simp only [CollatzResearch.WordTrace]
  refine ⟨22125176116330325528769781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29500234821773767371693041 22125176116330325528769781)
  ·
    refine ⟨2074235260905968018322167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22125176116330325528769781 2074235260905968018322167)
    ·
      refine ⟨3111352891358952027483251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2074235260905968018322167 3111352891358952027483251)
      ·
        refine ⟨4667029337038428041224877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3111352891358952027483251 4667029337038428041224877)
        ·
          refine ⟨1750136001389410515459329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4667029337038428041224877 1750136001389410515459329)
          ·
            refine ⟨1312602001042057886594497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1750136001389410515459329 1312602001042057886594497)
            ·
              refine ⟨984451500781543414945873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1312602001042057886594497 984451500781543414945873)
              ·
                refine ⟨738338625586157561209405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 984451500781543414945873 738338625586157561209405)
                ·
                  refine ⟨276876984594809085453527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 738338625586157561209405 276876984594809085453527)
                  ·
                    rfl

theorem cell21_1213236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_1213236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213236 prefixEnd_1213236 := by exact prefixLift 1213236
  have htrace : WordTrace (prefixWord ++ tailWord_1213236) baseStart_1213236 baseEnd_1213236 := by
    simpa [prefixWord, tailWord_1213236, baseEnd_1213236] using wordTrace_append hprefix tailTrace_1213236
  have hstable : (prefixWord ++ tailWord_1213236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213236).length < 2 ^ (prefixWord ++ tailWord_1213236).sum := by decide
  have hdescent : baseEnd_1213236 < baseStart_1213236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213272 : List Nat := [2, 1, 2, 2, 1, 1, 1, 11]
def baseStart_1213272 : Nat := 118140960795 + 1213272 * 2 ^ 59
def prefixEnd_1213272 : Nat := 4983230072969 + 3 ^ 40 * 1213272 * 2
def baseEnd_1213272 : Nat := 92295066761760340951151

theorem tailTrace_1213272 : CollatzResearch.WordTrace tailWord_1213272 prefixEnd_1213272 92295066761760340951151 := by
  unfold tailWord_1213272
  simp only [CollatzResearch.WordTrace]
  refine ⟨22125832630265114602925035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29501110173686819470566713 22125832630265114602925035)
  ·
    refine ⟨33188748945397671904387553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22125832630265114602925035 33188748945397671904387553)
    ·
      refine ⟨24891561709048253928290665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33188748945397671904387553 24891561709048253928290665)
      ·
        refine ⟨18668671281786190446217999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24891561709048253928290665 18668671281786190446217999)
        ·
          refine ⟨28003006922679285669326999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18668671281786190446217999 28003006922679285669326999)
          ·
            refine ⟨42004510384018928503990499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28003006922679285669326999 42004510384018928503990499)
            ·
              refine ⟨63006765576028392755985749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42004510384018928503990499 63006765576028392755985749)
              ·
                refine ⟨92295066761760340951151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 63006765576028392755985749 92295066761760340951151)
                ·
                  rfl

theorem cell21_1213272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 11].length) (baseStart_1213272 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213272 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213272 prefixEnd_1213272 := by exact prefixLift 1213272
  have htrace : WordTrace (prefixWord ++ tailWord_1213272) baseStart_1213272 baseEnd_1213272 := by
    simpa [prefixWord, tailWord_1213272, baseEnd_1213272] using wordTrace_append hprefix tailTrace_1213272
  have hstable : (prefixWord ++ tailWord_1213272).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213272).length < 2 ^ (prefixWord ++ tailWord_1213272).sum := by decide
  have hdescent : baseEnd_1213272 < baseStart_1213272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213320 : List Nat := [2, 1, 3, 3, 2, 1, 2, 2, 5]
def baseStart_1213320 : Nat := 118140960795 + 1213320 * 2 ^ 59
def prefixEnd_1213320 : Nat := 4983230072969 + 3 ^ 40 * 1213320 * 2
def baseEnd_1213320 : Nat := 276896154539243606053355

theorem tailTrace_1213320 : CollatzResearch.WordTrace tailWord_1213320 prefixEnd_1213320 276896154539243606053355 := by
  unfold tailWord_1213320
  simp only [CollatzResearch.WordTrace]
  refine ⟨22126707982178166701798707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29502277309570888935731609 22126707982178166701798707)
  ·
    refine ⟨33190061973267250052698061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22126707982178166701798707 33190061973267250052698061)
    ·
      refine ⟨12446273239975218769761773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33190061973267250052698061 12446273239975218769761773)
      ·
        refine ⟨4667352464990707038660665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12446273239975218769761773 4667352464990707038660665)
        ·
          refine ⟨3500514348743030278995499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4667352464990707038660665 3500514348743030278995499)
          ·
            refine ⟨5250771523114545418493249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3500514348743030278995499 5250771523114545418493249)
            ·
              refine ⟨3938078642335909063869937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5250771523114545418493249 3938078642335909063869937)
              ·
                refine ⟨2953558981751931797902453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3938078642335909063869937 2953558981751931797902453)
                ·
                  refine ⟨276896154539243606053355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2953558981751931797902453 276896154539243606053355)
                  ·
                    rfl

theorem cell21_1213320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_1213320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213320 prefixEnd_1213320 := by exact prefixLift 1213320
  have htrace : WordTrace (prefixWord ++ tailWord_1213320) baseStart_1213320 baseEnd_1213320 := by
    simpa [prefixWord, tailWord_1213320, baseEnd_1213320] using wordTrace_append hprefix tailTrace_1213320
  have hstable : (prefixWord ++ tailWord_1213320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213320).length < 2 ^ (prefixWord ++ tailWord_1213320).sum := by decide
  have hdescent : baseEnd_1213320 < baseStart_1213320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213365 : List Nat := [1, 3, 3, 2, 1, 1, 4, 6]
def baseStart_1213365 : Nat := 118140960795 + 1213365 * 2 ^ 59
def prefixEnd_1213365 : Nat := 4983230072969 + 3 ^ 40 * 1213365 * 2
def baseEnd_1213365 : Nat := 92302141384111175934421

theorem tailTrace_1213365 : CollatzResearch.WordTrace tailWord_1213365 prefixEnd_1213365 92302141384111175934421 := by
  unfold tailWord_1213365
  simp only [CollatzResearch.WordTrace]
  refine ⟨44255057249193306088985549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29503371499462204059323699 44255057249193306088985549)
  ·
    refine ⟨16595646468447489783369581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44255057249193306088985549 16595646468447489783369581)
    ·
      refine ⟨6223367425667808668763593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16595646468447489783369581 6223367425667808668763593)
      ·
        refine ⟨4667525569250856501572695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6223367425667808668763593 4667525569250856501572695)
        ·
          refine ⟨7001288353876284752359043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4667525569250856501572695 7001288353876284752359043)
          ·
            refine ⟨10501932530814427128538565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7001288353876284752359043 10501932530814427128538565)
            ·
              refine ⟨1969112349527705086600981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10501932530814427128538565 1969112349527705086600981)
              ·
                refine ⟨92302141384111175934421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1969112349527705086600981 92302141384111175934421)
                ·
                  rfl

theorem cell21_1213365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 6].length) (baseStart_1213365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213365 prefixEnd_1213365 := by exact prefixLift 1213365
  have htrace : WordTrace (prefixWord ++ tailWord_1213365) baseStart_1213365 baseEnd_1213365 := by
    simpa [prefixWord, tailWord_1213365, baseEnd_1213365] using wordTrace_append hprefix tailTrace_1213365
  have hstable : (prefixWord ++ tailWord_1213365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213365).length < 2 ^ (prefixWord ++ tailWord_1213365).sum := by decide
  have hdescent : baseEnd_1213365 < baseStart_1213365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213368 : List Nat := [2, 1, 2, 1, 2, 6, 2, 1, 4]
def baseStart_1213368 : Nat := 118140960795 + 1213368 * 2 ^ 59
def prefixEnd_1213368 : Nat := 4983230072969 + 3 ^ 40 * 1213368 * 2
def baseEnd_1213368 : Nat := 276907108793206189253257

theorem tailTrace_1213368 : CollatzResearch.WordTrace tailWord_1213368 prefixEnd_1213368 276907108793206189253257 := by
  unfold tailWord_1213368
  simp only [CollatzResearch.WordTrace]
  refine ⟨22127583334091218800672379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29503444445454958400896505 22127583334091218800672379)
  ·
    refine ⟨33191375001136828201008569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22127583334091218800672379 33191375001136828201008569)
    ·
      refine ⟨24893531250852621150756427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33191375001136828201008569 24893531250852621150756427)
      ·
        refine ⟨37340296876278931726134641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24893531250852621150756427 37340296876278931726134641)
        ·
          refine ⟨28005222657209198794600981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37340296876278931726134641 28005222657209198794600981)
          ·
            refine ⟨1312744812056681193496921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28005222657209198794600981 1312744812056681193496921)
            ·
              refine ⟨984558609042510895122691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1312744812056681193496921 984558609042510895122691)
              ·
                refine ⟨1476837913563766342684037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 984558609042510895122691 1476837913563766342684037)
                ·
                  refine ⟨276907108793206189253257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1476837913563766342684037 276907108793206189253257)
                  ·
                    rfl

theorem cell21_1213368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 4].length) (baseStart_1213368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213368 prefixEnd_1213368 := by exact prefixLift 1213368
  have htrace : WordTrace (prefixWord ++ tailWord_1213368) baseStart_1213368 baseEnd_1213368 := by
    simpa [prefixWord, tailWord_1213368, baseEnd_1213368] using wordTrace_append hprefix tailTrace_1213368
  have hstable : (prefixWord ++ tailWord_1213368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213368).length < 2 ^ (prefixWord ++ tailWord_1213368).sum := by decide
  have hdescent : baseEnd_1213368 < baseStart_1213368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213517 : List Nat := [1, 6, 1, 1, 1, 2, 9]
def baseStart_1213517 : Nat := 118140960795 + 1213517 * 2 ^ 59
def prefixEnd_1213517 : Nat := 4983230072969 + 3 ^ 40 * 1213517 * 2
def baseEnd_1213517 : Nat := 30771234735912782363291

theorem tailTrace_1213517 : CollatzResearch.WordTrace tailWord_1213517 prefixEnd_1213517 30771234735912782363291 := by
  unfold tailWord_1213517
  simp only [CollatzResearch.WordTrace]
  refine ⟨44260601144642636048518805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29507067429761757365679203 44260601144642636048518805)
  ·
    refine ⟨2074715678655123564774319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 44260601144642636048518805 2074715678655123564774319)
    ·
      refine ⟨3112073517982685347161479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2074715678655123564774319 3112073517982685347161479)
      ·
        refine ⟨4668110276974028020742219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3112073517982685347161479 4668110276974028020742219)
        ·
          refine ⟨7002165415461042031113329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4668110276974028020742219 7002165415461042031113329)
          ·
            refine ⟨5251624061595781523334997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7002165415461042031113329 5251624061595781523334997)
            ·
              refine ⟨30771234735912782363291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5251624061595781523334997 30771234735912782363291)
              ·
                rfl

theorem cell21_1213517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 9].length) (baseStart_1213517 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213517 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213517 prefixEnd_1213517 := by exact prefixLift 1213517
  have htrace : WordTrace (prefixWord ++ tailWord_1213517) baseStart_1213517 baseEnd_1213517 := by
    simpa [prefixWord, tailWord_1213517, baseEnd_1213517] using wordTrace_append hprefix tailTrace_1213517
  have hstable : (prefixWord ++ tailWord_1213517).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213517).length < 2 ^ (prefixWord ++ tailWord_1213517).sum := by decide
  have hdescent : baseEnd_1213517 < baseStart_1213517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213576 : List Nat := [2, 1, 3, 4, 11]
def baseStart_1213576 : Nat := 118140960795 + 1213576 * 2 ^ 59
def prefixEnd_1213576 : Nat := 4983230072969 + 3 ^ 40 * 1213576 * 2
def baseEnd_1213576 : Nat := 3419192311444988268965

theorem tailTrace_1213576 : CollatzResearch.WordTrace tailWord_1213576 prefixEnd_1213576 3419192311444988268965 := by
  unfold tailWord_1213576
  simp only [CollatzResearch.WordTrace]
  refine ⟨22131376525714444562458291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29508502034285926083277721 22131376525714444562458291)
  ·
    refine ⟨33197064788571666843687437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22131376525714444562458291 33197064788571666843687437)
    ·
      refine ⟨12448899295714375066382789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33197064788571666843687437 12448899295714375066382789)
      ·
        refine ⟨2334168617946445324946773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12448899295714375066382789 2334168617946445324946773)
        ·
          refine ⟨3419192311444988268965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2334168617946445324946773 3419192311444988268965)
          ·
            rfl

theorem cell21_1213576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 11].length) (baseStart_1213576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213576 prefixEnd_1213576 := by exact prefixLift 1213576
  have htrace : WordTrace (prefixWord ++ tailWord_1213576) baseStart_1213576 baseEnd_1213576 := by
    simpa [prefixWord, tailWord_1213576, baseEnd_1213576] using wordTrace_append hprefix tailTrace_1213576
  have hstable : (prefixWord ++ tailWord_1213576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213576).length < 2 ^ (prefixWord ++ tailWord_1213576).sum := by decide
  have hdescent : baseEnd_1213576 < baseStart_1213576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213582 : List Nat := [4, 1, 1, 3, 2, 1, 4, 2, 3]
def baseStart_1213582 : Nat := 118140960795 + 1213582 * 2 ^ 59
def prefixEnd_1213582 : Nat := 4983230072969 + 3 ^ 40 * 1213582 * 2
def baseEnd_1213582 : Nat := 276955946508789372686153

theorem tailTrace_1213582 : CollatzResearch.WordTrace tailWord_1213582 prefixEnd_1213582 276955946508789372686153 := by
  unfold tailWord_1213582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5532871486175894018704375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29508647926271434766423333 5532871486175894018704375)
  ·
    refine ⟨8299307229263841028056563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5532871486175894018704375 8299307229263841028056563)
    ·
      refine ⟨12448960843895761542084845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8299307229263841028056563 12448960843895761542084845)
      ·
        refine ⟨4668360316460910578281817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12448960843895761542084845 4668360316460910578281817)
        ·
          refine ⟨3501270237345682933711363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4668360316460910578281817 3501270237345682933711363)
          ·
            refine ⟨5251905356018524400567045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3501270237345682933711363 5251905356018524400567045)
            ·
              refine ⟨984732254253473325106321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5251905356018524400567045 984732254253473325106321)
              ·
                refine ⟨738549190690104993829741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 984732254253473325106321 738549190690104993829741)
                ·
                  refine ⟨276955946508789372686153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 738549190690104993829741 276955946508789372686153)
                  ·
                    rfl

theorem cell21_1213582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_1213582 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213582 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213582 prefixEnd_1213582 := by exact prefixLift 1213582
  have htrace : WordTrace (prefixWord ++ tailWord_1213582) baseStart_1213582 baseEnd_1213582 := by
    simpa [prefixWord, tailWord_1213582, baseEnd_1213582] using wordTrace_append hprefix tailTrace_1213582
  have hstable : (prefixWord ++ tailWord_1213582).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213582).length < 2 ^ (prefixWord ++ tailWord_1213582).sum := by decide
  have hdescent : baseEnd_1213582 < baseStart_1213582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213669 : List Nat := [1, 3, 1, 4, 3, 1, 1, 7]
def baseStart_1213669 : Nat := 118140960795 + 1213669 * 2 ^ 59
def prefixEnd_1213669 : Nat := 4983230072969 + 3 ^ 40 * 1213669 * 2
def baseEnd_1213669 : Nat := 92325267031365518245325

theorem tailTrace_1213669 : CollatzResearch.WordTrace tailWord_1213669 prefixEnd_1213669 92325267031365518245325 := by
  unfold tailWord_1213669
  simp only [CollatzResearch.WordTrace]
  refine ⟨44266145040091966008052061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29510763360061310672034707 44266145040091966008052061)
  ·
    refine ⟨16599804390034487253019523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44266145040091966008052061 16599804390034487253019523)
    ·
      refine ⟨24899706585051730879529285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16599804390034487253019523 24899706585051730879529285)
      ·
        refine ⟨4668694984697199539911741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24899706585051730879529285 4668694984697199539911741)
        ·
          refine ⟨1750760619261449827466903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4668694984697199539911741 1750760619261449827466903)
          ·
            refine ⟨2626140928892174741200355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1750760619261449827466903 2626140928892174741200355)
            ·
              refine ⟨3939211393338262111800533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2626140928892174741200355 3939211393338262111800533)
              ·
                refine ⟨92325267031365518245325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3939211393338262111800533 92325267031365518245325)
                ·
                  rfl

theorem cell21_1213669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 7].length) (baseStart_1213669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213669 prefixEnd_1213669 := by exact prefixLift 1213669
  have htrace : WordTrace (prefixWord ++ tailWord_1213669) baseStart_1213669 baseEnd_1213669 := by
    simpa [prefixWord, tailWord_1213669, baseEnd_1213669] using wordTrace_append hprefix tailTrace_1213669
  have hstable : (prefixWord ++ tailWord_1213669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213669).length < 2 ^ (prefixWord ++ tailWord_1213669).sum := by decide
  have hdescent : baseEnd_1213669 < baseStart_1213669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213700 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 5]
def baseStart_1213700 : Nat := 118140960795 + 1213700 * 2 ^ 59
def prefixEnd_1213700 : Nat := 4983230072969 + 3 ^ 40 * 1213700 * 2
def baseEnd_1213700 : Nat := 276982875716447389719245

theorem tailTrace_1213700 : CollatzResearch.WordTrace tailWord_1213700 prefixEnd_1213700 276982875716447389719245 := by
  unfold tailWord_1213700
  simp only [CollatzResearch.WordTrace]
  refine ⟨22133637851489829151215277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29511517135319772201620369 22133637851489829151215277)
  ·
    refine ⟨8300114194308685931705729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22133637851489829151215277 8300114194308685931705729)
    ·
      refine ⟨6225085645731514448779297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8300114194308685931705729 6225085645731514448779297)
      ·
        refine ⟨4668814234298635836584473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6225085645731514448779297 4668814234298635836584473)
        ·
          refine ⟨3501610675723976877438355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4668814234298635836584473 3501610675723976877438355)
          ·
            refine ⟨5252416013585965316157533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3501610675723976877438355 5252416013585965316157533)
            ·
              refine ⟨1969656005094736993559075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5252416013585965316157533 1969656005094736993559075)
              ·
                refine ⟨2954484007642105490338613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969656005094736993559075 2954484007642105490338613)
                ·
                  refine ⟨276982875716447389719245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2954484007642105490338613 276982875716447389719245)
                  ·
                    rfl

theorem cell21_1213700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_1213700 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213700 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213700 prefixEnd_1213700 := by exact prefixLift 1213700
  have htrace : WordTrace (prefixWord ++ tailWord_1213700) baseStart_1213700 baseEnd_1213700 := by
    simpa [prefixWord, tailWord_1213700, baseEnd_1213700] using wordTrace_append hprefix tailTrace_1213700
  have hstable : (prefixWord ++ tailWord_1213700).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213700).length < 2 ^ (prefixWord ++ tailWord_1213700).sum := by decide
  have hdescent : baseEnd_1213700 < baseStart_1213700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213804 : List Nat := [2, 2, 1, 1, 5, 2, 8]
def baseStart_1213804 : Nat := 118140960795 + 1213804 * 2 ^ 59
def prefixEnd_1213804 : Nat := 4983230072969 + 3 ^ 40 * 1213804 * 2
def baseEnd_1213804 : Nat := 30778512214818479998411

theorem tailTrace_1213804 : CollatzResearch.WordTrace tailWord_1213804 prefixEnd_1213804 30778512214818479998411 := by
  unfold tailWord_1213804
  simp only [CollatzResearch.WordTrace]
  refine ⟨22135534447301442032108233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29514045929735256042810977 22135534447301442032108233)
  ·
    refine ⟨16601650835476081524081175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22135534447301442032108233 16601650835476081524081175)
    ·
      refine ⟨24902476253214122286121763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16601650835476081524081175 24902476253214122286121763)
      ·
        refine ⟨37353714379821183429182645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24902476253214122286121763 37353714379821183429182645)
        ·
          refine ⟨3501910723108235946485873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37353714379821183429182645 3501910723108235946485873)
          ·
            refine ⟨2626433042331176959864405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3501910723108235946485873 2626433042331176959864405)
            ·
              refine ⟨30778512214818479998411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2626433042331176959864405 30778512214818479998411)
              ·
                rfl

theorem cell21_1213804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 8].length) (baseStart_1213804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213804 prefixEnd_1213804 := by exact prefixLift 1213804
  have htrace : WordTrace (prefixWord ++ tailWord_1213804) baseStart_1213804 baseEnd_1213804 := by
    simpa [prefixWord, tailWord_1213804, baseEnd_1213804] using wordTrace_append hprefix tailTrace_1213804
  have hstable : (prefixWord ++ tailWord_1213804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213804).length < 2 ^ (prefixWord ++ tailWord_1213804).sum := by decide
  have hdescent : baseEnd_1213804 < baseStart_1213804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213818 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 9]
def baseStart_1213818 : Nat := 118140960795 + 1213818 * 2 ^ 59
def prefixEnd_1213818 : Nat := 4983230072969 + 3 ^ 40 * 1213818 * 2
def baseEnd_1213818 : Nat := 277009804924105406752337

theorem tailTrace_1213818 : CollatzResearch.WordTrace tailWord_1213818 prefixEnd_1213818 277009804924105406752337 := by
  unfold tailWord_1213818
  simp only [CollatzResearch.WordTrace]
  refine ⟨11067894879138041113806527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29514386344368109636817405 11067894879138041113806527)
  ·
    refine ⟨16601842318707061670709791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11067894879138041113806527 16601842318707061670709791)
    ·
      refine ⟨24902763478060592506064687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16601842318707061670709791 24902763478060592506064687)
      ·
        refine ⟨37354145217090888759097031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24902763478060592506064687 37354145217090888759097031)
        ·
          refine ⟨56031217825636333138645547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37354145217090888759097031 56031217825636333138645547)
          ·
            refine ⟨84046826738454499707968321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56031217825636333138645547 84046826738454499707968321)
            ·
              refine ⟨63035120053840874780976241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84046826738454499707968321 63035120053840874780976241)
              ·
                refine ⟨47276340040380656085732181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63035120053840874780976241 47276340040380656085732181)
                ·
                  refine ⟨277009804924105406752337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47276340040380656085732181 277009804924105406752337)
                  ·
                    rfl

theorem cell21_1213818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_1213818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213818 prefixEnd_1213818 := by exact prefixLift 1213818
  have htrace : WordTrace (prefixWord ++ tailWord_1213818) baseStart_1213818 baseEnd_1213818 := by
    simpa [prefixWord, tailWord_1213818, baseEnd_1213818] using wordTrace_append hprefix tailTrace_1213818
  have hstable : (prefixWord ++ tailWord_1213818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213818).length < 2 ^ (prefixWord ++ tailWord_1213818).sum := by decide
  have hdescent : baseEnd_1213818 < baseStart_1213818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213849 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 6]
def baseStart_1213849 : Nat := 118140960795 + 1213849 * 2 ^ 59
def prefixEnd_1213849 : Nat := 4983230072969 + 3 ^ 40 * 1213849 * 2
def baseEnd_1213849 : Nat := 277016879546456241735607

theorem tailTrace_1213849 : CollatzResearch.WordTrace tailWord_1213849 prefixEnd_1213849 277016879546456241735607 := by
  unfold tailWord_1213849
  simp only [CollatzResearch.WordTrace]
  refine ⟨44272710179439856749604601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29515140119626571166403067 44272710179439856749604601)
  ·
    refine ⟨33204532634579892562203451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44272710179439856749604601 33204532634579892562203451)
    ·
      refine ⟨49806798951869838843305177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33204532634579892562203451 49806798951869838843305177)
      ·
        refine ⟨37355099213902379132478883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49806798951869838843305177 37355099213902379132478883)
        ·
          refine ⟨56032648820853568698718325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37355099213902379132478883 56032648820853568698718325)
          ·
            refine ⟨5253060826955022065504843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56032648820853568698718325 5253060826955022065504843)
            ·
              refine ⟨7879591240432533098257265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5253060826955022065504843 7879591240432533098257265)
              ·
                refine ⟨5909693430324399823692949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7879591240432533098257265 5909693430324399823692949)
                ·
                  refine ⟨277016879546456241735607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5909693430324399823692949 277016879546456241735607)
                  ·
                    rfl

theorem cell21_1213849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_1213849 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213849 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213849 prefixEnd_1213849 := by exact prefixLift 1213849
  have htrace : WordTrace (prefixWord ++ tailWord_1213849) baseStart_1213849 baseEnd_1213849 := by
    simpa [prefixWord, tailWord_1213849, baseEnd_1213849] using wordTrace_append hprefix tailTrace_1213849
  have hstable : (prefixWord ++ tailWord_1213849).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213849).length < 2 ^ (prefixWord ++ tailWord_1213849).sum := by decide
  have hdescent : baseEnd_1213849 < baseStart_1213849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213869 : List Nat := [1, 5, 2, 2, 1, 3, 1, 1, 5]
def baseStart_1213869 : Nat := 118140960795 + 1213869 * 2 ^ 59
def prefixEnd_1213869 : Nat := 4983230072969 + 3 ^ 40 * 1213869 * 2
def baseEnd_1213869 : Nat := 277021443818940651402233

theorem tailTrace_1213869 : CollatzResearch.WordTrace tailWord_1213869 prefixEnd_1213869 277021443818940651402233 := by
  unfold tailWord_1213869
  simp only [CollatzResearch.WordTrace]
  refine ⟨44273439639367400165332661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29515626426244933443555107 44273439639367400165332661)
  ·
    refine ⟨4150634966190693765499937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44273439639367400165332661 4150634966190693765499937)
    ·
      refine ⟨3112976224643020324124953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4150634966190693765499937 3112976224643020324124953)
      ·
        refine ⟨2334732168482265243093715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3112976224643020324124953 2334732168482265243093715)
        ·
          refine ⟨3502098252723397864640573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2334732168482265243093715 3502098252723397864640573)
          ·
            refine ⟨1313286844771274199240215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3502098252723397864640573 1313286844771274199240215)
            ·
              refine ⟨1969930267156911298860323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313286844771274199240215 1969930267156911298860323)
              ·
                refine ⟨2954895400735366948290485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1969930267156911298860323 2954895400735366948290485)
                ·
                  refine ⟨277021443818940651402233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2954895400735366948290485 277021443818940651402233)
                  ·
                    rfl

theorem cell21_1213869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_1213869 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213869 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213869 prefixEnd_1213869 := by exact prefixLift 1213869
  have htrace : WordTrace (prefixWord ++ tailWord_1213869) baseStart_1213869 baseEnd_1213869 := by
    simpa [prefixWord, tailWord_1213869, baseEnd_1213869] using wordTrace_append hprefix tailTrace_1213869
  have hstable : (prefixWord ++ tailWord_1213869).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213869).length < 2 ^ (prefixWord ++ tailWord_1213869).sum := by decide
  have hdescent : baseEnd_1213869 < baseStart_1213869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213928 : List Nat := [2, 1, 4, 1, 1, 2, 3, 4, 3]
def baseStart_1213928 : Nat := 118140960795 + 1213928 * 2 ^ 59
def prefixEnd_1213928 : Nat := 4983230072969 + 3 ^ 40 * 1213928 * 2
def baseEnd_1213928 : Nat := 277034908422769659918779

theorem tailTrace_1213928 : CollatzResearch.WordTrace tailWord_1213928 prefixEnd_1213928 277034908422769659918779 := by
  unfold tailWord_1213928
  simp only [CollatzResearch.WordTrace]
  refine ⟨22137795773076826620865219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29517061030769102161153625 22137795773076826620865219)
  ·
    refine ⟨33206693659615239931297829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22137795773076826620865219 33206693659615239931297829)
    ·
      refine ⟨6226255061177857487118343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33206693659615239931297829 6226255061177857487118343)
      ·
        refine ⟨9339382591766786230677515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6226255061177857487118343 9339382591766786230677515)
        ·
          refine ⟨14009073887650179346016273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9339382591766786230677515 14009073887650179346016273)
          ·
            refine ⟨10506805415737634509512205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14009073887650179346016273 10506805415737634509512205)
            ·
              refine ⟨3940052030901612941067077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10506805415737634509512205 3940052030901612941067077)
              ·
                refine ⟨738759755794052426450077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3940052030901612941067077 738759755794052426450077)
                ·
                  refine ⟨277034908422769659918779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 738759755794052426450077 277034908422769659918779)
                  ·
                    rfl

theorem cell21_1213928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 4, 3].length) (baseStart_1213928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213928 prefixEnd_1213928 := by exact prefixLift 1213928
  have htrace : WordTrace (prefixWord ++ tailWord_1213928) baseStart_1213928 baseEnd_1213928 := by
    simpa [prefixWord, tailWord_1213928, baseEnd_1213928] using wordTrace_append hprefix tailTrace_1213928
  have hstable : (prefixWord ++ tailWord_1213928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213928).length < 2 ^ (prefixWord ++ tailWord_1213928).sum := by decide
  have hdescent : baseEnd_1213928 < baseStart_1213928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213939 : List Nat := [1, 1, 1, 2, 2, 2, 2, 10]
def baseStart_1213939 : Nat := 118140960795 + 1213939 * 2 ^ 59
def prefixEnd_1213939 : Nat := 4983230072969 + 3 ^ 40 * 1213939 * 2
def baseEnd_1213939 : Nat := 92345806257545361745141

theorem tailTrace_1213939 : CollatzResearch.WordTrace tailWord_1213939 prefixEnd_1213939 92345806257545361745141 := by
  unfold tailWord_1213939
  simp only [CollatzResearch.WordTrace]
  refine ⟨44275992749113802120380871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29517328499409201413587247 44275992749113802120380871)
  ·
    refine ⟨66413989123670703180571307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44275992749113802120380871 66413989123670703180571307)
    ·
      refine ⟨99620983685506054770856961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66413989123670703180571307 99620983685506054770856961)
      ·
        refine ⟨74715737764129541078142721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 99620983685506054770856961 74715737764129541078142721)
        ·
          refine ⟨56036803323097155808607041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 74715737764129541078142721 56036803323097155808607041)
          ·
            refine ⟨42027602492322866856455281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56036803323097155808607041 42027602492322866856455281)
            ·
              refine ⟨31520701869242150142341461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42027602492322866856455281 31520701869242150142341461)
              ·
                refine ⟨92345806257545361745141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31520701869242150142341461 92345806257545361745141)
                ·
                  rfl

theorem cell21_1213939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 10].length) (baseStart_1213939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213939 prefixEnd_1213939 := by exact prefixLift 1213939
  have htrace : WordTrace (prefixWord ++ tailWord_1213939) baseStart_1213939 baseEnd_1213939 := by
    simpa [prefixWord, tailWord_1213939, baseEnd_1213939] using wordTrace_append hprefix tailTrace_1213939
  have hstable : (prefixWord ++ tailWord_1213939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213939).length < 2 ^ (prefixWord ++ tailWord_1213939).sum := by decide
  have hdescent : baseEnd_1213939 < baseStart_1213939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1213976 : List Nat := [2, 1, 2, 3, 5, 1, 1, 2, 4]
def baseStart_1213976 : Nat := 118140960795 + 1213976 * 2 ^ 59
def prefixEnd_1213976 : Nat := 4983230072969 + 3 ^ 40 * 1213976 * 2
def baseEnd_1213976 : Nat := 277045862676732243118681

theorem tailTrace_1213976 : CollatzResearch.WordTrace tailWord_1213976 prefixEnd_1213976 277045862676732243118681 := by
  unfold tailWord_1213976
  simp only [CollatzResearch.WordTrace]
  refine ⟨22138671124989878719738891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29518228166653171626318521 22138671124989878719738891)
  ·
    refine ⟨33208006687484818079608337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22138671124989878719738891 33208006687484818079608337)
    ·
      refine ⟨24906005015613613559706253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33208006687484818079608337 24906005015613613559706253)
      ·
        refine ⟨9339751880855105084889845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24906005015613613559706253 9339751880855105084889845)
        ·
          refine ⟨875601738830166101708423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9339751880855105084889845 875601738830166101708423)
          ·
            refine ⟨1313402608245249152562635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 875601738830166101708423 1313402608245249152562635)
            ·
              refine ⟨1970103912367873728843953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1313402608245249152562635 1970103912367873728843953)
              ·
                refine ⟨1477577934275905296632965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1970103912367873728843953 1477577934275905296632965)
                ·
                  refine ⟨277045862676732243118681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1477577934275905296632965 277045862676732243118681)
                  ·
                    rfl

theorem cell21_1213976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 1, 2, 4].length) (baseStart_1213976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1213976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1213976 prefixEnd_1213976 := by exact prefixLift 1213976
  have htrace : WordTrace (prefixWord ++ tailWord_1213976) baseStart_1213976 baseEnd_1213976 := by
    simpa [prefixWord, tailWord_1213976, baseEnd_1213976] using wordTrace_append hprefix tailTrace_1213976
  have hstable : (prefixWord ++ tailWord_1213976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1213976).length < 2 ^ (prefixWord ++ tailWord_1213976).sum := by decide
  have hdescent : baseEnd_1213976 < baseStart_1213976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1213976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214094 : List Nat := [4, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_1214094 : Nat := 118140960795 + 1214094 * 2 ^ 59
def prefixEnd_1214094 : Nat := 4983230072969 + 3 ^ 40 * 1214094 * 2
def baseEnd_1214094 : Nat := 277072791884390260151773

theorem tailTrace_1214094 : CollatzResearch.WordTrace tailWord_1214094 prefixEnd_1214094 277072791884390260151773 := by
  unfold tailWord_1214094
  simp only [CollatzResearch.WordTrace]
  refine ⟨5535205757944032949034167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29521097375701509061515557 5535205757944032949034167)
  ·
    refine ⟨8302808636916049423551251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5535205757944032949034167 8302808636916049423551251)
    ·
      refine ⟨12454212955374074135326877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8302808636916049423551251 12454212955374074135326877)
      ·
        refine ⟨4670329858265277800747579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12454212955374074135326877 4670329858265277800747579)
        ·
          refine ⟨7005494787397916701121369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4670329858265277800747579 7005494787397916701121369)
          ·
            refine ⟨5254121090548437525841027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7005494787397916701121369 5254121090548437525841027)
            ·
              refine ⟨7881181635822656288761541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5254121090548437525841027 7881181635822656288761541)
              ·
                refine ⟨1477721556716748054142789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7881181635822656288761541 1477721556716748054142789)
                ·
                  refine ⟨277072791884390260151773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1477721556716748054142789 277072791884390260151773)
                  ·
                    rfl

theorem cell21_1214094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_1214094 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1214094 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1214094 prefixEnd_1214094 := by exact prefixLift 1214094
  have htrace : WordTrace (prefixWord ++ tailWord_1214094) baseStart_1214094 baseEnd_1214094 := by
    simpa [prefixWord, tailWord_1214094, baseEnd_1214094] using wordTrace_append hprefix tailTrace_1214094
  have hstable : (prefixWord ++ tailWord_1214094).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214094).length < 2 ^ (prefixWord ++ tailWord_1214094).sum := by decide
  have hdescent : baseEnd_1214094 < baseStart_1214094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214125 : List Nat := [1, 5, 2, 1, 1, 1, 5, 5]
def baseStart_1214125 : Nat := 118140960795 + 1214125 * 2 ^ 59
def prefixEnd_1214125 : Nat := 4983230072969 + 3 ^ 40 * 1214125 * 2
def baseEnd_1214125 : Nat := 92359955502247031711681

theorem tailTrace_1214125 : CollatzResearch.WordTrace tailWord_1214125 prefixEnd_1214125 92359955502247031711681 := by
  unfold tailWord_1214125
  simp only [CollatzResearch.WordTrace]
  refine ⟨44282776726439955886651829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29521851150959970591101219 44282776726439955886651829)
  ·
    refine ⟨4151510318103745864373609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44282776726439955886651829 4151510318103745864373609)
    ·
      refine ⟨3113632738577809398280207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4151510318103745864373609 3113632738577809398280207)
      ·
        refine ⟨4670449107866714097420311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3113632738577809398280207 4670449107866714097420311)
        ·
          refine ⟨7005673661800071146130467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4670449107866714097420311 7005673661800071146130467)
          ·
            refine ⟨10508510492700106719195701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7005673661800071146130467 10508510492700106719195701)
            ·
              refine ⟨985172858690635004924597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10508510492700106719195701 985172858690635004924597)
              ·
                refine ⟨92359955502247031711681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 985172858690635004924597 92359955502247031711681)
                ·
                  rfl

theorem cell21_1214125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 5].length) (baseStart_1214125 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1214125 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1214125 prefixEnd_1214125 := by exact prefixLift 1214125
  have htrace : WordTrace (prefixWord ++ tailWord_1214125) baseStart_1214125 baseEnd_1214125 := by
    simpa [prefixWord, tailWord_1214125, baseEnd_1214125] using wordTrace_append hprefix tailTrace_1214125
  have hstable : (prefixWord ++ tailWord_1214125).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214125).length < 2 ^ (prefixWord ++ tailWord_1214125).sum := by decide
  have hdescent : baseEnd_1214125 < baseStart_1214125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214156 : List Nat := [2, 2, 1, 5, 2, 1, 2, 1, 5]
def baseStart_1214156 : Nat := 118140960795 + 1214156 * 2 ^ 59
def prefixEnd_1214156 : Nat := 4983230072969 + 3 ^ 40 * 1214156 * 2
def baseEnd_1214156 : Nat := 277086941129091930118313

theorem tailTrace_1214156 : CollatzResearch.WordTrace tailWord_1214156 prefixEnd_1214156 277086941129091930118313 := by
  unfold tailWord_1214156
  simp only [CollatzResearch.WordTrace]
  refine ⟨22141953694663824090515161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29522604926218432120686881 22141953694663824090515161)
  ·
    refine ⟨16606465270997868067886371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22141953694663824090515161 16606465270997868067886371)
    ·
      refine ⟨24909697906496802101829557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16606465270997868067886371 24909697906496802101829557)
      ·
        refine ⟨2335284178734075197046521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24909697906496802101829557 2335284178734075197046521)
        ·
          refine ⟨1751463134050556397784891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2335284178734075197046521 1751463134050556397784891)
          ·
            refine ⟨2627194701075834596677337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1751463134050556397784891 2627194701075834596677337)
            ·
              refine ⟨1970396025806875947508003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2627194701075834596677337 1970396025806875947508003)
              ·
                refine ⟨2955594038710313921262005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1970396025806875947508003 2955594038710313921262005)
                ·
                  refine ⟨277086941129091930118313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2955594038710313921262005 277086941129091930118313)
                  ·
                    rfl

theorem cell21_1214156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_1214156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1214156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1214156 prefixEnd_1214156 := by exact prefixLift 1214156
  have htrace : WordTrace (prefixWord ++ tailWord_1214156) baseStart_1214156 baseEnd_1214156 := by
    simpa [prefixWord, tailWord_1214156, baseEnd_1214156] using wordTrace_append hprefix tailTrace_1214156
  have hstable : (prefixWord ++ tailWord_1214156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214156).length < 2 ^ (prefixWord ++ tailWord_1214156).sum := by decide
  have hdescent : baseEnd_1214156 < baseStart_1214156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214167 : List Nat := [1, 1, 3, 2, 1, 3, 2, 8]
def baseStart_1214167 : Nat := 118140960795 + 1214167 * 2 ^ 59
def prefixEnd_1214167 : Nat := 4983230072969 + 3 ^ 40 * 1214167 * 2
def baseEnd_1214167 : Nat := 92363150492986118478319

theorem tailTrace_1214167 : CollatzResearch.WordTrace tailWord_1214167 prefixEnd_1214167 92363150492986118478319 := by
  unfold tailWord_1214167
  simp only [CollatzResearch.WordTrace]
  refine ⟨44284308592287797059680755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29522872394858531373120503 44284308592287797059680755)
  ·
    refine ⟨66426462888431695589521133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44284308592287797059680755 66426462888431695589521133)
    ·
      refine ⟨24909923583161885846070425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66426462888431695589521133 24909923583161885846070425)
      ·
        refine ⟨18682442687371414384552819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24909923583161885846070425 18682442687371414384552819)
        ·
          refine ⟨28023664031057121576829229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18682442687371414384552819 28023664031057121576829229)
          ·
            refine ⟨10508874011646420591310961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28023664031057121576829229 10508874011646420591310961)
            ·
              refine ⟨7881655508734815443483221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10508874011646420591310961 7881655508734815443483221)
              ·
                refine ⟨92363150492986118478319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7881655508734815443483221 92363150492986118478319)
                ·
                  rfl

theorem cell21_1214167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 8].length) (baseStart_1214167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1214167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1214167 prefixEnd_1214167 := by exact prefixLift 1214167
  have htrace : WordTrace (prefixWord ++ tailWord_1214167) baseStart_1214167 baseEnd_1214167 := by
    simpa [prefixWord, tailWord_1214167, baseEnd_1214167] using wordTrace_append hprefix tailTrace_1214167
  have hstable : (prefixWord ++ tailWord_1214167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214167).length < 2 ^ (prefixWord ++ tailWord_1214167).sum := by decide
  have hdescent : baseEnd_1214167 < baseStart_1214167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214184 : List Nat := [2, 1, 4, 1, 3, 2, 1, 7]
def baseStart_1214184 : Nat := 118140960795 + 1214184 * 2 ^ 59
def prefixEnd_1214184 : Nat := 4983230072969 + 3 ^ 40 * 1214184 * 2
def baseEnd_1214184 : Nat := 92364443703523367883863

theorem tailTrace_1214184 : CollatzResearch.WordTrace tailWord_1214184 prefixEnd_1214184 92364443703523367883863 := by
  unfold tailWord_1214184
  simp only [CollatzResearch.WordTrace]
  refine ⟨22142464316613104481524803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29523285755484139308699737 22142464316613104481524803)
  ·
    refine ⟨33213696474919656722287205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22142464316613104481524803 33213696474919656722287205)
    ·
      refine ⟨6227568089047435635428851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33213696474919656722287205 6227568089047435635428851)
      ·
        refine ⟨9341352133571153453143277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6227568089047435635428851 9341352133571153453143277)
        ·
          refine ⟨3503007050089182544928729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9341352133571153453143277 3503007050089182544928729)
          ·
            refine ⟨2627255287566886908696547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3503007050089182544928729 2627255287566886908696547)
            ·
              refine ⟨3940882931350330363044821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2627255287566886908696547 3940882931350330363044821)
              ·
                refine ⟨92364443703523367883863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3940882931350330363044821 92364443703523367883863)
                ·
                  rfl

theorem cell21_1214184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 7].length) (baseStart_1214184 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1214184 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1214184 prefixEnd_1214184 := by exact prefixLift 1214184
  have htrace : WordTrace (prefixWord ++ tailWord_1214184) baseStart_1214184 baseEnd_1214184 := by
    simpa [prefixWord, tailWord_1214184, baseEnd_1214184] using wordTrace_append hprefix tailTrace_1214184
  have hstable : (prefixWord ++ tailWord_1214184).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214184).length < 2 ^ (prefixWord ++ tailWord_1214184).sum := by decide
  have hdescent : baseEnd_1214184 < baseStart_1214184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214243 : List Nat := [1, 1, 1, 4, 2, 1, 4, 7]
def baseStart_1214243 : Nat := 118140960795 + 1214243 * 2 ^ 59
def prefixEnd_1214243 : Nat := 4983230072969 + 3 ^ 40 * 1214243 * 2
def baseEnd_1214243 : Nat := 92368931904799704056045

theorem tailTrace_1214243 : CollatzResearch.WordTrace tailWord_1214243 prefixEnd_1214243 92368931904799704056045 := by
  unfold tailWord_1214243
  simp only [CollatzResearch.WordTrace]
  refine ⟨44287080540012462039447383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29524720360008308026298255 44287080540012462039447383)
  ·
    refine ⟨66430620810018693059171075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44287080540012462039447383 66430620810018693059171075)
    ·
      refine ⟨99645931215028039588756613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66430620810018693059171075 99645931215028039588756613)
      ·
        refine ⟨18683612102817757422891865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 99645931215028039588756613 18683612102817757422891865)
        ·
          refine ⟨14012709077113318067168899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18683612102817757422891865 14012709077113318067168899)
          ·
            refine ⟨21019063615669977100753349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14012709077113318067168899 21019063615669977100753349)
            ·
              refine ⟨3941074427938120706391253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21019063615669977100753349 3941074427938120706391253)
              ·
                refine ⟨92368931904799704056045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3941074427938120706391253 92368931904799704056045)
                ·
                  rfl

theorem cell21_1214243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 7].length) (baseStart_1214243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1214243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1214243 prefixEnd_1214243 := by exact prefixLift 1214243
  have htrace : WordTrace (prefixWord ++ tailWord_1214243) baseStart_1214243 baseEnd_1214243 := by
    simpa [prefixWord, tailWord_1214243, baseEnd_1214243] using wordTrace_append hprefix tailTrace_1214243
  have hstable : (prefixWord ++ tailWord_1214243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214243).length < 2 ^ (prefixWord ++ tailWord_1214243).sum := by decide
  have hdescent : baseEnd_1214243 < baseStart_1214243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214260 : List Nat := [2, 5, 1, 1, 2, 10]
def baseStart_1214260 : Nat := 118140960795 + 1214260 * 2 ^ 59
def prefixEnd_1214260 : Nat := 4983230072969 + 3 ^ 40 * 1214260 * 2
def baseEnd_1214260 : Nat := 10263358346148550384621

theorem tailTrace_1214260 : CollatzResearch.WordTrace tailWord_1214260 prefixEnd_1214260 10263358346148550384621 := by
  unfold tailWord_1214260
  simp only [CollatzResearch.WordTrace]
  refine ⟨22143850290475436971408117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29525133720633915961877489 22143850290475436971408117)
  ·
    refine ⟨2075985964732072216069511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22143850290475436971408117 2075985964732072216069511)
    ·
      refine ⟨3113978947098108324104267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2075985964732072216069511 3113978947098108324104267)
      ·
        refine ⟨4670968420647162486156401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3113978947098108324104267 4670968420647162486156401)
        ·
          refine ⟨3503226315485371864617301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4670968420647162486156401 3503226315485371864617301)
          ·
            refine ⟨10263358346148550384621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3503226315485371864617301 10263358346148550384621)
            ·
              rfl

theorem cell21_1214260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 10].length) (baseStart_1214260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1214260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1214260 prefixEnd_1214260 := by exact prefixLift 1214260
  have htrace : WordTrace (prefixWord ++ tailWord_1214260) baseStart_1214260 baseEnd_1214260 := by
    simpa [prefixWord, tailWord_1214260, baseEnd_1214260] using wordTrace_append hprefix tailTrace_1214260
  have hstable : (prefixWord ++ tailWord_1214260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214260).length < 2 ^ (prefixWord ++ tailWord_1214260).sum := by decide
  have hdescent : baseEnd_1214260 < baseStart_1214260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214288 : List Nat := [2, 1, 1, 1, 1, 4, 1, 2, 8]
def baseStart_1214288 : Nat := 118140960795 + 1214288 * 2 ^ 59
def prefixEnd_1214288 : Nat := 4983230072969 + 3 ^ 40 * 1214288 * 2
def baseEnd_1214288 : Nat := 277117065327489033918043

theorem tailTrace_1214288 : CollatzResearch.WordTrace tailWord_1214288 prefixEnd_1214288 277117065327489033918043 := by
  unfold tailWord_1214288
  simp only [CollatzResearch.WordTrace]
  refine ⟨22144360912424717362417759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29525814549899623149890345 22144360912424717362417759)
  ·
    refine ⟨33216541368637076043626639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22144360912424717362417759 33216541368637076043626639)
    ·
      refine ⟨49824812052955614065439959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33216541368637076043626639 49824812052955614065439959)
      ·
        refine ⟨74737218079433421098159939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49824812052955614065439959 74737218079433421098159939)
        ·
          refine ⟨112105827119150131647239909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 74737218079433421098159939 112105827119150131647239909)
          ·
            refine ⟨21019842584840649683857483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112105827119150131647239909 21019842584840649683857483)
            ·
              refine ⟨31529763877260974525786225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21019842584840649683857483 31529763877260974525786225)
              ·
                refine ⟨23647322907945730894339669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31529763877260974525786225 23647322907945730894339669)
                ·
                  refine ⟨277117065327489033918043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23647322907945730894339669 277117065327489033918043)
                  ·
                    rfl

theorem cell21_1214288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 8].length) (baseStart_1214288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1214288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1214288 prefixEnd_1214288 := by exact prefixLift 1214288
  have htrace : WordTrace (prefixWord ++ tailWord_1214288) baseStart_1214288 baseEnd_1214288 := by
    simpa [prefixWord, tailWord_1214288, baseEnd_1214288] using wordTrace_append hprefix tailTrace_1214288
  have hstable : (prefixWord ++ tailWord_1214288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214288).length < 2 ^ (prefixWord ++ tailWord_1214288).sum := by decide
  have hdescent : baseEnd_1214288 < baseStart_1214288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214398 : List Nat := [4, 2, 1, 1, 1, 4, 1, 3, 4]
def baseStart_1214398 : Nat := 118140960795 + 1214398 * 2 ^ 59
def prefixEnd_1214398 : Nat := 4983230072969 + 3 ^ 40 * 1214398 * 2
def baseEnd_1214398 : Nat := 277142168826153287084485

theorem tailTrace_1214398 : CollatzResearch.WordTrace tailWord_1214398 prefixEnd_1214398 277142168826153287084485 := by
  unfold tailWord_1214398
  simp only [CollatzResearch.WordTrace]
  refine ⟨5536591731806365438917481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 29528489236300615674226565 5536591731806365438917481)
  ·
    refine ⟨4152443798854774079188111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5536591731806365438917481 4152443798854774079188111)
    ·
      refine ⟨6228665698282161118782167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4152443798854774079188111 6228665698282161118782167)
      ·
        refine ⟨9342998547423241678173251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6228665698282161118782167 9342998547423241678173251)
        ·
          refine ⟨14014497821134862517259877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9342998547423241678173251 14014497821134862517259877)
          ·
            refine ⟨2627718341462786721986227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14014497821134862517259877 2627718341462786721986227)
            ·
              refine ⟨3941577512194180082979341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2627718341462786721986227 3941577512194180082979341)
              ·
                refine ⟨1478091567072817531117253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3941577512194180082979341 1478091567072817531117253)
                ·
                  refine ⟨277142168826153287084485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1478091567072817531117253 277142168826153287084485)
                  ·
                    rfl

theorem cell21_1214398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_1214398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1214398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1214398 prefixEnd_1214398 := by exact prefixLift 1214398
  have htrace : WordTrace (prefixWord ++ tailWord_1214398) baseStart_1214398 baseEnd_1214398 := by
    simpa [prefixWord, tailWord_1214398, baseEnd_1214398] using wordTrace_append hprefix tailTrace_1214398
  have hstable : (prefixWord ++ tailWord_1214398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214398).length < 2 ^ (prefixWord ++ tailWord_1214398).sum := by decide
  have hdescent : baseEnd_1214398 < baseStart_1214398 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214457 : List Nat := [1, 2, 1, 3, 1, 4, 2, 3, 4]
def baseStart_1214457 : Nat := 118140960795 + 1214457 * 2 ^ 59
def prefixEnd_1214457 : Nat := 4983230072969 + 3 ^ 40 * 1214457 * 2
def baseEnd_1214457 : Nat := 277155633429982295601031

theorem tailTrace_1214457 : CollatzResearch.WordTrace tailWord_1214457 prefixEnd_1214457 277155633429982295601031 := by
  unfold tailWord_1214457
  simp only [CollatzResearch.WordTrace]
  refine ⟨44294885761237176587737625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29529923840824784391825083 44294885761237176587737625)
  ·
    refine ⟨33221164320927882440803219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44294885761237176587737625 33221164320927882440803219)
    ·
      refine ⟨49831746481391823661204829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33221164320927882440803219 49831746481391823661204829)
      ·
        refine ⟨18686904930521933872951811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49831746481391823661204829 18686904930521933872951811)
        ·
          refine ⟨28030357395782900809427717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18686904930521933872951811 28030357395782900809427717)
          ·
            refine ⟨5255692011709293901767697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28030357395782900809427717 5255692011709293901767697)
            ·
              refine ⟨3941769008781970426325773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5255692011709293901767697 3941769008781970426325773)
              ·
                refine ⟨1478163378293238909872165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3941769008781970426325773 1478163378293238909872165)
                ·
                  refine ⟨277155633429982295601031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1478163378293238909872165 277155633429982295601031)
                  ·
                    rfl

theorem cell21_1214457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 3, 4].length) (baseStart_1214457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1214457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1214457 prefixEnd_1214457 := by exact prefixLift 1214457
  have htrace : WordTrace (prefixWord ++ tailWord_1214457) baseStart_1214457 baseEnd_1214457 := by
    simpa [prefixWord, tailWord_1214457, baseEnd_1214457] using wordTrace_append hprefix tailTrace_1214457
  have hstable : (prefixWord ++ tailWord_1214457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214457).length < 2 ^ (prefixWord ++ tailWord_1214457).sum := by decide
  have hdescent : baseEnd_1214457 < baseStart_1214457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214626 : List Nat := [3, 3, 1, 3, 1, 1, 2, 3, 4]
def baseStart_1214626 : Nat := 118140960795 + 1214626 * 2 ^ 59
def prefixEnd_1214626 : Nat := 4983230072969 + 3 ^ 40 * 1214626 * 2
def baseEnd_1214626 : Nat := 277194201532475557284019

theorem tailTrace_1214626 : CollatzResearch.WordTrace tailWord_1214626 prefixEnd_1214626 277194201532475557284019 := by
  unfold tailWord_1214626
  simp only [CollatzResearch.WordTrace]
  refine ⟨11075262424406229612659933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29534033131749945633759821 11075262424406229612659933)
  ·
    refine ⟨4153223409152336104747475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11075262424406229612659933 4153223409152336104747475)
    ·
      refine ⟨6229835113728504157121213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4153223409152336104747475 6229835113728504157121213)
      ·
        refine ⟨2336188167648189058920455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6229835113728504157121213 2336188167648189058920455)
        ·
          refine ⟨3504282251472283588380683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2336188167648189058920455 3504282251472283588380683)
          ·
            refine ⟨5256423377208425382571025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3504282251472283588380683 5256423377208425382571025)
            ·
              refine ⟨3942317532906319036928269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5256423377208425382571025 3942317532906319036928269)
              ·
                refine ⟨1478369074839869638848101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3942317532906319036928269 1478369074839869638848101)
                ·
                  refine ⟨277194201532475557284019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1478369074839869638848101 277194201532475557284019)
                  ·
                    rfl

theorem cell21_1214626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_1214626 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1214626 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1214626 prefixEnd_1214626 := by exact prefixLift 1214626
  have htrace : WordTrace (prefixWord ++ tailWord_1214626) baseStart_1214626 baseEnd_1214626 := by
    simpa [prefixWord, tailWord_1214626, baseEnd_1214626] using wordTrace_append hprefix tailTrace_1214626
  have hstable : (prefixWord ++ tailWord_1214626).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214626).length < 2 ^ (prefixWord ++ tailWord_1214626).sum := by decide
  have hdescent : baseEnd_1214626 < baseStart_1214626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214730 : List Nat := [3, 1, 2, 2, 1, 1, 5, 1, 5]
def baseStart_1214730 : Nat := 118140960795 + 1214730 * 2 ^ 59
def prefixEnd_1214730 : Nat := 4983230072969 + 3 ^ 40 * 1214730 * 2
def baseEnd_1214730 : Nat := 277217935749394487550473

theorem tailTrace_1214730 : CollatzResearch.WordTrace tailWord_1214730 prefixEnd_1214730 277217935749394487550473 := by
  unfold tailWord_1214730
  simp only [CollatzResearch.WordTrace]
  refine ⟨11076210722312036053106411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 29536561926165429474950429 11076210722312036053106411)
  ·
    refine ⟨16614316083468054079659617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11076210722312036053106411 16614316083468054079659617)
    ·
      refine ⟨12460737062601040559744713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16614316083468054079659617 12460737062601040559744713)
      ·
        refine ⟨9345552796950780419808535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12460737062601040559744713 9345552796950780419808535)
        ·
          refine ⟨14018329195426170629712803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9345552796950780419808535 14018329195426170629712803)
          ·
            refine ⟨21027493793139255944569205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14018329195426170629712803 21027493793139255944569205)
            ·
              refine ⟨1971327543106805244803363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21027493793139255944569205 1971327543106805244803363)
              ·
                refine ⟨2956991314660207867205045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1971327543106805244803363 2956991314660207867205045)
                ·
                  refine ⟨277217935749394487550473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2956991314660207867205045 277217935749394487550473)
                  ·
                    rfl

theorem cell21_1214730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_1214730 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1214730 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1214730 prefixEnd_1214730 := by exact prefixLift 1214730
  have htrace : WordTrace (prefixWord ++ tailWord_1214730) baseStart_1214730 baseEnd_1214730 := by
    simpa [prefixWord, tailWord_1214730, baseEnd_1214730] using wordTrace_append hprefix tailTrace_1214730
  have hstable : (prefixWord ++ tailWord_1214730).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214730).length < 2 ^ (prefixWord ++ tailWord_1214730).sum := by decide
  have hdescent : baseEnd_1214730 < baseStart_1214730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214820 : List Nat := [2, 3, 1, 1, 3, 1, 2, 2, 6]
def baseStart_1214820 : Nat := 118140960795 + 1214820 * 2 ^ 59
def prefixEnd_1214820 : Nat := 4983230072969 + 3 ^ 40 * 1214820 * 2
def baseEnd_1214820 : Nat := 277238474975574331050289

theorem tailTrace_1214820 : CollatzResearch.WordTrace tailWord_1214820 prefixEnd_1214820 277238474975574331050289 := by
  unfold tailWord_1214820
  simp only [CollatzResearch.WordTrace]
  refine ⟨22154062729461044791600957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29538750305948059722134609 22154062729461044791600957)
  ·
    refine ⟨8307773523547891796850359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22154062729461044791600957 8307773523547891796850359)
    ·
      refine ⟨12461660285321837695275539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8307773523547891796850359 12461660285321837695275539)
      ·
        refine ⟨18692490427982756542913309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12461660285321837695275539 18692490427982756542913309)
        ·
          refine ⟨7009683910493533703592491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18692490427982756542913309 7009683910493533703592491)
          ·
            refine ⟨10514525865740300555388737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7009683910493533703592491 10514525865740300555388737)
            ·
              refine ⟨7885894399305225416541553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10514525865740300555388737 7885894399305225416541553)
              ·
                refine ⟨5914420799478919062406165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7885894399305225416541553 5914420799478919062406165)
                ·
                  refine ⟨277238474975574331050289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5914420799478919062406165 277238474975574331050289)
                  ·
                    rfl

theorem cell21_1214820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_1214820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1214820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1214820 prefixEnd_1214820 := by exact prefixLift 1214820
  have htrace : WordTrace (prefixWord ++ tailWord_1214820) baseStart_1214820 baseEnd_1214820 := by
    simpa [prefixWord, tailWord_1214820, baseEnd_1214820] using wordTrace_append hprefix tailTrace_1214820
  have hstable : (prefixWord ++ tailWord_1214820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214820).length < 2 ^ (prefixWord ++ tailWord_1214820).sum := by decide
  have hdescent : baseEnd_1214820 < baseStart_1214820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214823 : List Nat := [1, 1, 5, 1, 3, 1, 1, 5, 3]
def baseStart_1214823 : Nat := 118140960795 + 1214823 * 2 ^ 59
def prefixEnd_1214823 : Nat := 4983230072969 + 3 ^ 40 * 1214823 * 2
def baseEnd_1214823 : Nat := 277239159616446992500283

theorem tailTrace_1214823 : CollatzResearch.WordTrace tailWord_1214823 prefixEnd_1214823 277239159616446992500283 := by
  unfold tailWord_1214823
  simp only [CollatzResearch.WordTrace]
  refine ⟨44308234877911221095561123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29538823251940814063707415 44308234877911221095561123)
  ·
    refine ⟨66462352316866831643341685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44308234877911221095561123 66462352316866831643341685)
    ·
      refine ⟨6230845529706265466563283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 66462352316866831643341685 6230845529706265466563283)
      ·
        refine ⟨9346268294559398199844925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6230845529706265466563283 9346268294559398199844925)
        ·
          refine ⟨3504850610459774324941847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9346268294559398199844925 3504850610459774324941847)
          ·
            refine ⟨5257275915689661487412771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3504850610459774324941847 5257275915689661487412771)
            ·
              refine ⟨7885913873534492231119157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5257275915689661487412771 7885913873534492231119157)
              ·
                refine ⟨739304425643858646667421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7885913873534492231119157 739304425643858646667421)
                ·
                  refine ⟨277239159616446992500283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 739304425643858646667421 277239159616446992500283)
                  ·
                    rfl

theorem cell21_1214823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 5, 3].length) (baseStart_1214823 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1214823 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1214823 prefixEnd_1214823 := by exact prefixLift 1214823
  have htrace : WordTrace (prefixWord ++ tailWord_1214823) baseStart_1214823 baseEnd_1214823 := by
    simpa [prefixWord, tailWord_1214823, baseEnd_1214823] using wordTrace_append hprefix tailTrace_1214823
  have hstable : (prefixWord ++ tailWord_1214823).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214823).length < 2 ^ (prefixWord ++ tailWord_1214823).sum := by decide
  have hdescent : baseEnd_1214823 < baseStart_1214823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214837 : List Nat := [1, 3, 4, 1, 2, 2, 1, 1, 6]
def baseStart_1214837 : Nat := 118140960795 + 1214837 * 2 ^ 59
def prefixEnd_1214837 : Nat := 4983230072969 + 3 ^ 40 * 1214837 * 2
def baseEnd_1214837 : Nat := 277242354607186079266921

theorem tailTrace_1214837 : CollatzResearch.WordTrace tailWord_1214837 prefixEnd_1214837 277242354607186079266921 := by
  unfold tailWord_1214837
  simp only [CollatzResearch.WordTrace]
  refine ⟨44308745499860501486570765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 29539163666573667657713843 44308745499860501486570765)
  ·
    refine ⟨16615779562447688057464037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44308745499860501486570765 16615779562447688057464037)
    ·
      refine ⟨3115458667958941510774507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 16615779562447688057464037 3115458667958941510774507)
      ·
        refine ⟨4673188001938412266161761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3115458667958941510774507 4673188001938412266161761)
        ·
          refine ⟨3504891001453809199621321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4673188001938412266161761 3504891001453809199621321)
          ·
            refine ⟨2628668251090356899715991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3504891001453809199621321 2628668251090356899715991)
            ·
              refine ⟨3943002376635535349573987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2628668251090356899715991 3943002376635535349573987)
              ·
                refine ⟨5914503564953303024360981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3943002376635535349573987 5914503564953303024360981)
                ·
                  refine ⟨277242354607186079266921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5914503564953303024360981 277242354607186079266921)
                  ·
                    rfl

theorem cell21_1214837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 1, 6].length) (baseStart_1214837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1214837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1214837 prefixEnd_1214837 := by exact prefixLift 1214837
  have htrace : WordTrace (prefixWord ++ tailWord_1214837) baseStart_1214837 baseEnd_1214837 := by
    simpa [prefixWord, tailWord_1214837, baseEnd_1214837] using wordTrace_append hprefix tailTrace_1214837
  have hstable : (prefixWord ++ tailWord_1214837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214837).length < 2 ^ (prefixWord ++ tailWord_1214837).sum := by decide
  have hdescent : baseEnd_1214837 < baseStart_1214837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1214868 : List Nat := [2, 4, 2, 1, 3, 1, 1, 7]
def baseStart_1214868 : Nat := 118140960795 + 1214868 * 2 ^ 59
def prefixEnd_1214868 : Nat := 4983230072969 + 3 ^ 40 * 1214868 * 2
def baseEnd_1214868 : Nat := 92416476409845638083397

theorem tailTrace_1214868 : CollatzResearch.WordTrace tailWord_1214868 prefixEnd_1214868 92416476409845638083397 := by
  unfold tailWord_1214868
  simp only [CollatzResearch.WordTrace]
  refine ⟨22154938081374096890474629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 29539917441832129187299505 22154938081374096890474629)
  ·
    refine ⟨4154050890257643166963993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22154938081374096890474629 4154050890257643166963993)
    ·
      refine ⟨3115538167693232375222995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4154050890257643166963993 3115538167693232375222995)
      ·
        refine ⟨4673307251539848562834493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3115538167693232375222995 4673307251539848562834493)
        ·
          refine ⟨1752490219327443211062935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4673307251539848562834493 1752490219327443211062935)
          ·
            refine ⟨2628735328991164816594403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1752490219327443211062935 2628735328991164816594403)
            ·
              refine ⟨3943102993486747224891605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2628735328991164816594403 3943102993486747224891605)
              ·
                refine ⟨92416476409845638083397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3943102993486747224891605 92416476409845638083397)
                ·
                  rfl

theorem cell21_1214868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 7].length) (baseStart_1214868 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1214868 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1214868 prefixEnd_1214868 := by exact prefixLift 1214868
  have htrace : WordTrace (prefixWord ++ tailWord_1214868) baseStart_1214868 baseEnd_1214868 := by
    simpa [prefixWord, tailWord_1214868, baseEnd_1214868] using wordTrace_append hprefix tailTrace_1214868
  have hstable : (prefixWord ++ tailWord_1214868).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1214868).length < 2 ^ (prefixWord ++ tailWord_1214868).sum := by decide
  have hdescent : baseEnd_1214868 < baseStart_1214868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1214868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
