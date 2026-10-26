import V185TrunkScan23Chunk0278

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1649678 : List Nat := [4, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5]
def baseStart_1649678 : Nat := 118140960795 + 1649678 * 2 ^ 59
def prefixEnd_1649678 : Nat := 4983230072969 + 3 ^ 40 * 1649678 * 2
def baseEnd_1649678 : Nat := 847077739147901860938275

theorem tailTrace_1649678 : CollatzResearch.WordTrace tailWord_1649678 prefixEnd_1649678 847077739147901860938275 := by
  unfold tailWord_1649678
  simp only [CollatzResearch.WordTrace]
  refine ⟨7521087464688227927104711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40112466478337215611225125 7521087464688227927104711)
  ·
    refine ⟨11281631197032341890657067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7521087464688227927104711 11281631197032341890657067)
    ·
      refine ⟨16922446795548512835985601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11281631197032341890657067 16922446795548512835985601)
      ·
        refine ⟨12691835096661384626989201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16922446795548512835985601 12691835096661384626989201)
        ·
          refine ⟨9518876322496038470241901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12691835096661384626989201 9518876322496038470241901)
          ·
            refine ⟨3569578620936014426340713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9518876322496038470241901 3569578620936014426340713)
            ·
              refine ⟨2677183965702010819755535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3569578620936014426340713 2677183965702010819755535)
              ·
                refine ⟨4015775948553016229633303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677183965702010819755535 4015775948553016229633303)
                ·
                  refine ⟨6023663922829524344449955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4015775948553016229633303 6023663922829524344449955)
                  ·
                    refine ⟨9035495884244286516674933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6023663922829524344449955 9035495884244286516674933)
                    ·
                      refine ⟨847077739147901860938275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9035495884244286516674933 847077739147901860938275)
                      ·
                        rfl

theorem cell23_1649678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_1649678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649678 prefixEnd_1649678 := by exact prefixLift 1649678
  have htrace : WordTrace (prefixWord ++ tailWord_1649678) baseStart_1649678 baseEnd_1649678 := by
    simpa [prefixWord, tailWord_1649678, baseEnd_1649678] using wordTrace_append hprefix tailTrace_1649678
  have hstable : (prefixWord ++ tailWord_1649678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649678).length < 2 ^ (prefixWord ++ tailWord_1649678).sum := by decide
  have hdescent : baseEnd_1649678 < baseStart_1649678 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649761 : List Nat := [1, 2, 3, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_1649761 : Nat := 118140960795 + 1649761 * 2 ^ 59
def prefixEnd_1649761 : Nat := 4983230072969 + 3 ^ 40 * 1649761 * 2
def baseEnd_1649761 : Nat := 847120358042225036200393

theorem tailTrace_1649761 : CollatzResearch.WordTrace tailWord_1649761 prefixEnd_1649761 847120358042225036200393 := by
  unfold tailWord_1649761
  simp only [CollatzResearch.WordTrace]
  refine ⟨60171726976205128592109137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40114484650803419061406091 60171726976205128592109137)
  ·
    refine ⟨45128795232153846444081853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60171726976205128592109137 45128795232153846444081853)
    ·
      refine ⟨16923298212057692416530695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45128795232153846444081853 16923298212057692416530695)
      ·
        refine ⟨25384947318086538624796043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16923298212057692416530695 25384947318086538624796043)
        ·
          refine ⟨38077420977129807937194065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25384947318086538624796043 38077420977129807937194065)
          ·
            refine ⟨28558065732847355952895549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38077420977129807937194065 28558065732847355952895549)
            ·
              refine ⟨10709274649817758482335831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28558065732847355952895549 10709274649817758482335831)
              ·
                refine ⟨16063911974726637723503747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10709274649817758482335831 16063911974726637723503747)
                ·
                  refine ⟨24095867962089956585255621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16063911974726637723503747 24095867962089956585255621)
                  ·
                    refine ⟨4517975242891866859735429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24095867962089956585255621 4517975242891866859735429)
                    ·
                      refine ⟨847120358042225036200393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4517975242891866859735429 847120358042225036200393)
                      ·
                        rfl

theorem cell23_1649761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_1649761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649761 prefixEnd_1649761 := by exact prefixLift 1649761
  have htrace : WordTrace (prefixWord ++ tailWord_1649761) baseStart_1649761 baseEnd_1649761 := by
    simpa [prefixWord, tailWord_1649761, baseEnd_1649761] using wordTrace_append hprefix tailTrace_1649761
  have hstable : (prefixWord ++ tailWord_1649761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649761).length < 2 ^ (prefixWord ++ tailWord_1649761).sum := by decide
  have hdescent : baseEnd_1649761 < baseStart_1649761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649765 : List Nat := [1, 3, 1, 3, 2, 1, 4, 1, 1, 4, 2]
def baseStart_1649765 : Nat := 118140960795 + 1649765 * 2 ^ 59
def prefixEnd_1649765 : Nat := 4983230072969 + 3 ^ 40 * 1649765 * 2
def baseEnd_1649765 : Nat := 847122411964843020550375

theorem tailTrace_1649765 : CollatzResearch.WordTrace tailWord_1649765 prefixEnd_1649765 847122411964843020550375 := by
  unfold tailWord_1649765
  simp only [CollatzResearch.WordTrace]
  refine ⟨60171872868190637275254749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40114581912127091516836499 60171872868190637275254749)
  ·
    refine ⟨22564452325571488978220531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60171872868190637275254749 22564452325571488978220531)
    ·
      refine ⟨33846678488357233467330797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22564452325571488978220531 33846678488357233467330797)
      ·
        refine ⟨12692504433133962550249049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33846678488357233467330797 12692504433133962550249049)
        ·
          refine ⟨9519378324850471912686787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12692504433133962550249049 9519378324850471912686787)
          ·
            refine ⟨14279067487275707869030181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9519378324850471912686787 14279067487275707869030181)
            ·
              refine ⟨2677325153864195225443159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14279067487275707869030181 2677325153864195225443159)
              ·
                refine ⟨4015987730796292838164739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677325153864195225443159 4015987730796292838164739)
                ·
                  refine ⟨6023981596194439257247109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4015987730796292838164739 6023981596194439257247109)
                  ·
                    refine ⟨1129496549286457360733833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6023981596194439257247109 1129496549286457360733833)
                    ·
                      refine ⟨847122411964843020550375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1129496549286457360733833 847122411964843020550375)
                      ·
                        rfl

theorem cell23_1649765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_1649765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649765 prefixEnd_1649765 := by exact prefixLift 1649765
  have htrace : WordTrace (prefixWord ++ tailWord_1649765) baseStart_1649765 baseEnd_1649765 := by
    simpa [prefixWord, tailWord_1649765, baseEnd_1649765] using wordTrace_append hprefix tailTrace_1649765
  have hstable : (prefixWord ++ tailWord_1649765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649765).length < 2 ^ (prefixWord ++ tailWord_1649765).sum := by decide
  have hdescent : baseEnd_1649765 < baseStart_1649765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649782 : List Nat := [5, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2]
def baseStart_1649782 : Nat := 118140960795 + 1649782 * 2 ^ 59
def prefixEnd_1649782 : Nat := 4983230072969 + 3 ^ 40 * 1649782 * 2
def baseEnd_1649782 : Nat := 847131141135969454037797

theorem tailTrace_1649782 : CollatzResearch.WordTrace tailWord_1649782 prefixEnd_1649782 847131141135969454037797 := by
  unfold tailWord_1649782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3760780806820565573663975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40114995272752699452415733 3760780806820565573663975)
  ·
    refine ⟨5641171210230848360495963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3760780806820565573663975 5641171210230848360495963)
    ·
      refine ⟨8461756815346272540743945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5641171210230848360495963 8461756815346272540743945)
      ·
        refine ⟨6346317611509704405557959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8461756815346272540743945 6346317611509704405557959)
        ·
          refine ⟨9519476417264556608336939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6346317611509704405557959 9519476417264556608336939)
          ·
            refine ⟨14279214625896834912505409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9519476417264556608336939 14279214625896834912505409)
            ·
              refine ⟨10709410969422626184379057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14279214625896834912505409 10709410969422626184379057)
              ·
                refine ⟨8032058227066969638284293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10709410969422626184379057 8032058227066969638284293)
                ·
                  refine ⟨1506010917575056807178305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8032058227066969638284293 1506010917575056807178305)
                  ·
                    refine ⟨1129508188181292605383729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1506010917575056807178305 1129508188181292605383729)
                    ·
                      refine ⟨847131141135969454037797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1129508188181292605383729 847131141135969454037797)
                      ·
                        rfl

theorem cell23_1649782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_1649782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649782 prefixEnd_1649782 := by exact prefixLift 1649782
  have htrace : WordTrace (prefixWord ++ tailWord_1649782) baseStart_1649782 baseEnd_1649782 := by
    simpa [prefixWord, tailWord_1649782, baseEnd_1649782] using wordTrace_append hprefix tailTrace_1649782
  have hstable : (prefixWord ++ tailWord_1649782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649782).length < 2 ^ (prefixWord ++ tailWord_1649782).sum := by decide
  have hdescent : baseEnd_1649782 < baseStart_1649782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649808 : List Nat := [2, 1, 1, 1, 1, 1, 4, 3, 2, 5, 2]
def baseStart_1649808 : Nat := 118140960795 + 1649808 * 2 ^ 59
def prefixEnd_1649808 : Nat := 4983230072969 + 3 ^ 40 * 1649808 * 2
def baseEnd_1649808 : Nat := 847144491632986352312677

theorem tailTrace_1649808 : CollatzResearch.WordTrace tailWord_1649808 prefixEnd_1649808 847144491632986352312677 := by
  unfold tailWord_1649808
  simp only [CollatzResearch.WordTrace]
  refine ⟨30086720603517427809535039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40115627471356570412713385 30086720603517427809535039)
  ·
    refine ⟨45130080905276141714302559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30086720603517427809535039 45130080905276141714302559)
    ·
      refine ⟨67695121357914212571453839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45130080905276141714302559 67695121357914212571453839)
      ·
        refine ⟨101542682036871318857180759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67695121357914212571453839 101542682036871318857180759)
        ·
          refine ⟨152314023055306978285771139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101542682036871318857180759 152314023055306978285771139)
          ·
            refine ⟨228471034582960467428656709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152314023055306978285771139 228471034582960467428656709)
            ·
              refine ⟨42838318984305087642873133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228471034582960467428656709 42838318984305087642873133)
              ·
                refine ⟨16064369619114407866077425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42838318984305087642873133 16064369619114407866077425)
                ·
                  refine ⟨12048277214335805899558069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16064369619114407866077425 12048277214335805899558069)
                  ·
                    refine ⟨1129525988843981803083569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12048277214335805899558069 1129525988843981803083569)
                    ·
                      refine ⟨847144491632986352312677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1129525988843981803083569 847144491632986352312677)
                      ·
                        rfl

theorem cell23_1649808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 3, 2, 5, 2].length) (baseStart_1649808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649808 prefixEnd_1649808 := by exact prefixLift 1649808
  have htrace : WordTrace (prefixWord ++ tailWord_1649808) baseStart_1649808 baseEnd_1649808 := by
    simpa [prefixWord, tailWord_1649808, baseEnd_1649808] using wordTrace_append hprefix tailTrace_1649808
  have hstable : (prefixWord ++ tailWord_1649808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649808).length < 2 ^ (prefixWord ++ tailWord_1649808).sum := by decide
  have hdescent : baseEnd_1649808 < baseStart_1649808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649811 : List Nat := [1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 5]
def baseStart_1649811 : Nat := 118140960795 + 1649811 * 2 ^ 59
def prefixEnd_1649811 : Nat := 4983230072969 + 3 ^ 40 * 1649811 * 2
def baseEnd_1649811 : Nat := 847146032074949840575163

theorem tailTrace_1649811 : CollatzResearch.WordTrace tailWord_1649811 prefixEnd_1649811 847146032074949840575163 := by
  unfold tailWord_1649811
  simp only [CollatzResearch.WordTrace]
  refine ⟨60173550626023987131429287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40115700417349324754286191 60173550626023987131429287)
  ·
    refine ⟨90260325939035980697143931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60173550626023987131429287 90260325939035980697143931)
    ·
      refine ⟨135390488908553971045715897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90260325939035980697143931 135390488908553971045715897)
      ·
        refine ⟨101542866681415478284286923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135390488908553971045715897 101542866681415478284286923)
        ·
          refine ⟨152314300022123217426430385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101542866681415478284286923 152314300022123217426430385)
          ·
            refine ⟨114235725016592413069822789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152314300022123217426430385 114235725016592413069822789)
            ·
              refine ⟨21419198440611077450591773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114235725016592413069822789 21419198440611077450591773)
              ·
                refine ⟨8032199415229154043971915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21419198440611077450591773 8032199415229154043971915)
                ·
                  refine ⟨12048299122843731065957873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8032199415229154043971915 12048299122843731065957873)
                  ·
                    refine ⟨9036224342132798299468405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12048299122843731065957873 9036224342132798299468405)
                    ·
                      refine ⟨847146032074949840575163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9036224342132798299468405 847146032074949840575163)
                      ·
                        rfl

theorem cell23_1649811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 1, 2, 5].length) (baseStart_1649811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649811 prefixEnd_1649811 := by exact prefixLift 1649811
  have htrace : WordTrace (prefixWord ++ tailWord_1649811) baseStart_1649811 baseEnd_1649811 := by
    simpa [prefixWord, tailWord_1649811, baseEnd_1649811] using wordTrace_append hprefix tailTrace_1649811
  have hstable : (prefixWord ++ tailWord_1649811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649811).length < 2 ^ (prefixWord ++ tailWord_1649811).sum := by decide
  have hdescent : baseEnd_1649811 < baseStart_1649811 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649818 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 1, 7]
def baseStart_1649818 : Nat := 118140960795 + 1649818 * 2 ^ 59
def prefixEnd_1649818 : Nat := 4983230072969 + 3 ^ 40 * 1649818 * 2
def baseEnd_1649818 : Nat := 282383208813177104395877

theorem tailTrace_1649818 : CollatzResearch.WordTrace tailWord_1649818 prefixEnd_1649818 282383208813177104395877 := by
  unfold tailWord_1649818
  simp only [CollatzResearch.WordTrace]
  refine ⟨15043451484249656831733527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40115870624665751551289405 15043451484249656831733527)
  ·
    refine ⟨22565177226374485247600291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15043451484249656831733527 22565177226374485247600291)
    ·
      refine ⟨33847765839561727871400437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22565177226374485247600291 33847765839561727871400437)
      ·
        refine ⟨3173228047458911987943791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33847765839561727871400437 3173228047458911987943791)
        ·
          refine ⟨4759842071188367981915687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3173228047458911987943791 4759842071188367981915687)
          ·
            refine ⟨7139763106782551972873531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4759842071188367981915687 7139763106782551972873531)
            ·
              refine ⟨10709644660173827959310297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7139763106782551972873531 10709644660173827959310297)
              ·
                refine ⟨8032233495130370969482723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10709644660173827959310297 8032233495130370969482723)
                ·
                  refine ⟨12048350242695556454224085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8032233495130370969482723 12048350242695556454224085)
                  ·
                    refine ⟨282383208813177104395877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12048350242695556454224085 282383208813177104395877)
                    ·
                      rfl

theorem cell23_1649818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 1, 7].length) (baseStart_1649818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649818 prefixEnd_1649818 := by exact prefixLift 1649818
  have htrace : WordTrace (prefixWord ++ tailWord_1649818) baseStart_1649818 baseEnd_1649818 := by
    simpa [prefixWord, tailWord_1649818, baseEnd_1649818] using wordTrace_append hprefix tailTrace_1649818
  have hstable : (prefixWord ++ tailWord_1649818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649818).length < 2 ^ (prefixWord ++ tailWord_1649818).sum := by decide
  have hdescent : baseEnd_1649818 < baseStart_1649818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649851 : List Nat := [1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 6]
def baseStart_1649851 : Nat := 118140960795 + 1649851 * 2 ^ 59
def prefixEnd_1649851 : Nat := 4983230072969 + 3 ^ 40 * 1649851 * 2
def baseEnd_1649851 : Nat := 847166571301129684074979

theorem tailTrace_1649851 : CollatzResearch.WordTrace tailWord_1649851 prefixEnd_1649851 847166571301129684074979 := by
  unfold tailWord_1649851
  simp only [CollatzResearch.WordTrace]
  refine ⟨60175009545879073962885407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40116673030586049308590271 60175009545879073962885407)
  ·
    refine ⟨90262514318818610944328111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60175009545879073962885407 90262514318818610944328111)
    ·
      refine ⟨135393771478227916416492167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90262514318818610944328111 135393771478227916416492167)
      ·
        refine ⟨203090657217341874624738251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135393771478227916416492167 203090657217341874624738251)
        ·
          refine ⟨304635985826012811937107377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203090657217341874624738251 304635985826012811937107377)
          ·
            refine ⟨228476989369509608952830533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304635985826012811937107377 228476989369509608952830533)
            ·
              refine ⟨42839435506783051678655725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228476989369509608952830533 42839435506783051678655725)
              ·
                refine ⟨16064788315043644379495897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42839435506783051678655725 16064788315043644379495897)
                ·
                  refine ⟨12048591236282733284621923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16064788315043644379495897 12048591236282733284621923)
                  ·
                    refine ⟨18072886854424099926932885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12048591236282733284621923 18072886854424099926932885)
                    ·
                      refine ⟨847166571301129684074979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18072886854424099926932885 847166571301129684074979)
                      ·
                        rfl

theorem cell23_1649851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 1, 6].length) (baseStart_1649851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649851 prefixEnd_1649851 := by exact prefixLift 1649851
  have htrace : WordTrace (prefixWord ++ tailWord_1649851) baseStart_1649851 baseEnd_1649851 := by
    simpa [prefixWord, tailWord_1649851, baseEnd_1649851] using wordTrace_append hprefix tailTrace_1649851
  have hstable : (prefixWord ++ tailWord_1649851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649851).length < 2 ^ (prefixWord ++ tailWord_1649851).sum := by decide
  have hdescent : baseEnd_1649851 < baseStart_1649851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649916 : List Nat := [2, 2, 2, 1, 5, 2, 2, 2, 1, 4]
def baseStart_1649916 : Nat := 118140960795 + 1649916 * 2 ^ 59
def prefixEnd_1649916 : Nat := 4983230072969 + 3 ^ 40 * 1649916 * 2
def baseEnd_1649916 : Nat := 282399982514557309920727

theorem tailTrace_1649916 : CollatzResearch.WordTrace tailWord_1649916 prefixEnd_1649916 282399982514557309920727 := by
  unfold tailWord_1649916
  simp only [CollatzResearch.WordTrace]
  refine ⟨30088690145321795032000801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40118253527095726709334401 30088690145321795032000801)
  ·
    refine ⟨22566517608991346274000601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30088690145321795032000801 22566517608991346274000601)
    ·
      refine ⟨16924888206743509705500451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22566517608991346274000601 16924888206743509705500451)
      ·
        refine ⟨25387332310115264558250677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16924888206743509705500451 25387332310115264558250677)
        ·
          refine ⟨2380062404073306052336001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25387332310115264558250677 2380062404073306052336001)
          ·
            refine ⟨1785046803054979539252001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2380062404073306052336001 1785046803054979539252001)
            ·
              refine ⟨1338785102291234654439001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1785046803054979539252001 1338785102291234654439001)
              ·
                refine ⟨1004088826718425990829251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1338785102291234654439001 1004088826718425990829251)
                ·
                  refine ⟨1506133240077638986243877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1004088826718425990829251 1506133240077638986243877)
                  ·
                    refine ⟨282399982514557309920727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1506133240077638986243877 282399982514557309920727)
                    ·
                      rfl

theorem cell23_1649916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_1649916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649916 prefixEnd_1649916 := by exact prefixLift 1649916
  have htrace : WordTrace (prefixWord ++ tailWord_1649916) baseStart_1649916 baseEnd_1649916 := by
    simpa [prefixWord, tailWord_1649916, baseEnd_1649916] using wordTrace_append hprefix tailTrace_1649916
  have hstable : (prefixWord ++ tailWord_1649916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649916).length < 2 ^ (prefixWord ++ tailWord_1649916).sum := by decide
  have hdescent : baseEnd_1649916 < baseStart_1649916 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649949 : List Nat := [1, 4, 2, 3, 1, 1, 3, 1, 2, 3, 2]
def baseStart_1649949 : Nat := 118140960795 + 1649949 * 2 ^ 59
def prefixEnd_1649949 : Nat := 4983230072969 + 3 ^ 40 * 1649949 * 2
def baseEnd_1649949 : Nat := 847216892405270300649529

theorem tailTrace_1649949 : CollatzResearch.WordTrace tailWord_1649949 prefixEnd_1649949 847216892405270300649529 := by
  unfold tailWord_1649949
  simp only [CollatzResearch.WordTrace]
  refine ⟨60178583899524036699952901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40119055933016024466635267 60178583899524036699952901)
  ·
    refine ⟨11283484481160756881241169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60178583899524036699952901 11283484481160756881241169)
    ·
      refine ⟨8462613360870567660930877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11283484481160756881241169 8462613360870567660930877)
      ·
        refine ⟨3173480010326462872849079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8462613360870567660930877 3173480010326462872849079)
        ·
          refine ⟨4760220015489694309273619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3173480010326462872849079 4760220015489694309273619)
          ·
            refine ⟨7140330023234541463910429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4760220015489694309273619 7140330023234541463910429)
            ·
              refine ⟨2677623758712953048966411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7140330023234541463910429 2677623758712953048966411)
              ·
                refine ⟨4016435638069429573449617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677623758712953048966411 4016435638069429573449617)
                ·
                  refine ⟨3012326728552072180087213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4016435638069429573449617 3012326728552072180087213)
                  ·
                    refine ⟨1129622523207027067532705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3012326728552072180087213 1129622523207027067532705)
                    ·
                      refine ⟨847216892405270300649529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1129622523207027067532705 847216892405270300649529)
                      ·
                        rfl

theorem cell23_1649949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_1649949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649949 prefixEnd_1649949 := by exact prefixLift 1649949
  have htrace : WordTrace (prefixWord ++ tailWord_1649949) baseStart_1649949 baseEnd_1649949 := by
    simpa [prefixWord, tailWord_1649949, baseEnd_1649949] using wordTrace_append hprefix tailTrace_1649949
  have hstable : (prefixWord ++ tailWord_1649949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649949).length < 2 ^ (prefixWord ++ tailWord_1649949).sum := by decide
  have hdescent : baseEnd_1649949 < baseStart_1649949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1649972 : List Nat := [2, 5, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_1649972 : Nat := 118140960795 + 1649972 * 2 ^ 59
def prefixEnd_1649972 : Nat := 4983230072969 + 3 ^ 40 * 1649972 * 2
def baseEnd_1649972 : Nat := 282409567486774570220641

theorem tailTrace_1649972 : CollatzResearch.WordTrace tailWord_1649972 prefixEnd_1649972 282409567486774570220641 := by
  unfold tailWord_1649972
  simp only [CollatzResearch.WordTrace]
  refine ⟨30089711389220355814020085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40119615185627141085360113 30089711389220355814020085)
  ·
    refine ⟨2820910442739408357564383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30089711389220355814020085 2820910442739408357564383)
    ·
      refine ⟨4231365664109112536346575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2820910442739408357564383 4231365664109112536346575)
      ·
        refine ⟨6347048496163668804519863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4231365664109112536346575 6347048496163668804519863)
        ·
          refine ⟨9520572744245503206779795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6347048496163668804519863 9520572744245503206779795)
          ·
            refine ⟨14280859116368254810169693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9520572744245503206779795 14280859116368254810169693)
            ·
              refine ⟨5355322168638095553813635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14280859116368254810169693 5355322168638095553813635)
              ·
                refine ⟨8032983252957143330720453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5355322168638095553813635 8032983252957143330720453)
                ·
                  refine ⟨1506184359929464374510085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8032983252957143330720453 1506184359929464374510085)
                  ·
                    refine ⟨282409567486774570220641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1506184359929464374510085 282409567486774570220641)
                    ·
                      rfl

theorem cell23_1649972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_1649972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1649972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1649972 prefixEnd_1649972 := by exact prefixLift 1649972
  have htrace : WordTrace (prefixWord ++ tailWord_1649972) baseStart_1649972 baseEnd_1649972 := by
    simpa [prefixWord, tailWord_1649972, baseEnd_1649972] using wordTrace_append hprefix tailTrace_1649972
  have hstable : (prefixWord ++ tailWord_1649972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1649972).length < 2 ^ (prefixWord ++ tailWord_1649972).sum := by decide
  have hdescent : baseEnd_1649972 < baseStart_1649972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1649972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650008 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 1, 4, 5]
def baseStart_1650008 : Nat := 118140960795 + 1650008 * 2 ^ 59
def prefixEnd_1650008 : Nat := 4983230072969 + 3 ^ 40 * 1650008 * 2
def baseEnd_1650008 : Nat := 847247187763885569811757

theorem tailTrace_1650008 : CollatzResearch.WordTrace tailWord_1650008 prefixEnd_1650008 847247187763885569811757 := by
  unfold tailWord_1650008
  simp only [CollatzResearch.WordTrace]
  refine ⟨30090367903155144888175339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40120490537540193184233785 30090367903155144888175339)
  ·
    refine ⟨45135551854732717332263009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30090367903155144888175339 45135551854732717332263009)
    ·
      refine ⟨33851663891049537999197257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45135551854732717332263009 33851663891049537999197257)
      ·
        refine ⟨25388747918287153499397943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33851663891049537999197257 25388747918287153499397943)
        ·
          refine ⟨38083121877430730249096915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25388747918287153499397943 38083121877430730249096915)
          ·
            refine ⟨57124682816146095373645373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38083121877430730249096915 57124682816146095373645373)
            ·
              refine ⟨21421756056054785765117015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57124682816146095373645373 21421756056054785765117015)
              ·
                refine ⟨32132634084082178647675523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21421756056054785765117015 32132634084082178647675523)
                ·
                  refine ⟨48198951126123267971513285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32132634084082178647675523 48198951126123267971513285)
                  ·
                    refine ⟨9037303336148112744658741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48198951126123267971513285 9037303336148112744658741)
                    ·
                      refine ⟨847247187763885569811757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9037303336148112744658741 847247187763885569811757)
                      ·
                        rfl

theorem cell23_1650008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_1650008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650008 prefixEnd_1650008 := by exact prefixLift 1650008
  have htrace : WordTrace (prefixWord ++ tailWord_1650008) baseStart_1650008 baseEnd_1650008 := by
    simpa [prefixWord, tailWord_1650008, baseEnd_1650008] using wordTrace_append hprefix tailTrace_1650008
  have hstable : (prefixWord ++ tailWord_1650008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650008).length < 2 ^ (prefixWord ++ tailWord_1650008).sum := by decide
  have hdescent : baseEnd_1650008 < baseStart_1650008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650030 : List Nat := [4, 1, 2, 4, 2, 1, 1, 1, 3, 2, 2]
def baseStart_1650030 : Nat := 118140960795 + 1650030 * 2 ^ 59
def prefixEnd_1650030 : Nat := 4983230072969 + 3 ^ 40 * 1650030 * 2
def baseEnd_1650030 : Nat := 847258484338284483736657

theorem tailTrace_1650030 : CollatzResearch.WordTrace tailWord_1650030 prefixEnd_1650030 847258484338284483736657 := by
  unfold tailWord_1650030
  simp only [CollatzResearch.WordTrace]
  refine ⟨7522692276528823441706443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40121025474820391689101029 7522692276528823441706443)
  ·
    refine ⟨11284038414793235162559665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7522692276528823441706443 11284038414793235162559665)
    ·
      refine ⟨8463028811094926371919749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11284038414793235162559665 8463028811094926371919749)
      ·
        refine ⟨1586817902080298694734953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8463028811094926371919749 1586817902080298694734953)
        ·
          refine ⟨1190113426560224021051215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1586817902080298694734953 1190113426560224021051215)
          ·
            refine ⟨1785170139840336031576823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190113426560224021051215 1785170139840336031576823)
            ·
              refine ⟨2677755209760504047365235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1785170139840336031576823 2677755209760504047365235)
              ·
                refine ⟨4016632814640756071047853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677755209760504047365235 4016632814640756071047853)
                ·
                  refine ⟨1506237305490283526642945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4016632814640756071047853 1506237305490283526642945)
                  ·
                    refine ⟨1129677979117712644982209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1506237305490283526642945 1129677979117712644982209)
                    ·
                      refine ⟨847258484338284483736657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1129677979117712644982209 847258484338284483736657)
                      ·
                        rfl

theorem cell23_1650030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_1650030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650030 prefixEnd_1650030 := by exact prefixLift 1650030
  have htrace : WordTrace (prefixWord ++ tailWord_1650030) baseStart_1650030 baseEnd_1650030 := by
    simpa [prefixWord, tailWord_1650030, baseEnd_1650030] using wordTrace_append hprefix tailTrace_1650030
  have hstable : (prefixWord ++ tailWord_1650030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650030).length < 2 ^ (prefixWord ++ tailWord_1650030).sum := by decide
  have hdescent : baseEnd_1650030 < baseStart_1650030 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650035 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 2, 8, 2]
def baseStart_1650035 : Nat := 118140960795 + 1650035 * 2 ^ 59
def prefixEnd_1650035 : Nat := 4983230072969 + 3 ^ 40 * 1650035 * 2
def baseEnd_1650035 : Nat := 847261051741556964174133

theorem tailTrace_1650035 : CollatzResearch.WordTrace tailWord_1650035 prefixEnd_1650035 847261051741556964174133 := by
  unfold tailWord_1650035
  simp only [CollatzResearch.WordTrace]
  refine ⟨60181720577212473387583559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40121147051474982258389039 60181720577212473387583559)
  ·
    refine ⟨90272580865818710081375339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60181720577212473387583559 90272580865818710081375339)
    ·
      refine ⟨135408871298728065122063009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90272580865818710081375339 135408871298728065122063009)
      ·
        refine ⟨101556653474046048841547257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135408871298728065122063009 101556653474046048841547257)
        ·
          refine ⟨76167490105534536631160443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101556653474046048841547257 76167490105534536631160443)
          ·
            refine ⟨114251235158301804946740665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76167490105534536631160443 114251235158301804946740665)
            ·
              refine ⟨85688426368726353710055499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114251235158301804946740665 85688426368726353710055499)
              ·
                refine ⟨128532639553089530565083249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85688426368726353710055499 128532639553089530565083249)
                ·
                  refine ⟨96399479664817147923812437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128532639553089530565083249 96399479664817147923812437)
                  ·
                    refine ⟨1129681402322075952232177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96399479664817147923812437 1129681402322075952232177)
                    ·
                      refine ⟨847261051741556964174133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1129681402322075952232177 847261051741556964174133)
                      ·
                        rfl

theorem cell23_1650035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 8, 2].length) (baseStart_1650035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650035 prefixEnd_1650035 := by exact prefixLift 1650035
  have htrace : WordTrace (prefixWord ++ tailWord_1650035) baseStart_1650035 baseEnd_1650035 := by
    simpa [prefixWord, tailWord_1650035, baseEnd_1650035] using wordTrace_append hprefix tailTrace_1650035
  have hstable : (prefixWord ++ tailWord_1650035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650035).length < 2 ^ (prefixWord ++ tailWord_1650035).sum := by decide
  have hdescent : baseEnd_1650035 < baseStart_1650035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650048 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 6]
def baseStart_1650048 : Nat := 118140960795 + 1650048 * 2 ^ 59
def prefixEnd_1650048 : Nat := 4983230072969 + 3 ^ 40 * 1650048 * 2
def baseEnd_1650048 : Nat := 847267726990065413311573

theorem tailTrace_1650048 : CollatzResearch.WordTrace tailWord_1650048 prefixEnd_1650048 847267726990065413311573 := by
  unfold tailWord_1650048
  simp only [CollatzResearch.WordTrace]
  refine ⟨30091097363082688303903399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40121463150776917738537865 30091097363082688303903399)
  ·
    refine ⟨45136646044624032455855099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30091097363082688303903399 45136646044624032455855099)
    ·
      refine ⟨67704969066936048683782649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45136646044624032455855099 67704969066936048683782649)
      ·
        refine ⟨50778726800202036512836987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67704969066936048683782649 50778726800202036512836987)
        ·
          refine ⟨76168090200303054769255481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50778726800202036512836987 76168090200303054769255481)
          ·
            refine ⟨57126067650227291076941611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76168090200303054769255481 57126067650227291076941611)
            ·
              refine ⟨85689101475340936615412417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57126067650227291076941611 85689101475340936615412417)
              ·
                refine ⟨64266826106505702461559313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85689101475340936615412417 64266826106505702461559313)
                ·
                  refine ⟨48200119579879276846169485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64266826106505702461559313 48200119579879276846169485)
                  ·
                    refine ⟨18075044842454728817313557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48200119579879276846169485 18075044842454728817313557)
                    ·
                      refine ⟨847267726990065413311573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18075044842454728817313557 847267726990065413311573)
                      ·
                        rfl

theorem cell23_1650048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 2, 3, 6].length) (baseStart_1650048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650048 prefixEnd_1650048 := by exact prefixLift 1650048
  have htrace : WordTrace (prefixWord ++ tailWord_1650048) baseStart_1650048 baseEnd_1650048 := by
    simpa [prefixWord, tailWord_1650048, baseEnd_1650048] using wordTrace_append hprefix tailTrace_1650048
  have hstable : (prefixWord ++ tailWord_1650048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650048).length < 2 ^ (prefixWord ++ tailWord_1650048).sum := by decide
  have hdescent : baseEnd_1650048 < baseStart_1650048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650055 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_1650055 : Nat := 118140960795 + 1650055 * 2 ^ 59
def prefixEnd_1650055 : Nat := 4983230072969 + 3 ^ 40 * 1650055 * 2
def baseEnd_1650055 : Nat := 847271321354646885924041

theorem tailTrace_1650055 : CollatzResearch.WordTrace tailWord_1650055 prefixEnd_1650055 847271321354646885924041 := by
  unfold tailWord_1650055
  simp only [CollatzResearch.WordTrace]
  refine ⟨60182450037140016803311619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40121633358093344535541079 60182450037140016803311619)
  ·
    refine ⟨90273675055710025204967429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60182450037140016803311619 90273675055710025204967429)
    ·
      refine ⟨16926314072945629725931393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90273675055710025204967429 16926314072945629725931393)
      ·
        refine ⟨12694735554709222294448545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16926314072945629725931393 12694735554709222294448545)
        ·
          refine ⟨9521051666031916720836409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12694735554709222294448545 9521051666031916720836409)
          ·
            refine ⟨7140788749523937540627307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9521051666031916720836409 7140788749523937540627307)
            ·
              refine ⟨10711183124285906310940961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7140788749523937540627307 10711183124285906310940961)
              ·
                refine ⟨8033387343214429733205721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10711183124285906310940961 8033387343214429733205721)
                ·
                  refine ⟨6025040507410822299904291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8033387343214429733205721 6025040507410822299904291)
                  ·
                    refine ⟨9037560761116233449856437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6025040507410822299904291 9037560761116233449856437)
                    ·
                      refine ⟨847271321354646885924041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9037560761116233449856437 847271321354646885924041)
                      ·
                        rfl

theorem cell23_1650055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_1650055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650055 prefixEnd_1650055 := by exact prefixLift 1650055
  have htrace : WordTrace (prefixWord ++ tailWord_1650055) baseStart_1650055 baseEnd_1650055 := by
    simpa [prefixWord, tailWord_1650055, baseEnd_1650055] using wordTrace_append hprefix tailTrace_1650055
  have hstable : (prefixWord ++ tailWord_1650055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650055).length < 2 ^ (prefixWord ++ tailWord_1650055).sum := by decide
  have hdescent : baseEnd_1650055 < baseStart_1650055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650056 : List Nat := [2, 1, 3, 3, 1, 4, 1, 2, 1, 3, 2]
def baseStart_1650056 : Nat := 118140960795 + 1650056 * 2 ^ 59
def prefixEnd_1650056 : Nat := 4983230072969 + 3 ^ 40 * 1650056 * 2
def baseEnd_1650056 : Nat := 847271834835301382011537

theorem tailTrace_1650056 : CollatzResearch.WordTrace tailWord_1650056 prefixEnd_1650056 847271834835301382011537 := by
  unfold tailWord_1650056
  simp only [CollatzResearch.WordTrace]
  refine ⟨30091243255068196987049011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40121657673424262649398681 30091243255068196987049011)
  ·
    refine ⟨45136864882602295480573517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30091243255068196987049011 45136864882602295480573517)
    ·
      refine ⟨16926324330975860805215069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45136864882602295480573517 16926324330975860805215069)
      ·
        refine ⟨6347371624115947801955651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16926324330975860805215069 6347371624115947801955651)
        ·
          refine ⟨9521057436173921702933477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6347371624115947801955651 9521057436173921702933477)
          ·
            refine ⟨1785198269282610319300027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9521057436173921702933477 1785198269282610319300027)
            ·
              refine ⟨2677797403923915478950041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1785198269282610319300027 2677797403923915478950041)
              ·
                refine ⟨2008348052942936609212531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2677797403923915478950041 2008348052942936609212531)
                ·
                  refine ⟨3012522079414404913818797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2008348052942936609212531 3012522079414404913818797)
                  ·
                    refine ⟨1129695779780401842682049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3012522079414404913818797 1129695779780401842682049)
                    ·
                      refine ⟨847271834835301382011537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1129695779780401842682049 847271834835301382011537)
                      ·
                        rfl

theorem cell23_1650056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_1650056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650056 prefixEnd_1650056 := by exact prefixLift 1650056
  have htrace : WordTrace (prefixWord ++ tailWord_1650056) baseStart_1650056 baseEnd_1650056 := by
    simpa [prefixWord, tailWord_1650056, baseEnd_1650056] using wordTrace_append hprefix tailTrace_1650056
  have hstable : (prefixWord ++ tailWord_1650056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650056).length < 2 ^ (prefixWord ++ tailWord_1650056).sum := by decide
  have hdescent : baseEnd_1650056 < baseStart_1650056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650122 : List Nat := [3, 1, 2, 1, 2, 3, 3, 1, 2, 5]
def baseStart_1650122 : Nat := 118140960795 + 1650122 * 2 ^ 59
def prefixEnd_1650122 : Nat := 4983230072969 + 3 ^ 40 * 1650122 * 2
def baseEnd_1650122 : Nat := 282435241519499374595411

theorem tailTrace_1650122 : CollatzResearch.WordTrace tailWord_1650122 prefixEnd_1650122 282435241519499374595411 := by
  unfold tailWord_1650122
  simp only [CollatzResearch.WordTrace]
  refine ⟨15046223431974321811500155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40123262485264858164000413 15046223431974321811500155)
  ·
    refine ⟨22569335147961482717250233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15046223431974321811500155 22569335147961482717250233)
    ·
      refine ⟨16927001360971112037937675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22569335147961482717250233 16927001360971112037937675)
      ·
        refine ⟨25390502041456668056906513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16927001360971112037937675 25390502041456668056906513)
        ·
          refine ⟨19042876531092501042679885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25390502041456668056906513 19042876531092501042679885)
          ·
            refine ⟨7141078699159687891004957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19042876531092501042679885 7141078699159687891004957)
            ·
              refine ⟨2677904512184882959126859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7141078699159687891004957 2677904512184882959126859)
              ·
                refine ⟨4016856768277324438690289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2677904512184882959126859 4016856768277324438690289)
                ·
                  refine ⟨3012642576207993329017717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4016856768277324438690289 3012642576207993329017717)
                  ·
                    refine ⟨282435241519499374595411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3012642576207993329017717 282435241519499374595411)
                    ·
                      rfl

theorem cell23_1650122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_1650122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650122 prefixEnd_1650122 := by exact prefixLift 1650122
  have htrace : WordTrace (prefixWord ++ tailWord_1650122) baseStart_1650122 baseEnd_1650122 := by
    simpa [prefixWord, tailWord_1650122, baseEnd_1650122] using wordTrace_append hprefix tailTrace_1650122
  have hstable : (prefixWord ++ tailWord_1650122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650122).length < 2 ^ (prefixWord ++ tailWord_1650122).sum := by decide
  have hdescent : baseEnd_1650122 < baseStart_1650122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650186 : List Nat := [3, 1, 2, 2, 2, 2, 3, 3, 1, 4]
def baseStart_1650186 : Nat := 118140960795 + 1650186 * 2 ^ 59
def prefixEnd_1650186 : Nat := 4983230072969 + 3 ^ 40 * 1650186 * 2
def baseEnd_1650186 : Nat := 282446195773461957795313

theorem tailTrace_1650186 : CollatzResearch.WordTrace tailWord_1650186 prefixEnd_1650186 282446195773461957795313 := by
  unfold tailWord_1650186
  simp only [CollatzResearch.WordTrace]
  refine ⟨15046806999916356544082603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40124818666443617450886941 15046806999916356544082603)
  ·
    refine ⟨22570210499874534816123905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15046806999916356544082603 22570210499874534816123905)
    ·
      refine ⟨16927657874905901112092929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22570210499874534816123905 16927657874905901112092929)
      ·
        refine ⟨12695743406179425834069697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16927657874905901112092929 12695743406179425834069697)
        ·
          refine ⟨9521807554634569375552273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12695743406179425834069697 9521807554634569375552273)
          ·
            refine ⟨7141355665975927031664205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9521807554634569375552273 7141355665975927031664205)
            ·
              refine ⟨2678008374740972636874077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7141355665975927031664205 2678008374740972636874077)
              ·
                refine ⟨1004253140527864738827779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2678008374740972636874077 1004253140527864738827779)
                ·
                  refine ⟨1506379710791797108241669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1004253140527864738827779 1506379710791797108241669)
                  ·
                    refine ⟨282446195773461957795313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1506379710791797108241669 282446195773461957795313)
                    ·
                      rfl

theorem cell23_1650186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 3, 3, 1, 4].length) (baseStart_1650186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650186 prefixEnd_1650186 := by exact prefixLift 1650186
  have htrace : WordTrace (prefixWord ++ tailWord_1650186) baseStart_1650186 baseEnd_1650186 := by
    simpa [prefixWord, tailWord_1650186, baseEnd_1650186] using wordTrace_append hprefix tailTrace_1650186
  have hstable : (prefixWord ++ tailWord_1650186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650186).length < 2 ^ (prefixWord ++ tailWord_1650186).sum := by decide
  have hdescent : baseEnd_1650186 < baseStart_1650186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650229 : List Nat := [1, 3, 3, 1, 1, 3, 3, 2, 1, 5]
def baseStart_1650229 : Nat := 118140960795 + 1650229 * 2 ^ 59
def prefixEnd_1650229 : Nat := 4983230072969 + 3 ^ 40 * 1650229 * 2
def baseEnd_1650229 : Nat := 282453555662843068382747

theorem tailTrace_1650229 : CollatzResearch.WordTrace tailWord_1650229 prefixEnd_1650229 282453555662843068382747 := by
  unfold tailWord_1650229
  simp only [CollatzResearch.WordTrace]
  refine ⟨60188796338509644520145741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40125864225673096346763827 60188796338509644520145741)
  ·
    refine ⟨22570798626941116695054653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60188796338509644520145741 22570798626941116695054653)
    ·
      refine ⟨8464049485102918760645495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22570798626941116695054653 8464049485102918760645495)
      ·
        refine ⟨12696074227654378140968243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8464049485102918760645495 12696074227654378140968243)
        ·
          refine ⟨19044111341481567211452365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12696074227654378140968243 19044111341481567211452365)
          ·
            refine ⟨7141541753055587704294637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19044111341481567211452365 7141541753055587704294637)
            ·
              refine ⟨2678078157395845389110489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7141541753055587704294637 2678078157395845389110489)
              ·
                refine ⟨2008558618046884041832867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2678078157395845389110489 2008558618046884041832867)
                ·
                  refine ⟨3012837927070326062749301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2008558618046884041832867 3012837927070326062749301)
                  ·
                    refine ⟨282453555662843068382747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3012837927070326062749301 282453555662843068382747)
                    ·
                      rfl

theorem cell23_1650229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_1650229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650229 prefixEnd_1650229 := by exact prefixLift 1650229
  have htrace : WordTrace (prefixWord ++ tailWord_1650229) baseStart_1650229 baseEnd_1650229 := by
    simpa [prefixWord, tailWord_1650229, baseEnd_1650229] using wordTrace_append hprefix tailTrace_1650229
  have hstable : (prefixWord ++ tailWord_1650229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650229).length < 2 ^ (prefixWord ++ tailWord_1650229).sum := by decide
  have hdescent : baseEnd_1650229 < baseStart_1650229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650299 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 4, 1, 3]
def baseStart_1650299 : Nat := 118140960795 + 1650299 * 2 ^ 59
def prefixEnd_1650299 : Nat := 4983230072969 + 3 ^ 40 * 1650299 * 2
def baseEnd_1650299 : Nat := 847396610634343931272919

theorem tailTrace_1650299 : CollatzResearch.WordTrace tailWord_1650299 prefixEnd_1650299 847396610634343931272919 := by
  unfold tailWord_1650299
  simp only [CollatzResearch.WordTrace]
  refine ⟨60191349448256046475193951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40127566298837364316795967 60191349448256046475193951)
  ·
    refine ⟨90287024172384069712790927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60191349448256046475193951 90287024172384069712790927)
    ·
      refine ⟨135430536258576104569186391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90287024172384069712790927 135430536258576104569186391)
      ·
        refine ⟨203145804387864156853779587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135430536258576104569186391 203145804387864156853779587)
        ·
          refine ⟨304718706581796235280669381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203145804387864156853779587 304718706581796235280669381)
          ·
            refine ⟨57134757484086794115125509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304718706581796235280669381 57134757484086794115125509)
            ·
              refine ⟨10712767028266273896586033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57134757484086794115125509 10712767028266273896586033)
              ·
                refine ⟨8034575271199705422439525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10712767028266273896586033 8034575271199705422439525)
                ·
                  refine ⟨1506482863349944766707411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8034575271199705422439525 1506482863349944766707411)
                  ·
                    refine ⟨2259724295024917150061117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1506482863349944766707411 2259724295024917150061117)
                    ·
                      refine ⟨847396610634343931272919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2259724295024917150061117 847396610634343931272919)
                      ·
                        rfl

theorem cell23_1650299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 4, 1, 3].length) (baseStart_1650299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650299 prefixEnd_1650299 := by exact prefixLift 1650299
  have htrace : WordTrace (prefixWord ++ tailWord_1650299) baseStart_1650299 baseEnd_1650299 := by
    simpa [prefixWord, tailWord_1650299, baseEnd_1650299] using wordTrace_append hprefix tailTrace_1650299
  have hstable : (prefixWord ++ tailWord_1650299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650299).length < 2 ^ (prefixWord ++ tailWord_1650299).sum := by decide
  have hdescent : baseEnd_1650299 < baseStart_1650299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650352 : List Nat := [2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 4]
def baseStart_1650352 : Nat := 118140960795 + 1650352 * 2 ^ 59
def prefixEnd_1650352 : Nat := 4983230072969 + 3 ^ 40 * 1650352 * 2
def baseEnd_1650352 : Nat := 847423825109032223910175

theorem tailTrace_1650352 : CollatzResearch.WordTrace tailWord_1650352 prefixEnd_1650352 847423825109032223910175 := by
  unfold tailWord_1650352
  simp only [CollatzResearch.WordTrace]
  refine ⟨30096641258532018263436655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40128855011376024351248873 30096641258532018263436655)
  ·
    refine ⟨45144961887798027395154983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30096641258532018263436655 45144961887798027395154983)
    ·
      refine ⟨67717442831697041092732475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45144961887798027395154983 67717442831697041092732475)
      ·
        refine ⟨101576164247545561639098713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67717442831697041092732475 101576164247545561639098713)
        ·
          refine ⟨76182123185659171229324035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101576164247545561639098713 76182123185659171229324035)
          ·
            refine ⟨114273184778488756843986053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76182123185659171229324035 114273184778488756843986053)
            ·
              refine ⟨21426222145966641908247385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114273184778488756843986053 21426222145966641908247385)
              ·
                refine ⟨16069666609474981431185539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21426222145966641908247385 16069666609474981431185539)
                ·
                  refine ⟨24104499914212472146778309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16069666609474981431185539 24104499914212472146778309)
                  ·
                    refine ⟨4519593733914838527520933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24104499914212472146778309 4519593733914838527520933)
                    ·
                      refine ⟨847423825109032223910175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4519593733914838527520933 847423825109032223910175)
                      ·
                        rfl

theorem cell23_1650352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 4].length) (baseStart_1650352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650352 prefixEnd_1650352 := by exact prefixLift 1650352
  have htrace : WordTrace (prefixWord ++ tailWord_1650352) baseStart_1650352 baseEnd_1650352 := by
    simpa [prefixWord, tailWord_1650352, baseEnd_1650352] using wordTrace_append hprefix tailTrace_1650352
  have hstable : (prefixWord ++ tailWord_1650352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650352).length < 2 ^ (prefixWord ++ tailWord_1650352).sum := by decide
  have hdescent : baseEnd_1650352 < baseStart_1650352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650359 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 5]
def baseStart_1650359 : Nat := 118140960795 + 1650359 * 2 ^ 59
def prefixEnd_1650359 : Nat := 4983230072969 + 3 ^ 40 * 1650359 * 2
def baseEnd_1650359 : Nat := 847427419473613696522643

theorem tailTrace_1650359 : CollatzResearch.WordTrace tailWord_1650359 prefixEnd_1650359 847427419473613696522643 := by
  unfold tailWord_1650359
  simp only [CollatzResearch.WordTrace]
  refine ⟨60193537828038676722378131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40129025218692451148252087 60193537828038676722378131)
  ·
    refine ⟨90290306742058015083567197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60193537828038676722378131 90290306742058015083567197)
    ·
      refine ⟨33858865028271755656337699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90290306742058015083567197 33858865028271755656337699)
      ·
        refine ⟨50788297542407633484506549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33858865028271755656337699 50788297542407633484506549)
        ·
          refine ⟨4761402894600715639172489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50788297542407633484506549 4761402894600715639172489)
          ·
            refine ⟨3571052170950536729379367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4761402894600715639172489 3571052170950536729379367)
            ·
              refine ⟨5356578256425805094069051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3571052170950536729379367 5356578256425805094069051)
              ·
                refine ⟨8034867384638707641103577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5356578256425805094069051 8034867384638707641103577)
                ·
                  refine ⟨6026150538479030730827683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8034867384638707641103577 6026150538479030730827683)
                  ·
                    refine ⟨9039225807718546096241525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6026150538479030730827683 9039225807718546096241525)
                    ·
                      refine ⟨847427419473613696522643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9039225807718546096241525 847427419473613696522643)
                      ·
                        rfl

theorem cell23_1650359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 2, 1, 5].length) (baseStart_1650359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650359 prefixEnd_1650359 := by exact prefixLift 1650359
  have htrace : WordTrace (prefixWord ++ tailWord_1650359) baseStart_1650359 baseEnd_1650359 := by
    simpa [prefixWord, tailWord_1650359, baseEnd_1650359] using wordTrace_append hprefix tailTrace_1650359
  have hstable : (prefixWord ++ tailWord_1650359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650359).length < 2 ^ (prefixWord ++ tailWord_1650359).sum := by decide
  have hdescent : baseEnd_1650359 < baseStart_1650359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650379 : List Nat := [1, 1, 1, 1, 3, 2, 1, 8, 5]
def baseStart_1650379 : Nat := 118140960795 + 1650379 * 2 ^ 59
def prefixEnd_1650379 : Nat := 4983230072969 + 3 ^ 40 * 1650379 * 2
def baseEnd_1650379 : Nat := 94159743231855957585839

theorem tailTrace_1650379 : CollatzResearch.WordTrace tailWord_1650379 prefixEnd_1650379 94159743231855957585839 := by
  unfold tailWord_1650379
  simp only [CollatzResearch.WordTrace]
  refine ⟨60194267287966220138106191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40129511525310813425404127 60194267287966220138106191)
  ·
    refine ⟨90291400931949330207159287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60194267287966220138106191 90291400931949330207159287)
    ·
      refine ⟨135437101397923995310738931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90291400931949330207159287 135437101397923995310738931)
      ·
        refine ⟨203155652096885992966108397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135437101397923995310738931 203155652096885992966108397)
        ·
          refine ⟨76183369536332247362290649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203155652096885992966108397 76183369536332247362290649)
          ·
            refine ⟨57137527152249185521717987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76183369536332247362290649 57137527152249185521717987)
            ·
              refine ⟨85706290728373778282576981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57137527152249185521717987 85706290728373778282576981)
              ·
                refine ⟨1004370594473130214248949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 85706290728373778282576981 1004370594473130214248949)
                ·
                  refine ⟨94159743231855957585839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1004370594473130214248949 94159743231855957585839)
                  ·
                    rfl

theorem cell23_1650379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 5].length) (baseStart_1650379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650379 prefixEnd_1650379 := by exact prefixLift 1650379
  have htrace : WordTrace (prefixWord ++ tailWord_1650379) baseStart_1650379 baseEnd_1650379 := by
    simpa [prefixWord, tailWord_1650379, baseEnd_1650379] using wordTrace_append hprefix tailTrace_1650379
  have hstable : (prefixWord ++ tailWord_1650379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650379).length < 2 ^ (prefixWord ++ tailWord_1650379).sum := by decide
  have hdescent : baseEnd_1650379 < baseStart_1650379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650429 : List Nat := [1, 4, 1, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_1650429 : Nat := 118140960795 + 1650429 * 2 ^ 59
def prefixEnd_1650429 : Nat := 4983230072969 + 3 ^ 40 * 1650429 * 2
def baseEnd_1650429 : Nat := 847463363119428422647321

theorem tailTrace_1650429 : CollatzResearch.WordTrace tailWord_1650429 prefixEnd_1650429 847463363119428422647321 := by
  unfold tailWord_1650429
  simp only [CollatzResearch.WordTrace]
  refine ⟨60196090937785078677426341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40130727291856719118284227 60196090937785078677426341)
  ·
    refine ⟨11286767050834702252017439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60196090937785078677426341 11286767050834702252017439)
    ·
      refine ⟨16930150576252053378026159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11286767050834702252017439 16930150576252053378026159)
      ·
        refine ⟨25395225864378080067039239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16930150576252053378026159 25395225864378080067039239)
        ·
          refine ⟨38092838796567120100558859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25395225864378080067039239 38092838796567120100558859)
          ·
            refine ⟨57139258194850680150838289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38092838796567120100558859 57139258194850680150838289)
            ·
              refine ⟨42854443646138010113128717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57139258194850680150838289 42854443646138010113128717)
              ·
                refine ⟨16070416367301753792423269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42854443646138010113128717 16070416367301753792423269)
                ·
                  refine ⟨3013203068869078836079363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16070416367301753792423269 3013203068869078836079363)
                  ·
                    refine ⟨4519804603303618254119045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3013203068869078836079363 4519804603303618254119045)
                    ·
                      refine ⟨847463363119428422647321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4519804603303618254119045 847463363119428422647321)
                      ·
                        rfl

theorem cell23_1650429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_1650429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650429 prefixEnd_1650429 := by exact prefixLift 1650429
  have htrace : WordTrace (prefixWord ++ tailWord_1650429) baseStart_1650429 baseEnd_1650429 := by
    simpa [prefixWord, tailWord_1650429, baseEnd_1650429] using wordTrace_append hprefix tailTrace_1650429
  have hstable : (prefixWord ++ tailWord_1650429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650429).length < 2 ^ (prefixWord ++ tailWord_1650429).sum := by decide
  have hdescent : baseEnd_1650429 < baseStart_1650429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650446 : List Nat := [4, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2]
def baseStart_1650446 : Nat := 118140960795 + 1650446 * 2 ^ 59
def prefixEnd_1650446 : Nat := 4983230072969 + 3 ^ 40 * 1650446 * 2
def baseEnd_1650446 : Nat := 847472092290554856134743

theorem tailTrace_1650446 : CollatzResearch.WordTrace tailWord_1650446 prefixEnd_1650446 847472092290554856134743 := by
  unfold tailWord_1650446
  simp only [CollatzResearch.WordTrace]
  refine ⟨7524588872340436322599399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40131140652482327053863461 7524588872340436322599399)
  ·
    refine ⟨11286883308510654483899099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7524588872340436322599399 11286883308510654483899099)
    ·
      refine ⟨16930324962765981725848649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11286883308510654483899099 16930324962765981725848649)
      ·
        refine ⟨12697743722074486294386487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16930324962765981725848649 12697743722074486294386487)
        ·
          refine ⟨19046615583111729441579731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12697743722074486294386487 19046615583111729441579731)
          ·
            refine ⟨28569923374667594162369597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19046615583111729441579731 28569923374667594162369597)
            ·
              refine ⟨10713721265500347810888599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28569923374667594162369597 10713721265500347810888599)
              ·
                refine ⟨16070581898250521716332899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10713721265500347810888599 16070581898250521716332899)
                ·
                  refine ⟨24105872847375782574499349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16070581898250521716332899 24105872847375782574499349)
                  ·
                    refine ⟨1129962789720739808179657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24105872847375782574499349 1129962789720739808179657)
                    ·
                      refine ⟨847472092290554856134743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1129962789720739808179657 847472092290554856134743)
                      ·
                        rfl

theorem cell23_1650446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_1650446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650446 prefixEnd_1650446 := by exact prefixLift 1650446
  have htrace : WordTrace (prefixWord ++ tailWord_1650446) baseStart_1650446 baseEnd_1650446 := by
    simpa [prefixWord, tailWord_1650446, baseEnd_1650446] using wordTrace_append hprefix tailTrace_1650446
  have hstable : (prefixWord ++ tailWord_1650446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650446).length < 2 ^ (prefixWord ++ tailWord_1650446).sum := by decide
  have hdescent : baseEnd_1650446 < baseStart_1650446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650449 : List Nat := [1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 3]
def baseStart_1650449 : Nat := 118140960795 + 1650449 * 2 ^ 59
def prefixEnd_1650449 : Nat := 4983230072969 + 3 ^ 40 * 1650449 * 2
def baseEnd_1650449 : Nat := 847473632732518344397229

theorem tailTrace_1650449 : CollatzResearch.WordTrace tailWord_1650449 prefixEnd_1650449 847473632732518344397229 := by
  unfold tailWord_1650449
  simp only [CollatzResearch.WordTrace]
  refine ⟨60196820397712622093154401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40131213598475081395436267 60196820397712622093154401)
  ·
    refine ⟨45147615298284466569865801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60196820397712622093154401 45147615298284466569865801)
    ·
      refine ⟨33860711473713349927399351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45147615298284466569865801 33860711473713349927399351)
      ·
        refine ⟨50791067210570024891099027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33860711473713349927399351 50791067210570024891099027)
        ·
          refine ⟨76186600815855037336648541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50791067210570024891099027 76186600815855037336648541)
          ·
            refine ⟨28569975305945639001243203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76186600815855037336648541 28569975305945639001243203)
            ·
              refine ⟨42854962958918458501864805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28569975305945639001243203 42854962958918458501864805)
              ·
                refine ⟨8035305554797210969099651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42854962958918458501864805 8035305554797210969099651)
                ·
                  refine ⟨12052958332195816453649477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8035305554797210969099651 12052958332195816453649477)
                  ·
                    refine ⟨2259929687286715585059277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12052958332195816453649477 2259929687286715585059277)
                    ·
                      refine ⟨847473632732518344397229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2259929687286715585059277 847473632732518344397229)
                      ·
                        rfl

theorem cell23_1650449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_1650449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650449 prefixEnd_1650449 := by exact prefixLift 1650449
  have htrace : WordTrace (prefixWord ++ tailWord_1650449) baseStart_1650449 baseEnd_1650449 := by
    simpa [prefixWord, tailWord_1650449, baseEnd_1650449] using wordTrace_append hprefix tailTrace_1650449
  have hstable : (prefixWord ++ tailWord_1650449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650449).length < 2 ^ (prefixWord ++ tailWord_1650449).sum := by decide
  have hdescent : baseEnd_1650449 < baseStart_1650449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650466 : List Nat := [3, 3, 1, 1, 2, 1, 3, 1, 1, 4, 3]
def baseStart_1650466 : Nat := 118140960795 + 1650466 * 2 ^ 59
def prefixEnd_1650466 : Nat := 4983230072969 + 3 ^ 40 * 1650466 * 2
def baseEnd_1650466 : Nat := 847482361903644777884651

theorem tailTrace_1650466 : CollatzResearch.WordTrace tailWord_1650466 prefixEnd_1650466 847482361903644777884651 := by
  unfold tailWord_1650466
  simp only [CollatzResearch.WordTrace]
  refine ⟨15049360109662758499130813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40131626959100689331015501 15049360109662758499130813)
  ·
    refine ⟨5643510041123534437174055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15049360109662758499130813 5643510041123534437174055)
    ·
      refine ⟨8465265061685301655761083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5643510041123534437174055 8465265061685301655761083)
      ·
        refine ⟨12697897592527952483641625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8465265061685301655761083 12697897592527952483641625)
        ·
          refine ⟨9523423194395964362731219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12697897592527952483641625 9523423194395964362731219)
          ·
            refine ⟨14285134791593946544096829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9523423194395964362731219 14285134791593946544096829)
            ·
              refine ⟨5356925546847729954036311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14285134791593946544096829 5356925546847729954036311)
              ·
                refine ⟨8035388320271594931054467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5356925546847729954036311 8035388320271594931054467)
                ·
                  refine ⟨12053082480407392396581701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8035388320271594931054467 12053082480407392396581701)
                  ·
                    refine ⟨2259952965076386074359069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12053082480407392396581701 2259952965076386074359069)
                    ·
                      refine ⟨847482361903644777884651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2259952965076386074359069 847482361903644777884651)
                      ·
                        rfl

theorem cell23_1650466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_1650466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650466 prefixEnd_1650466 := by exact prefixLift 1650466
  have htrace : WordTrace (prefixWord ++ tailWord_1650466) baseStart_1650466 baseEnd_1650466 := by
    simpa [prefixWord, tailWord_1650466, baseEnd_1650466] using wordTrace_append hprefix tailTrace_1650466
  have hstable : (prefixWord ++ tailWord_1650466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650466).length < 2 ^ (prefixWord ++ tailWord_1650466).sum := by decide
  have hdescent : baseEnd_1650466 < baseStart_1650466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650506 : List Nat := [3, 1, 2, 1, 1, 1, 3, 1, 3, 5, 2]
def baseStart_1650506 : Nat := 118140960795 + 1650506 * 2 ^ 59
def prefixEnd_1650506 : Nat := 4983230072969 + 3 ^ 40 * 1650506 * 2
def baseEnd_1650506 : Nat := 847502901129824621384467

theorem tailTrace_1650506 : CollatzResearch.WordTrace tailWord_1650506 prefixEnd_1650506 847502901129824621384467 := by
  unfold tailWord_1650506
  simp only [CollatzResearch.WordTrace]
  refine ⟨15049724839626530206994843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40132599572337413885319581 15049724839626530206994843)
  ·
    refine ⟨22574587259439795310492265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15049724839626530206994843 22574587259439795310492265)
    ·
      refine ⟨16930940444579846482869199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22574587259439795310492265 16930940444579846482869199)
      ·
        refine ⟨25396410666869769724303799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16930940444579846482869199 25396410666869769724303799)
        ·
          refine ⟨38094616000304654586455699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25396410666869769724303799 38094616000304654586455699)
          ·
            refine ⟨57141924000456981879683549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38094616000304654586455699 57141924000456981879683549)
            ·
              refine ⟨21428221500171368204881331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57141924000456981879683549 21428221500171368204881331)
              ·
                refine ⟨32142332250257052307321997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21428221500171368204881331 32142332250257052307321997)
                ·
                  refine ⟨12053374593846394615245749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32142332250257052307321997 12053374593846394615245749)
                  ·
                    refine ⟨1130003868173099495179289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12053374593846394615245749 1130003868173099495179289)
                    ·
                      refine ⟨847502901129824621384467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1130003868173099495179289 847502901129824621384467)
                      ·
                        rfl

theorem cell23_1650506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 1, 3, 5, 2].length) (baseStart_1650506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650506 prefixEnd_1650506 := by exact prefixLift 1650506
  have htrace : WordTrace (prefixWord ++ tailWord_1650506) baseStart_1650506 baseEnd_1650506 := by
    simpa [prefixWord, tailWord_1650506, baseEnd_1650506] using wordTrace_append hprefix tailTrace_1650506
  have hstable : (prefixWord ++ tailWord_1650506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650506).length < 2 ^ (prefixWord ++ tailWord_1650506).sum := by decide
  have hdescent : baseEnd_1650506 < baseStart_1650506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650513 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 3, 1, 3]
def baseStart_1650513 : Nat := 118140960795 + 1650513 * 2 ^ 59
def prefixEnd_1650513 : Nat := 4983230072969 + 3 ^ 40 * 1650513 * 2
def baseEnd_1650513 : Nat := 847506495494406093996935

theorem tailTrace_1650513 : CollatzResearch.WordTrace tailWord_1650513 prefixEnd_1650513 847506495494406093996935 := by
  unfold tailWord_1650513
  simp only [CollatzResearch.WordTrace]
  refine ⟨60199154669480761023484193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40132769779653840682322795 60199154669480761023484193)
  ·
    refine ⟨45149366002110570767613145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60199154669480761023484193 45149366002110570767613145)
    ·
      refine ⟨33862024501582928075709859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45149366002110570767613145 33862024501582928075709859)
      ·
        refine ⟨50793036752374392113564789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33862024501582928075709859 50793036752374392113564789)
        ·
          refine ⟨4761847195535099260646699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50793036752374392113564789 4761847195535099260646699)
          ·
            refine ⟨7142770793302648890970049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4761847195535099260646699 7142770793302648890970049)
            ·
              refine ⟨5357078094976986668227537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7142770793302648890970049 5357078094976986668227537)
              ·
                refine ⟨4017808571232740001170653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5357078094976986668227537 4017808571232740001170653)
                ·
                  refine ⟨1506678214212277500438995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4017808571232740001170653 1506678214212277500438995)
                  ·
                    refine ⟨2260017321318416250658493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1506678214212277500438995 2260017321318416250658493)
                    ·
                      refine ⟨847506495494406093996935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2260017321318416250658493 847506495494406093996935)
                      ·
                        rfl

theorem cell23_1650513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_1650513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650513 prefixEnd_1650513 := by exact prefixLift 1650513
  have htrace : WordTrace (prefixWord ++ tailWord_1650513) baseStart_1650513 baseEnd_1650513 := by
    simpa [prefixWord, tailWord_1650513, baseEnd_1650513] using wordTrace_append hprefix tailTrace_1650513
  have hstable : (prefixWord ++ tailWord_1650513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650513).length < 2 ^ (prefixWord ++ tailWord_1650513).sum := by decide
  have hdescent : baseEnd_1650513 < baseStart_1650513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650524 : List Nat := [2, 2, 4, 2, 3, 1, 1, 3, 1, 4]
def baseStart_1650524 : Nat := 118140960795 + 1650524 * 2 ^ 59
def prefixEnd_1650524 : Nat := 4983230072969 + 3 ^ 40 * 1650524 * 2
def baseEnd_1650524 : Nat := 282504047927201850319795

theorem tailTrace_1650524 : CollatzResearch.WordTrace tailWord_1650524 prefixEnd_1650524 282504047927201850319795 := by
  unfold tailWord_1650524
  simp only [CollatzResearch.WordTrace]
  refine ⟨30099777936220454951067313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40133037248293939934756417 30099777936220454951067313)
  ·
    refine ⟨22574833452165341213300485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30099777936220454951067313 22574833452165341213300485)
    ·
      refine ⟨4232781272281001477493841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22574833452165341213300485 4232781272281001477493841)
      ·
        refine ⟨3174585954210751108120381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4232781272281001477493841 3174585954210751108120381)
        ·
          refine ⟨1190469732829031665545143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3174585954210751108120381 1190469732829031665545143)
          ·
            refine ⟨1785704599243547498317715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190469732829031665545143 1785704599243547498317715)
            ·
              refine ⟨2678556898865321247476573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1785704599243547498317715 2678556898865321247476573)
              ·
                refine ⟨1004458837074495467803715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2678556898865321247476573 1004458837074495467803715)
                ·
                  refine ⟨1506688255611743201705573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1004458837074495467803715 1506688255611743201705573)
                  ·
                    refine ⟨282504047927201850319795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1506688255611743201705573 282504047927201850319795)
                    ·
                      rfl

theorem cell23_1650524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_1650524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650524 prefixEnd_1650524 := by exact prefixLift 1650524
  have htrace : WordTrace (prefixWord ++ tailWord_1650524) baseStart_1650524 baseEnd_1650524 := by
    simpa [prefixWord, tailWord_1650524, baseEnd_1650524] using wordTrace_append hprefix tailTrace_1650524
  have hstable : (prefixWord ++ tailWord_1650524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650524).length < 2 ^ (prefixWord ++ tailWord_1650524).sum := by decide
  have hdescent : baseEnd_1650524 < baseStart_1650524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650529 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 3, 6]
def baseStart_1650529 : Nat := 118140960795 + 1650529 * 2 ^ 59
def prefixEnd_1650529 : Nat := 4983230072969 + 3 ^ 40 * 1650529 * 2
def baseEnd_1650529 : Nat := 282504903728292677132287

theorem tailTrace_1650529 : CollatzResearch.WordTrace tailWord_1650529 prefixEnd_1650529 282504903728292677132287 := by
  unfold tailWord_1650529
  simp only [CollatzResearch.WordTrace]
  refine ⟨60199738237422795756066641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40133158824948530504044427 60199738237422795756066641)
  ·
    refine ⟨45149803678067096817049981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60199738237422795756066641 45149803678067096817049981)
    ·
      refine ⟨16931176379275161306393743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45149803678067096817049981 16931176379275161306393743)
      ·
        refine ⟨25396764568912741959590615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16931176379275161306393743 25396764568912741959590615)
        ·
          refine ⟨38095146853369112939385923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25396764568912741959590615 38095146853369112939385923)
          ·
            refine ⟨57142720280053669409078885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38095146853369112939385923 57142720280053669409078885)
            ·
              refine ⟨10714260052510063014202291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57142720280053669409078885 10714260052510063014202291)
              ·
                refine ⟨16071390078765094521303437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10714260052510063014202291 16071390078765094521303437)
                ·
                  refine ⟨6026771279536910445488789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16071390078765094521303437 6026771279536910445488789)
                  ·
                    refine ⟨282504903728292677132287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6026771279536910445488789 282504903728292677132287)
                    ·
                      rfl

theorem cell23_1650529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_1650529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650529 prefixEnd_1650529 := by exact prefixLift 1650529
  have htrace : WordTrace (prefixWord ++ tailWord_1650529) baseStart_1650529 baseEnd_1650529 := by
    simpa [prefixWord, tailWord_1650529, baseEnd_1650529] using wordTrace_append hprefix tailTrace_1650529
  have hstable : (prefixWord ++ tailWord_1650529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650529).length < 2 ^ (prefixWord ++ tailWord_1650529).sum := by decide
  have hdescent : baseEnd_1650529 < baseStart_1650529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650563 : List Nat := [1, 1, 1, 3, 4, 3, 1, 3, 2, 4]
def baseStart_1650563 : Nat := 118140960795 + 1650563 * 2 ^ 59
def prefixEnd_1650563 : Nat := 4983230072969 + 3 ^ 40 * 1650563 * 2
def baseEnd_1650563 : Nat := 282510723175710299457235

theorem tailTrace_1650563 : CollatzResearch.WordTrace tailWord_1650563 prefixEnd_1650563 282510723175710299457235 := by
  unfold tailWord_1650563
  simp only [CollatzResearch.WordTrace]
  refine ⟨60200978319299619562804343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40133985546199746375202895 60200978319299619562804343)
  ·
    refine ⟨90301467478949429344206515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60200978319299619562804343 90301467478949429344206515)
    ·
      refine ⟨135452201218424144016309773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90301467478949429344206515 135452201218424144016309773)
      ·
        refine ⟨50794575456909054006116165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135452201218424144016309773 50794575456909054006116165)
        ·
          refine ⟨9523982898170447626146781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50794575456909054006116165 9523982898170447626146781)
          ·
            refine ⟨3571493586813917859805043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9523982898170447626146781 3571493586813917859805043)
            ·
              refine ⟨5357240380220876789707565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3571493586813917859805043 5357240380220876789707565)
              ·
                refine ⟨2008965142582828796140337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5357240380220876789707565 2008965142582828796140337)
                ·
                  refine ⟨1506723856937121597105253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2008965142582828796140337 1506723856937121597105253)
                  ·
                    refine ⟨282510723175710299457235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1506723856937121597105253 282510723175710299457235)
                    ·
                      rfl

theorem cell23_1650563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 1, 3, 2, 4].length) (baseStart_1650563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650563 prefixEnd_1650563 := by exact prefixLift 1650563
  have htrace : WordTrace (prefixWord ++ tailWord_1650563) baseStart_1650563 baseEnd_1650563 := by
    simpa [prefixWord, tailWord_1650563, baseEnd_1650563] using wordTrace_append hprefix tailTrace_1650563
  have hstable : (prefixWord ++ tailWord_1650563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650563).length < 2 ^ (prefixWord ++ tailWord_1650563).sum := by decide
  have hdescent : baseEnd_1650563 < baseStart_1650563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650619 : List Nat := [1, 1, 1, 1, 1, 2, 2, 5, 1, 8]
def baseStart_1650619 : Nat := 118140960795 + 1650619 * 2 ^ 59
def prefixEnd_1650619 : Nat := 4983230072969 + 3 ^ 40 * 1650619 * 2
def baseEnd_1650619 : Nat := 282520308147927559757149

theorem tailTrace_1650619 : CollatzResearch.WordTrace tailWord_1650619 prefixEnd_1650619 282520308147927559757149 := by
  unfold tailWord_1650619
  simp only [CollatzResearch.WordTrace]
  refine ⟨60203020807096741126842911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40135347204731160751228607 60203020807096741126842911)
  ·
    refine ⟨90304531210645111690264367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60203020807096741126842911 90304531210645111690264367)
    ·
      refine ⟨135456796815967667535396551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90304531210645111690264367 135456796815967667535396551)
      ·
        refine ⟨203185195223951501303094827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135456796815967667535396551 203185195223951501303094827)
        ·
          refine ⟨304777792835927251954642241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203185195223951501303094827 304777792835927251954642241)
          ·
            refine ⟨228583344626945438965981681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304777792835927251954642241 228583344626945438965981681)
            ·
              refine ⟨171437508470209079224486261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228583344626945438965981681 171437508470209079224486261)
              ·
                refine ⟨16072266419082101177295587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 171437508470209079224486261 16072266419082101177295587)
                ·
                  refine ⟨24108399628623151765943381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16072266419082101177295587 24108399628623151765943381)
                  ·
                    refine ⟨282520308147927559757149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24108399628623151765943381 282520308147927559757149)
                    ·
                      rfl

theorem cell23_1650619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 8].length) (baseStart_1650619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650619 prefixEnd_1650619 := by exact prefixLift 1650619
  have htrace : WordTrace (prefixWord ++ tailWord_1650619) baseStart_1650619 baseEnd_1650619 := by
    simpa [prefixWord, tailWord_1650619, baseEnd_1650619] using wordTrace_append hprefix tailTrace_1650619
  have hstable : (prefixWord ++ tailWord_1650619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650619).length < 2 ^ (prefixWord ++ tailWord_1650619).sum := by decide
  have hdescent : baseEnd_1650619 < baseStart_1650619 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650660 : List Nat := [2, 3, 1, 1, 1, 1, 5, 1, 4, 2, 2]
def baseStart_1650660 : Nat := 118140960795 + 1650660 * 2 ^ 59
def prefixEnd_1650660 : Nat := 4983230072969 + 3 ^ 40 * 1650660 * 2
def baseEnd_1650660 : Nat := 847581977150617018858759

theorem tailTrace_1650660 : CollatzResearch.WordTrace tailWord_1650660 prefixEnd_1650660 847581977150617018858759 := by
  unfold tailWord_1650660
  simp only [CollatzResearch.WordTrace]
  refine ⟨30102258099974102564542717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40136344133298803419390289 30102258099974102564542717)
  ·
    refine ⟨11288346787490288461703519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30102258099974102564542717 11288346787490288461703519)
    ·
      refine ⟨16932520181235432692555279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11288346787490288461703519 16932520181235432692555279)
      ·
        refine ⟨25398780271853149038832919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16932520181235432692555279 25398780271853149038832919)
        ·
          refine ⟨38098170407779723558249379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25398780271853149038832919 38098170407779723558249379)
          ·
            refine ⟨57147255611669585337374069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38098170407779723558249379 57147255611669585337374069)
            ·
              refine ⟨5357555213594023625378819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57147255611669585337374069 5357555213594023625378819)
              ·
                refine ⟨8036332820391035438068229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5357555213594023625378819 8036332820391035438068229)
                ·
                  refine ⟨1506812403823319144637793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8036332820391035438068229 1506812403823319144637793)
                  ·
                    refine ⟨1130109302867489358478345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1506812403823319144637793 1130109302867489358478345)
                    ·
                      refine ⟨847581977150617018858759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1130109302867489358478345 847581977150617018858759)
                      ·
                        rfl

theorem cell23_1650660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_1650660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650660 prefixEnd_1650660 := by exact prefixLift 1650660
  have htrace : WordTrace (prefixWord ++ tailWord_1650660) baseStart_1650660 baseEnd_1650660 := by
    simpa [prefixWord, tailWord_1650660, baseEnd_1650660] using wordTrace_append hprefix tailTrace_1650660
  have hstable : (prefixWord ++ tailWord_1650660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650660).length < 2 ^ (prefixWord ++ tailWord_1650660).sum := by decide
  have hdescent : baseEnd_1650660 < baseStart_1650660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650696 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 1, 7]
def baseStart_1650696 : Nat := 118140960795 + 1650696 * 2 ^ 59
def prefixEnd_1650696 : Nat := 4983230072969 + 3 ^ 40 * 1650696 * 2
def baseEnd_1650696 : Nat := 282533487484726292669531

theorem tailTrace_1650696 : CollatzResearch.WordTrace tailWord_1650696 prefixEnd_1650696 282533487484726292669531 := by
  unfold tailWord_1650696
  simp only [CollatzResearch.WordTrace]
  refine ⟨30102914613908891638697971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40137219485211855518263961 30102914613908891638697971)
  ·
    refine ⟨45154371920863337458046957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30102914613908891638697971 45154371920863337458046957)
    ·
      refine ⟨16932889470323751546767609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45154371920863337458046957 16932889470323751546767609)
      ·
        refine ⟨12699667102742813660075707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16932889470323751546767609 12699667102742813660075707)
        ·
          refine ⟨19049500654114220490113561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12699667102742813660075707 19049500654114220490113561)
          ·
            refine ⟨14287125490585665367585171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19049500654114220490113561 14287125490585665367585171)
            ·
              refine ⟨21430688235878498051377757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14287125490585665367585171 21430688235878498051377757)
              ·
                refine ⟨8036508088454436769266659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21430688235878498051377757 8036508088454436769266659)
                ·
                  refine ⟨12054762132681655153899989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8036508088454436769266659 12054762132681655153899989)
                  ·
                    refine ⟨282533487484726292669531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12054762132681655153899989 282533487484726292669531)
                    ·
                      rfl

theorem cell23_1650696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 1, 7].length) (baseStart_1650696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650696 prefixEnd_1650696 := by exact prefixLift 1650696
  have htrace : WordTrace (prefixWord ++ tailWord_1650696) baseStart_1650696 baseEnd_1650696 := by
    simpa [prefixWord, tailWord_1650696, baseEnd_1650696] using wordTrace_append hprefix tailTrace_1650696
  have hstable : (prefixWord ++ tailWord_1650696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650696).length < 2 ^ (prefixWord ++ tailWord_1650696).sum := by decide
  have hdescent : baseEnd_1650696 < baseStart_1650696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650717 : List Nat := [1, 4, 2, 2, 2, 2, 3, 2, 5]
def baseStart_1650717 : Nat := 118140960795 + 1650717 * 2 ^ 59
def prefixEnd_1650717 : Nat := 4983230072969 + 3 ^ 40 * 1650717 * 2
def baseEnd_1650717 : Nat := 94179027283102588427333

theorem tailTrace_1650717 : CollatzResearch.WordTrace tailWord_1650717 prefixEnd_1650717 94179027283102588427333 := by
  unfold tailWord_1650717
  simp only [CollatzResearch.WordTrace]
  refine ⟨60206595160741703863910405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40137730107161135909273603 60206595160741703863910405)
  ·
    refine ⟨11288736592639069474483201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60206595160741703863910405 11288736592639069474483201)
    ·
      refine ⟨8466552444479302105862401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11288736592639069474483201 8466552444479302105862401)
      ·
        refine ⟨6349914333359476579396801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8466552444479302105862401 6349914333359476579396801)
        ·
          refine ⟨4762435750019607434547601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6349914333359476579396801 4762435750019607434547601)
          ·
            refine ⟨3571826812514705575910701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4762435750019607434547601 3571826812514705575910701)
            ·
              refine ⟨1339435054693014590966513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3571826812514705575910701 1339435054693014590966513)
              ·
                refine ⟨1004576291019760943224885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1339435054693014590966513 1004576291019760943224885)
                ·
                  refine ⟨94179027283102588427333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1004576291019760943224885 94179027283102588427333)
                  ·
                    rfl

theorem cell23_1650717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_1650717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650717 prefixEnd_1650717 := by exact prefixLift 1650717
  have htrace : WordTrace (prefixWord ++ tailWord_1650717) baseStart_1650717 baseEnd_1650717 := by
    simpa [prefixWord, tailWord_1650717, baseEnd_1650717] using wordTrace_append hprefix tailTrace_1650717
  have hstable : (prefixWord ++ tailWord_1650717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650717).length < 2 ^ (prefixWord ++ tailWord_1650717).sum := by decide
  have hdescent : baseEnd_1650717 < baseStart_1650717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650728 : List Nat := [2, 1, 5, 3, 1, 2, 2, 1, 2, 2, 2]
def baseStart_1650728 : Nat := 118140960795 + 1650728 * 2 ^ 59
def prefixEnd_1650728 : Nat := 4983230072969 + 3 ^ 40 * 1650728 * 2
def baseEnd_1650728 : Nat := 847616893835122752808447

theorem tailTrace_1650728 : CollatzResearch.WordTrace tailWord_1650728 prefixEnd_1650728 847616893835122752808447 := by
  unfold tailWord_1650728
  simp only [CollatzResearch.WordTrace]
  refine ⟨30103498181850926371280419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40137997575801235161707225 30103498181850926371280419)
  ·
    refine ⟨45155247272776389556920629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30103498181850926371280419 45155247272776389556920629)
    ·
      refine ⟨4233304431822786520961309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45155247272776389556920629 4233304431822786520961309)
      ·
        refine ⟨1587489161933544945360491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4233304431822786520961309 1587489161933544945360491)
        ·
          refine ⟨2381233742900317418040737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1587489161933544945360491 2381233742900317418040737)
          ·
            refine ⟨1785925307175238063530553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2381233742900317418040737 1785925307175238063530553)
            ·
              refine ⟨1339443980381428547647915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1785925307175238063530553 1339443980381428547647915)
              ·
                refine ⟨2009165970572142821471873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339443980381428547647915 2009165970572142821471873)
                ·
                  refine ⟨1506874477929107116103905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2009165970572142821471873 1506874477929107116103905)
                  ·
                    refine ⟨1130155858446830337077929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1506874477929107116103905 1130155858446830337077929)
                    ·
                      refine ⟨847616893835122752808447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1130155858446830337077929 847616893835122752808447)
                      ·
                        rfl

theorem cell23_1650728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_1650728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650728 prefixEnd_1650728 := by exact prefixLift 1650728
  have htrace : WordTrace (prefixWord ++ tailWord_1650728) baseStart_1650728 baseEnd_1650728 := by
    simpa [prefixWord, tailWord_1650728, baseEnd_1650728] using wordTrace_append hprefix tailTrace_1650728
  have hstable : (prefixWord ++ tailWord_1650728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650728).length < 2 ^ (prefixWord ++ tailWord_1650728).sum := by decide
  have hdescent : baseEnd_1650728 < baseStart_1650728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650743 : List Nat := [1, 1, 3, 1, 2, 2, 2, 4, 3, 4]
def baseStart_1650743 : Nat := 118140960795 + 1650743 * 2 ^ 59
def prefixEnd_1650743 : Nat := 4983230072969 + 3 ^ 40 * 1650743 * 2
def baseEnd_1650743 : Nat := 282541532014980064706959

theorem tailTrace_1650743 : CollatzResearch.WordTrace tailWord_1650743 prefixEnd_1650743 282541532014980064706959 := by
  unfold tailWord_1650743
  simp only [CollatzResearch.WordTrace]
  refine ⟨60207543458647510304356883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40138362305765006869571255 60207543458647510304356883)
  ·
    refine ⟨90311315187971265456535325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60207543458647510304356883 90311315187971265456535325)
    ·
      refine ⟨33866743195489224546200747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90311315187971265456535325 33866743195489224546200747)
      ·
        refine ⟨50800114793233836819301121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33866743195489224546200747 50800114793233836819301121)
        ·
          refine ⟨38100086094925377614475841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50800114793233836819301121 38100086094925377614475841)
          ·
            refine ⟨28575064571194033210856881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38100086094925377614475841 28575064571194033210856881)
            ·
              refine ⟨21431298428395524908142661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28575064571194033210856881 21431298428395524908142661)
              ·
                refine ⟨4018368455324160920276749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21431298428395524908142661 4018368455324160920276749)
                ·
                  refine ⟨1506888170746560345103781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4018368455324160920276749 1506888170746560345103781)
                  ·
                    refine ⟨282541532014980064706959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1506888170746560345103781 282541532014980064706959)
                    ·
                      rfl

theorem cell23_1650743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 4, 3, 4].length) (baseStart_1650743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650743 prefixEnd_1650743 := by exact prefixLift 1650743
  have htrace : WordTrace (prefixWord ++ tailWord_1650743) baseStart_1650743 baseEnd_1650743 := by
    simpa [prefixWord, tailWord_1650743, baseEnd_1650743] using wordTrace_append hprefix tailTrace_1650743
  have hstable : (prefixWord ++ tailWord_1650743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650743).length < 2 ^ (prefixWord ++ tailWord_1650743).sum := by decide
  have hdescent : baseEnd_1650743 < baseStart_1650743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650746 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6]
def baseStart_1650746 : Nat := 118140960795 + 1650746 * 2 ^ 59
def prefixEnd_1650746 : Nat := 4983230072969 + 3 ^ 40 * 1650746 * 2
def baseEnd_1650746 : Nat := 847626136486903682383363

theorem tailTrace_1650746 : CollatzResearch.WordTrace tailWord_1650746 prefixEnd_1650746 847626136486903682383363 := by
  unfold tailWord_1650746
  simp only [CollatzResearch.WordTrace]
  refine ⟨15051913219409160454179023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40138435251757761211144061 15051913219409160454179023)
  ·
    refine ⟨22577869829113740681268535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15051913219409160454179023 22577869829113740681268535)
    ·
      refine ⟨33866804743670611021902803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22577869829113740681268535 33866804743670611021902803)
      ·
        refine ⟨50800207115505916532854205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33866804743670611021902803 50800207115505916532854205)
        ·
          refine ⟨19050077668314718699820327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50800207115505916532854205 19050077668314718699820327)
          ·
            refine ⟨28575116502472078049730491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19050077668314718699820327 28575116502472078049730491)
            ·
              refine ⟨42862674753708117074595737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28575116502472078049730491 42862674753708117074595737)
              ·
                refine ⟨32147006065281087805946803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42862674753708117074595737 32147006065281087805946803)
                ·
                  refine ⟨48220509097921631708920205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32147006065281087805946803 48220509097921631708920205)
                  ·
                    refine ⟨18082690911720611890845077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48220509097921631708920205 18082690911720611890845077)
                    ·
                      refine ⟨847626136486903682383363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18082690911720611890845077 847626136486903682383363)
                      ·
                        rfl

theorem cell23_1650746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_1650746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650746 prefixEnd_1650746 := by exact prefixLift 1650746
  have htrace : WordTrace (prefixWord ++ tailWord_1650746) baseStart_1650746 baseEnd_1650746 := by
    simpa [prefixWord, tailWord_1650746, baseEnd_1650746] using wordTrace_append hprefix tailTrace_1650746
  have hstable : (prefixWord ++ tailWord_1650746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650746).length < 2 ^ (prefixWord ++ tailWord_1650746).sum := by decide
  have hdescent : baseEnd_1650746 < baseStart_1650746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650773 : List Nat := [1, 3, 2, 2, 1, 3, 1, 4, 6]
def baseStart_1650773 : Nat := 118140960795 + 1650773 * 2 ^ 59
def prefixEnd_1650773 : Nat := 4983230072969 + 3 ^ 40 * 1650773 * 2
def baseEnd_1650773 : Nat := 94182222273841675193971

theorem tailTrace_1650773 : CollatzResearch.WordTrace tailWord_1650773 prefixEnd_1650773 94182222273841675193971 := by
  unfold tailWord_1650773
  simp only [CollatzResearch.WordTrace]
  refine ⟨60208637648538825427948973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40139091765692550285299315 60208637648538825427948973)
  ·
    refine ⟨22578239118202059535480865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60208637648538825427948973 22578239118202059535480865)
    ·
      refine ⟨16933679338651544651610649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22578239118202059535480865 16933679338651544651610649)
      ·
        refine ⟨12700259503988658488707987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16933679338651544651610649 12700259503988658488707987)
        ·
          refine ⟨19050389255982987733061981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12700259503988658488707987 19050389255982987733061981)
          ·
            refine ⟨7143895970993620399898243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19050389255982987733061981 7143895970993620399898243)
            ·
              refine ⟨10715843956490430599847365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7143895970993620399898243 10715843956490430599847365)
              ·
                refine ⟨2009220741841955737471381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10715843956490430599847365 2009220741841955737471381)
                ·
                  refine ⟨94182222273841675193971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2009220741841955737471381 94182222273841675193971)
                  ·
                    rfl

theorem cell23_1650773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 6].length) (baseStart_1650773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650773 prefixEnd_1650773 := by exact prefixLift 1650773
  have htrace : WordTrace (prefixWord ++ tailWord_1650773) baseStart_1650773 baseEnd_1650773 := by
    simpa [prefixWord, tailWord_1650773, baseEnd_1650773] using wordTrace_append hprefix tailTrace_1650773
  have hstable : (prefixWord ++ tailWord_1650773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650773).length < 2 ^ (prefixWord ++ tailWord_1650773).sum := by decide
  have hdescent : baseEnd_1650773 < baseStart_1650773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650800 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 5, 1, 3]
def baseStart_1650800 : Nat := 118140960795 + 1650800 * 2 ^ 59
def prefixEnd_1650800 : Nat := 4983230072969 + 3 ^ 40 * 1650800 * 2
def baseEnd_1650800 : Nat := 847653864442246471108115

theorem tailTrace_1650800 : CollatzResearch.WordTrace tailWord_1650800 prefixEnd_1650800 847653864442246471108115 := by
  unfold tailWord_1650800
  simp only [CollatzResearch.WordTrace]
  refine ⟨30104811209720504519590927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40139748279627339359454569 30104811209720504519590927)
  ·
    refine ⟨45157216814580756779386391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30104811209720504519590927 45157216814580756779386391)
    ·
      refine ⟨67735825221871135169079587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45157216814580756779386391 67735825221871135169079587)
      ·
        refine ⟨101603737832806702753619381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67735825221871135169079587 101603737832806702753619381)
        ·
          refine ⟨9525350421825628383151817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101603737832806702753619381 9525350421825628383151817)
          ·
            refine ⟨7144012816369221287363863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9525350421825628383151817 7144012816369221287363863)
            ·
              refine ⟨10716019224553831931045795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7144012816369221287363863 10716019224553831931045795)
              ·
                refine ⟨16074028836830747896568693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10716019224553831931045795 16074028836830747896568693)
                ·
                  refine ⟨1506940203452882615303315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16074028836830747896568693 1506940203452882615303315)
                  ·
                    refine ⟨2260410305179323922954973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1506940203452882615303315 2260410305179323922954973)
                    ·
                      refine ⟨847653864442246471108115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2260410305179323922954973 847653864442246471108115)
                      ·
                        rfl

theorem cell23_1650800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 5, 1, 3].length) (baseStart_1650800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650800 prefixEnd_1650800 := by exact prefixLift 1650800
  have htrace : WordTrace (prefixWord ++ tailWord_1650800) baseStart_1650800 baseEnd_1650800 := by
    simpa [prefixWord, tailWord_1650800, baseEnd_1650800] using wordTrace_append hprefix tailTrace_1650800
  have hstable : (prefixWord ++ tailWord_1650800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650800).length < 2 ^ (prefixWord ++ tailWord_1650800).sum := by decide
  have hdescent : baseEnd_1650800 < baseStart_1650800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650820 : List Nat := [2, 3, 2, 1, 2, 1, 3, 3, 1, 5]
def baseStart_1650820 : Nat := 118140960795 + 1650820 * 2 ^ 59
def prefixEnd_1650820 : Nat := 4983230072969 + 3 ^ 40 * 1650820 * 2
def baseEnd_1650820 : Nat := 282554711351778797619341

theorem tailTrace_1650820 : CollatzResearch.WordTrace tailWord_1650820 prefixEnd_1650820 282554711351778797619341 := by
  unfold tailWord_1650820
  simp only [CollatzResearch.WordTrace]
  refine ⟨30105175939684276227454957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40140234586245701636606609 30105175939684276227454957)
  ·
    refine ⟨11289440977381603585295609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30105175939684276227454957 11289440977381603585295609)
    ·
      refine ⟨8467080733036202688971707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11289440977381603585295609 8467080733036202688971707)
      ·
        refine ⟨12700621099554304033457561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8467080733036202688971707 12700621099554304033457561)
        ·
          refine ⟨9525465824665728025093171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12700621099554304033457561 9525465824665728025093171)
          ·
            refine ⟨14288198736998592037639757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9525465824665728025093171 14288198736998592037639757)
            ·
              refine ⟨5358074526374472014114909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14288198736998592037639757 5358074526374472014114909)
              ·
                refine ⟨2009277947390427005293091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5358074526374472014114909 2009277947390427005293091)
                ·
                  refine ⟨3013916921085640507939637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009277947390427005293091 3013916921085640507939637)
                  ·
                    refine ⟨282554711351778797619341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3013916921085640507939637 282554711351778797619341)
                    ·
                      rfl

theorem cell23_1650820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_1650820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650820 prefixEnd_1650820 := by exact prefixLift 1650820
  have htrace : WordTrace (prefixWord ++ tailWord_1650820) baseStart_1650820 baseEnd_1650820 := by
    simpa [prefixWord, tailWord_1650820, baseEnd_1650820] using wordTrace_append hprefix tailTrace_1650820
  have hstable : (prefixWord ++ tailWord_1650820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650820).length < 2 ^ (prefixWord ++ tailWord_1650820).sum := by decide
  have hdescent : baseEnd_1650820 < baseStart_1650820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650834 : List Nat := [3, 2, 3, 1, 1, 1, 1, 6, 1, 1, 3]
def baseStart_1650834 : Nat := 118140960795 + 1650834 * 2 ^ 59
def prefixEnd_1650834 : Nat := 4983230072969 + 3 ^ 40 * 1650834 * 2
def baseEnd_1650834 : Nat := 847671322784499338082959

theorem tailTrace_1650834 : CollatzResearch.WordTrace tailWord_1650834 prefixEnd_1650834 847671322784499338082959 := by
  unfold tailWord_1650834
  simp only [CollatzResearch.WordTrace]
  refine ⟨15052715625329458211479889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40140575000878555230613037 15052715625329458211479889)
  ·
    refine ⟨11289536718997093658609917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15052715625329458211479889 11289536718997093658609917)
    ·
      refine ⟨4233576269623910121978719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11289536718997093658609917 4233576269623910121978719)
      ·
        refine ⟨6350364404435865182968079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4233576269623910121978719 6350364404435865182968079)
        ·
          refine ⟨9525546606653797774452119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6350364404435865182968079 9525546606653797774452119)
          ·
            refine ⟨14288319909980696661678179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9525546606653797774452119 14288319909980696661678179)
            ·
              refine ⟨21432479864971044992517269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14288319909980696661678179 21432479864971044992517269)
              ·
                refine ⟨1004647493670517734024247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21432479864971044992517269 1004647493670517734024247)
                ·
                  refine ⟨1506971240505776601036371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1004647493670517734024247 1506971240505776601036371)
                  ·
                    refine ⟨2260456860758664901554557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1506971240505776601036371 2260456860758664901554557)
                    ·
                      refine ⟨847671322784499338082959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2260456860758664901554557 847671322784499338082959)
                      ·
                        rfl

theorem cell23_1650834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 1, 1, 3].length) (baseStart_1650834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650834 prefixEnd_1650834 := by exact prefixLift 1650834
  have htrace : WordTrace (prefixWord ++ tailWord_1650834) baseStart_1650834 baseEnd_1650834 := by
    simpa [prefixWord, tailWord_1650834, baseEnd_1650834] using wordTrace_append hprefix tailTrace_1650834
  have hstable : (prefixWord ++ tailWord_1650834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650834).length < 2 ^ (prefixWord ++ tailWord_1650834).sum := by decide
  have hdescent : baseEnd_1650834 < baseStart_1650834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650853 : List Nat := [1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 6]
def baseStart_1650853 : Nat := 118140960795 + 1650853 * 2 ^ 59
def prefixEnd_1650853 : Nat := 4983230072969 + 3 ^ 40 * 1650853 * 2
def baseEnd_1650853 : Nat := 847681078916934763745371

theorem tailTrace_1650853 : CollatzResearch.WordTrace tailWord_1650853 prefixEnd_1650853 847681078916934763745371 := by
  unfold tailWord_1650853
  simp only [CollatzResearch.WordTrace]
  refine ⟨60211555488248999090861213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40141036992165999393907475 60211555488248999090861213)
  ·
    refine ⟨22579333308093374659072955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60211555488248999090861213 22579333308093374659072955)
    ·
      refine ⟨33868999962140061988609433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22579333308093374659072955 33868999962140061988609433)
      ·
        refine ⟨25401749971605046491457075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33868999962140061988609433 25401749971605046491457075)
        ·
          refine ⟨38102624957407569737185613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25401749971605046491457075 38102624957407569737185613)
          ·
            refine ⟨14288484359027838651444605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38102624957407569737185613 14288484359027838651444605)
            ·
              refine ⟨5358181634635439494291727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14288484359027838651444605 5358181634635439494291727)
              ·
                refine ⟨8037272451953159241437591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5358181634635439494291727 8037272451953159241437591)
                ·
                  refine ⟨12055908677929738862156387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8037272451953159241437591 12055908677929738862156387)
                  ·
                    refine ⟨18083863016894608293234581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12055908677929738862156387 18083863016894608293234581)
                    ·
                      refine ⟨847681078916934763745371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18083863016894608293234581 847681078916934763745371)
                      ·
                        rfl

theorem cell23_1650853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_1650853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650853 prefixEnd_1650853 := by exact prefixLift 1650853
  have htrace : WordTrace (prefixWord ++ tailWord_1650853) baseStart_1650853 baseEnd_1650853 := by
    simpa [prefixWord, tailWord_1650853, baseEnd_1650853] using wordTrace_append hprefix tailTrace_1650853
  have hstable : (prefixWord ++ tailWord_1650853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650853).length < 2 ^ (prefixWord ++ tailWord_1650853).sum := by decide
  have hdescent : baseEnd_1650853 < baseStart_1650853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650891 : List Nat := [1, 1, 1, 1, 3, 2, 7, 2, 1, 2, 2]
def baseStart_1650891 : Nat := 118140960795 + 1650891 * 2 ^ 59
def prefixEnd_1650891 : Nat := 4983230072969 + 3 ^ 40 * 1650891 * 2
def baseEnd_1650891 : Nat := 847700591181805615070197

theorem tailTrace_1650891 : CollatzResearch.WordTrace tailWord_1650891 prefixEnd_1650891 847700591181805615070197 := by
  unfold tailWord_1650891
  simp only [CollatzResearch.WordTrace]
  refine ⟨60212941462111331580744527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40141960974740887720496351 60212941462111331580744527)
  ·
    refine ⟨90319412193166997371116791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60212941462111331580744527 90319412193166997371116791)
    ·
      refine ⟨135479118289750496056675187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90319412193166997371116791 135479118289750496056675187)
      ·
        refine ⟨203218677434625744085012781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135479118289750496056675187 203218677434625744085012781)
        ·
          refine ⟨76207004037984654031879793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203218677434625744085012781 76207004037984654031879793)
          ·
            refine ⟨57155253028488490523909845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76207004037984654031879793 57155253028488490523909845)
            ·
              refine ⟨1339576242855198996654137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 57155253028488490523909845 1339576242855198996654137)
              ·
                refine ⟨1004682182141399247490603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1339576242855198996654137 1004682182141399247490603)
                ·
                  refine ⟨1507023273212098871235905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1004682182141399247490603 1507023273212098871235905)
                  ·
                    refine ⟨1130267454909074153426929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1507023273212098871235905 1130267454909074153426929)
                    ·
                      refine ⟨847700591181805615070197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1130267454909074153426929 847700591181805615070197)
                      ·
                        rfl

theorem cell23_1650891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 7, 2, 1, 2, 2].length) (baseStart_1650891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650891 prefixEnd_1650891 := by exact prefixLift 1650891
  have htrace : WordTrace (prefixWord ++ tailWord_1650891) baseStart_1650891 baseEnd_1650891 := by
    simpa [prefixWord, tailWord_1650891, baseEnd_1650891] using wordTrace_append hprefix tailTrace_1650891
  have hstable : (prefixWord ++ tailWord_1650891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650891).length < 2 ^ (prefixWord ++ tailWord_1650891).sum := by decide
  have hdescent : baseEnd_1650891 < baseStart_1650891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650901 : List Nat := [1, 3, 2, 4, 2, 2, 2, 1, 2, 4]
def baseStart_1650901 : Nat := 118140960795 + 1650901 * 2 ^ 59
def prefixEnd_1650901 : Nat := 4983230072969 + 3 ^ 40 * 1650901 * 2
def baseEnd_1650901 : Nat := 282568575329450191981717

theorem tailTrace_1650901 : CollatzResearch.WordTrace tailWord_1650901 prefixEnd_1650901 282568575329450191981717 := by
  unfold tailWord_1650901
  simp only [CollatzResearch.WordTrace]
  refine ⟨60213306192075103288608557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40142204128050068859072371 60213306192075103288608557)
  ·
    refine ⟨22579989822028163733228209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60213306192075103288608557 22579989822028163733228209)
    ·
      refine ⟨16934992366521122799921157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22579989822028163733228209 16934992366521122799921157)
      ·
        refine ⟨3175311068722710524985217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16934992366521122799921157 3175311068722710524985217)
        ·
          refine ⟨2381483301542032893738913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3175311068722710524985217 2381483301542032893738913)
          ·
            refine ⟨1786112476156524670304185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2381483301542032893738913 1786112476156524670304185)
            ·
              refine ⟨1339584357117393502728139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1786112476156524670304185 1339584357117393502728139)
              ·
                refine ⟨2009376535676090254092209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339584357117393502728139 2009376535676090254092209)
                ·
                  refine ⟨1507032401757067690569157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2009376535676090254092209 1507032401757067690569157)
                  ·
                    refine ⟨282568575329450191981717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1507032401757067690569157 282568575329450191981717)
                    ·
                      rfl

theorem cell23_1650901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_1650901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650901 prefixEnd_1650901 := by exact prefixLift 1650901
  have htrace : WordTrace (prefixWord ++ tailWord_1650901) baseStart_1650901 baseEnd_1650901 := by
    simpa [prefixWord, tailWord_1650901, baseEnd_1650901] using wordTrace_append hprefix tailTrace_1650901
  have hstable : (prefixWord ++ tailWord_1650901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650901).length < 2 ^ (prefixWord ++ tailWord_1650901).sum := by decide
  have hdescent : baseEnd_1650901 < baseStart_1650901 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650908 : List Nat := [2, 2, 5, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_1650908 : Nat := 118140960795 + 1650908 * 2 ^ 59
def prefixEnd_1650908 : Nat := 4983230072969 + 3 ^ 40 * 1650908 * 2
def baseEnd_1650908 : Nat := 847709320352932048557619

theorem tailTrace_1650908 : CollatzResearch.WordTrace tailWord_1650908 prefixEnd_1650908 847709320352932048557619 := by
  unfold tailWord_1650908
  simp only [CollatzResearch.WordTrace]
  refine ⟨30106780751524871742056689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40142374335366495656075585 30106780751524871742056689)
  ·
    refine ⟨22580085563643653806542517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30106780751524871742056689 22580085563643653806542517)
    ·
      refine ⟨2116883021591592544363361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22580085563643653806542517 2116883021591592544363361)
      ·
        refine ⟨1587662266193694408272521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2116883021591592544363361 1587662266193694408272521)
        ·
          refine ⟨1190746699645270806204391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1587662266193694408272521 1190746699645270806204391)
          ·
            refine ⟨1786120049467906209306587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1190746699645270806204391 1786120049467906209306587)
            ·
              refine ⟨2679180074201859313959881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1786120049467906209306587 2679180074201859313959881)
              ·
                refine ⟨2009385055651394485469911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2679180074201859313959881 2009385055651394485469911)
                ·
                  refine ⟨3014077583477091728204867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009385055651394485469911 3014077583477091728204867)
                  ·
                    refine ⟨4521116375215637592307301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3014077583477091728204867 4521116375215637592307301)
                    ·
                      refine ⟨847709320352932048557619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4521116375215637592307301 847709320352932048557619)
                      ·
                        rfl

theorem cell23_1650908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_1650908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650908 prefixEnd_1650908 := by exact prefixLift 1650908
  have htrace : WordTrace (prefixWord ++ tailWord_1650908) baseStart_1650908 baseEnd_1650908 := by
    simpa [prefixWord, tailWord_1650908, baseEnd_1650908] using wordTrace_append hprefix tailTrace_1650908
  have hstable : (prefixWord ++ tailWord_1650908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650908).length < 2 ^ (prefixWord ++ tailWord_1650908).sum := by decide
  have hdescent : baseEnd_1650908 < baseStart_1650908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1650934 : List Nat := [5, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2]
def baseStart_1650934 : Nat := 118140960795 + 1650934 * 2 ^ 59
def prefixEnd_1650934 : Nat := 4983230072969 + 3 ^ 40 * 1650934 * 2
def baseEnd_1650934 : Nat := 847722670849948946832499

theorem tailTrace_1650934 : CollatzResearch.WordTrace tailWord_1650934 prefixEnd_1650934 847722670849948946832499 := by
  unfold tailWord_1650934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3763406862559721870284991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40143006533970366616373237 3763406862559721870284991)
  ·
    refine ⟨5645110293839582805427487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3763406862559721870284991 5645110293839582805427487)
    ·
      refine ⟨8467665440759374208141231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5645110293839582805427487 8467665440759374208141231)
      ·
        refine ⟨12701498161139061312211847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8467665440759374208141231 12701498161139061312211847)
        ·
          refine ⟨19052247241708591968317771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12701498161139061312211847 19052247241708591968317771)
          ·
            refine ⟨28578370862562887952476657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19052247241708591968317771 28578370862562887952476657)
            ·
              refine ⟨21433778146922165964357493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28578370862562887952476657 21433778146922165964357493)
              ·
                refine ⟨2009416701273953059158515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21433778146922165964357493 2009416701273953059158515)
                ·
                  refine ⟨3014125051910929588737773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009416701273953059158515 3014125051910929588737773)
                  ·
                    refine ⟨1130296894466598595776665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3014125051910929588737773 1130296894466598595776665)
                    ·
                      refine ⟨847722670849948946832499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1130296894466598595776665 847722670849948946832499)
                      ·
                        rfl

theorem cell23_1650934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_1650934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1650934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1650934 prefixEnd_1650934 := by exact prefixLift 1650934
  have htrace : WordTrace (prefixWord ++ tailWord_1650934) baseStart_1650934 baseEnd_1650934 := by
    simpa [prefixWord, tailWord_1650934, baseEnd_1650934] using wordTrace_append hprefix tailTrace_1650934
  have hstable : (prefixWord ++ tailWord_1650934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1650934).length < 2 ^ (prefixWord ++ tailWord_1650934).sum := by decide
  have hdescent : baseEnd_1650934 < baseStart_1650934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1650934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651000 : List Nat := [2, 1, 2, 1, 3, 1, 2, 4, 2, 5]
def baseStart_1651000 : Nat := 118140960795 + 1651000 * 2 ^ 59
def prefixEnd_1651000 : Nat := 4983230072969 + 3 ^ 40 * 1651000 * 2
def baseEnd_1651000 : Nat := 282585520191048562869065

theorem tailTrace_1651000 : CollatzResearch.WordTrace tailWord_1651000 prefixEnd_1651000 282585520191048562869065 := by
  unfold tailWord_1651000
  simp only [CollatzResearch.WordTrace]
  refine ⟨30108458509358221598231227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40144611345810962130974969 30108458509358221598231227)
  ·
    refine ⟨45162687764037332397346841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30108458509358221598231227 45162687764037332397346841)
    ·
      refine ⟨33872015823027999298010131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45162687764037332397346841 33872015823027999298010131)
      ·
        refine ⟨50808023734541998947015197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33872015823027999298010131 50808023734541998947015197)
        ·
          refine ⟨19053008900453249605130699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50808023734541998947015197 19053008900453249605130699)
          ·
            refine ⟨28579513350679874407696049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19053008900453249605130699 28579513350679874407696049)
            ·
              refine ⟨21434635013009905805772037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28579513350679874407696049 21434635013009905805772037)
              ·
                refine ⟨4018994064939357338582257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21434635013009905805772037 4018994064939357338582257)
                ·
                  refine ⟨3014245548704518003936693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4018994064939357338582257 3014245548704518003936693)
                  ·
                    refine ⟨282585520191048562869065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3014245548704518003936693 282585520191048562869065)
                    ·
                      rfl

theorem cell23_1651000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 2, 5].length) (baseStart_1651000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651000 prefixEnd_1651000 := by exact prefixLift 1651000
  have htrace : WordTrace (prefixWord ++ tailWord_1651000) baseStart_1651000 baseEnd_1651000 := by
    simpa [prefixWord, tailWord_1651000, baseEnd_1651000] using wordTrace_append hprefix tailTrace_1651000
  have hstable : (prefixWord ++ tailWord_1651000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651000).length < 2 ^ (prefixWord ++ tailWord_1651000).sum := by decide
  have hdescent : baseEnd_1651000 < baseStart_1651000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651020 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 3, 3, 4]
def baseStart_1651020 : Nat := 118140960795 + 1651020 * 2 ^ 59
def prefixEnd_1651020 : Nat := 4983230072969 + 3 ^ 40 * 1651020 * 2
def baseEnd_1651020 : Nat := 847766830186235610357103

theorem tailTrace_1651020 : CollatzResearch.WordTrace tailWord_1651020 prefixEnd_1651020 847766830186235610357103 := by
  unfold tailWord_1651020
  simp only [CollatzResearch.WordTrace]
  refine ⟨30108823239321993306095257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40145097652429324408127009 30108823239321993306095257)
  ·
    refine ⟨22581617429491494979571443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30108823239321993306095257 22581617429491494979571443)
    ·
      refine ⟨33872426144237242469357165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22581617429491494979571443 33872426144237242469357165)
      ·
        refine ⟨12702159804088965926008937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33872426144237242469357165 12702159804088965926008937)
        ·
          refine ⟨9526619853066724444506703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12702159804088965926008937 9526619853066724444506703)
          ·
            refine ⟨14289929779600086666760055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9526619853066724444506703 14289929779600086666760055)
            ·
              refine ⟨21434894669400130000140083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14289929779600086666760055 21434894669400130000140083)
              ·
                refine ⟨32152342004100195000210125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21434894669400130000140083 32152342004100195000210125)
                ·
                  refine ⟨12057128251537573125078797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32152342004100195000210125 12057128251537573125078797)
                  ·
                    refine ⟨4521423094326589921904549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12057128251537573125078797 4521423094326589921904549)
                    ·
                      refine ⟨847766830186235610357103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4521423094326589921904549 847766830186235610357103)
                      ·
                        rfl

theorem cell23_1651020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_1651020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651020 prefixEnd_1651020 := by exact prefixLift 1651020
  have htrace : WordTrace (prefixWord ++ tailWord_1651020) baseStart_1651020 baseEnd_1651020 := by
    simpa [prefixWord, tailWord_1651020, baseEnd_1651020] using wordTrace_append hprefix tailTrace_1651020
  have hstable : (prefixWord ++ tailWord_1651020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651020).length < 2 ^ (prefixWord ++ tailWord_1651020).sum := by decide
  have hdescent : baseEnd_1651020 < baseStart_1651020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651127 : List Nat := [1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 4]
def baseStart_1651127 : Nat := 118140960795 + 1651127 * 2 ^ 59
def prefixEnd_1651127 : Nat := 4983230072969 + 3 ^ 40 * 1651127 * 2
def baseEnd_1651127 : Nat := 847821772616266691719111

theorem tailTrace_1651127 : CollatzResearch.WordTrace tailWord_1651127 prefixEnd_1651127 847821772616266691719111 := by
  unfold tailWord_1651127
  simp only [CollatzResearch.WordTrace]
  refine ⟨60221549089256343886335635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40147699392837562590890423 60221549089256343886335635)
  ·
    refine ⟨90332323633884515829503453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60221549089256343886335635 90332323633884515829503453)
    ·
      refine ⟨33874621362706693436063795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90332323633884515829503453 33874621362706693436063795)
      ·
        refine ⟨50811932044060040154095693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33874621362706693436063795 50811932044060040154095693)
        ·
          refine ⟨19054474516522515057785885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50811932044060040154095693 19054474516522515057785885)
          ·
            refine ⟨7145427943695943146669707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19054474516522515057785885 7145427943695943146669707)
            ·
              refine ⟨10718141915543914720004561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7145427943695943146669707 10718141915543914720004561)
              ·
                refine ⟨8038606436657936040003421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10718141915543914720004561 8038606436657936040003421)
                ·
                  refine ⟨3014477413746726015001283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8038606436657936040003421 3014477413746726015001283)
                  ·
                    refine ⟨4521716120620089022501925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3014477413746726015001283 4521716120620089022501925)
                    ·
                      refine ⟨847821772616266691719111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4521716120620089022501925 847821772616266691719111)
                      ·
                        rfl

theorem cell23_1651127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 4].length) (baseStart_1651127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651127 prefixEnd_1651127 := by exact prefixLift 1651127
  have htrace : WordTrace (prefixWord ++ tailWord_1651127) baseStart_1651127 baseEnd_1651127 := by
    simpa [prefixWord, tailWord_1651127, baseEnd_1651127] using wordTrace_append hprefix tailTrace_1651127
  have hstable : (prefixWord ++ tailWord_1651127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651127).length < 2 ^ (prefixWord ++ tailWord_1651127).sum := by decide
  have hdescent : baseEnd_1651127 < baseStart_1651127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651148 : List Nat := [2, 2, 1, 4, 3, 2, 1, 1, 2, 3, 2]
def baseStart_1651148 : Nat := 118140960795 + 1651148 * 2 ^ 59
def prefixEnd_1651148 : Nat := 4983230072969 + 3 ^ 40 * 1651148 * 2
def baseEnd_1651148 : Nat := 847832555710011109556515

theorem tailTrace_1651148 : CollatzResearch.WordTrace tailWord_1651148 prefixEnd_1651148 847832555710011109556515 := by
  unfold tailWord_1651148
  simp only [CollatzResearch.WordTrace]
  refine ⟨30111157511090132236425049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40148210014786842981900065 30111157511090132236425049)
  ·
    refine ⟨22583368133317599177318787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30111157511090132236425049 22583368133317599177318787)
    ·
      refine ⟨33875052199976398765978181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22583368133317599177318787 33875052199976398765978181)
      ·
        refine ⟨6351572287495574768620909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33875052199976398765978181 6351572287495574768620909)
        ·
          refine ⟨2381839607810840538232841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6351572287495574768620909 2381839607810840538232841)
          ·
            refine ⟨1786379705858130403674631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2381839607810840538232841 1786379705858130403674631)
            ·
              refine ⟨2679569558787195605511947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1786379705858130403674631 2679569558787195605511947)
              ·
                refine ⟨4019354338180793408267921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2679569558787195605511947 4019354338180793408267921)
                ·
                  refine ⟨3014515753635595056200941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4019354338180793408267921 3014515753635595056200941)
                  ·
                    refine ⟨1130443407613348146075353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3014515753635595056200941 1130443407613348146075353)
                    ·
                      refine ⟨847832555710011109556515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1130443407613348146075353 847832555710011109556515)
                      ·
                        rfl

theorem cell23_1651148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_1651148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651148 prefixEnd_1651148 := by exact prefixLift 1651148
  have htrace : WordTrace (prefixWord ++ tailWord_1651148) baseStart_1651148 baseEnd_1651148 := by
    simpa [prefixWord, tailWord_1651148, baseEnd_1651148] using wordTrace_append hprefix tailTrace_1651148
  have hstable : (prefixWord ++ tailWord_1651148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651148).length < 2 ^ (prefixWord ++ tailWord_1651148).sum := by decide
  have hdescent : baseEnd_1651148 < baseStart_1651148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651178 : List Nat := [3, 1, 3, 1, 3, 2, 2, 1, 3, 2, 2]
def baseStart_1651178 : Nat := 118140960795 + 1651178 * 2 ^ 59
def prefixEnd_1651178 : Nat := 4983230072969 + 3 ^ 40 * 1651178 * 2
def baseEnd_1651178 : Nat := 847847960129645992181377

theorem tailTrace_1651178 : CollatzResearch.WordTrace tailWord_1651178 prefixEnd_1651178 847847960129645992181377 := by
  unfold tailWord_1651178
  simp only [CollatzResearch.WordTrace]
  refine ⟨15055852303017894899110547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40148939474714386397628125 15055852303017894899110547)
  ·
    refine ⟨22583778454526842348665821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15055852303017894899110547 22583778454526842348665821)
    ·
      refine ⟨8468916920447565880749683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22583778454526842348665821 8468916920447565880749683)
      ·
        refine ⟨12703375380671348821124525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8468916920447565880749683 12703375380671348821124525)
        ·
          refine ⟨4763765767751755807921697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12703375380671348821124525 4763765767751755807921697)
          ·
            refine ⟨3572824325813816855941273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4763765767751755807921697 3572824325813816855941273)
            ·
              refine ⟨2679618244360362641955955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3572824325813816855941273 2679618244360362641955955)
              ·
                refine ⟨4019427366540543962933933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2679618244360362641955955 4019427366540543962933933)
                ·
                  refine ⟨1507285262452703986100225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4019427366540543962933933 1507285262452703986100225)
                  ·
                    refine ⟨1130463946839527989575169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1507285262452703986100225 1130463946839527989575169)
                    ·
                      refine ⟨847847960129645992181377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1130463946839527989575169 847847960129645992181377)
                      ·
                        rfl

theorem cell23_1651178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_1651178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651178 prefixEnd_1651178 := by exact prefixLift 1651178
  have htrace : WordTrace (prefixWord ++ tailWord_1651178) baseStart_1651178 baseEnd_1651178 := by
    simpa [prefixWord, tailWord_1651178, baseEnd_1651178] using wordTrace_append hprefix tailTrace_1651178
  have hstable : (prefixWord ++ tailWord_1651178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651178).length < 2 ^ (prefixWord ++ tailWord_1651178).sum := by decide
  have hdescent : baseEnd_1651178 < baseStart_1651178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651221 : List Nat := [1, 3, 2, 1, 3, 1, 1, 5, 1, 3, 2]
def baseStart_1651221 : Nat := 118140960795 + 1651221 * 2 ^ 59
def prefixEnd_1651221 : Nat := 4983230072969 + 3 ^ 40 * 1651221 * 2
def baseEnd_1651221 : Nat := 847870039797789323943679

theorem tailTrace_1651221 : CollatzResearch.WordTrace tailWord_1651221 prefixEnd_1651221 847870039797789323943679 := by
  unfold tailWord_1651221
  simp only [CollatzResearch.WordTrace]
  refine ⟨60224977550915797940257517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40149985033943865293505011 60224977550915797940257517)
  ·
    refine ⟨22584366581593424227596569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60224977550915797940257517 22584366581593424227596569)
    ·
      refine ⟨16938274936195068170697427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22584366581593424227596569 16938274936195068170697427)
      ·
        refine ⟨25407412404292602256046141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16938274936195068170697427 25407412404292602256046141)
        ·
          refine ⟨9527779651609725846017303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25407412404292602256046141 9527779651609725846017303)
          ·
            refine ⟨14291669477414588769025955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9527779651609725846017303 14291669477414588769025955)
            ·
              refine ⟨21437504216121883153538933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14291669477414588769025955 21437504216121883153538933)
              ·
                refine ⟨2009766020261426545644275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21437504216121883153538933 2009766020261426545644275)
                ·
                  refine ⟨3014649030392139818466413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009766020261426545644275 3014649030392139818466413)
                  ·
                    refine ⟨1130493386397052431924905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3014649030392139818466413 1130493386397052431924905)
                    ·
                      refine ⟨847870039797789323943679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1130493386397052431924905 847870039797789323943679)
                      ·
                        rfl

theorem cell23_1651221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_1651221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651221 prefixEnd_1651221 := by exact prefixLift 1651221
  have htrace : WordTrace (prefixWord ++ tailWord_1651221) baseStart_1651221 baseEnd_1651221 := by
    simpa [prefixWord, tailWord_1651221, baseEnd_1651221] using wordTrace_append hprefix tailTrace_1651221
  have hstable : (prefixWord ++ tailWord_1651221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651221).length < 2 ^ (prefixWord ++ tailWord_1651221).sum := by decide
  have hdescent : baseEnd_1651221 < baseStart_1651221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651257 : List Nat := [1, 2, 1, 5, 1, 1, 2, 1, 9]
def baseStart_1651257 : Nat := 118140960795 + 1651257 * 2 ^ 59
def prefixEnd_1651257 : Nat := 4983230072969 + 3 ^ 40 * 1651257 * 2
def baseEnd_1651257 : Nat := 94209836122372353677057

theorem tailTrace_1651257 : CollatzResearch.WordTrace tailWord_1651257 prefixEnd_1651257 94209836122372353677057 := by
  unfold tailWord_1651257
  simp only [CollatzResearch.WordTrace]
  refine ⟨60226290578785376088568025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40150860385856917392378683 60226290578785376088568025)
  ·
    refine ⟨45169717934089032066426019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60226290578785376088568025 45169717934089032066426019)
    ·
      refine ⟨67754576901133548099639029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45169717934089032066426019 67754576901133548099639029)
      ·
        refine ⟨6351991584481270134341159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67754576901133548099639029 6351991584481270134341159)
        ·
          refine ⟨9527987376721905201511739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6351991584481270134341159 9527987376721905201511739)
          ·
            refine ⟨14291981065082857802267609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9527987376721905201511739 14291981065082857802267609)
            ·
              refine ⟨10718985798812143351700707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14291981065082857802267609 10718985798812143351700707)
              ·
                refine ⟨16078478698218215027551061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10718985798812143351700707 16078478698218215027551061)
                ·
                  refine ⟨94209836122372353677057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16078478698218215027551061 94209836122372353677057)
                  ·
                    rfl

theorem cell23_1651257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 9].length) (baseStart_1651257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651257 prefixEnd_1651257 := by exact prefixLift 1651257
  have htrace : WordTrace (prefixWord ++ tailWord_1651257) baseStart_1651257 baseEnd_1651257 := by
    simpa [prefixWord, tailWord_1651257, baseEnd_1651257] using wordTrace_append hprefix tailTrace_1651257
  have hstable : (prefixWord ++ tailWord_1651257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651257).length < 2 ^ (prefixWord ++ tailWord_1651257).sum := by decide
  have hdescent : baseEnd_1651257 < baseStart_1651257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651298 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_1651298 : Nat := 118140960795 + 1651298 * 2 ^ 59
def prefixEnd_1651298 : Nat := 4983230072969 + 3 ^ 40 * 1651298 * 2
def baseEnd_1651298 : Nat := 847909577808185522680825

theorem tailTrace_1651298 : CollatzResearch.WordTrace tailWord_1651298 prefixEnd_1651298 847909577808185522680825 := by
  unfold tailWord_1651298
  simp only [CollatzResearch.WordTrace]
  refine ⟨15056946492909210022702637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40151857314424560060540365 15056946492909210022702637)
  ·
    refine ⟨5646354934840953758513489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15056946492909210022702637 5646354934840953758513489)
    ·
      refine ⟨4234766201130715318885117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5646354934840953758513489 4234766201130715318885117)
      ·
        refine ⟨1588037325424018244581919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4234766201130715318885117 1588037325424018244581919)
        ·
          refine ⟨2382055988136027366872879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1588037325424018244581919 2382055988136027366872879)
          ·
            refine ⟨3573083982204041050309319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382055988136027366872879 3573083982204041050309319)
            ·
              refine ⟨5359625973306061575463979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573083982204041050309319 5359625973306061575463979)
              ·
                refine ⟨8039438959959092363195969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5359625973306061575463979 8039438959959092363195969)
                ·
                  refine ⟨6029579219969319272396977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8039438959959092363195969 6029579219969319272396977)
                  ·
                    refine ⟨4522184414976989454297733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6029579219969319272396977 4522184414976989454297733)
                    ·
                      refine ⟨847909577808185522680825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4522184414976989454297733 847909577808185522680825)
                      ·
                        rfl

theorem cell23_1651298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_1651298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651298 prefixEnd_1651298 := by exact prefixLift 1651298
  have htrace : WordTrace (prefixWord ++ tailWord_1651298) baseStart_1651298 baseEnd_1651298 := by
    simpa [prefixWord, tailWord_1651298, baseEnd_1651298] using wordTrace_append hprefix tailTrace_1651298
  have hstable : (prefixWord ++ tailWord_1651298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651298).length < 2 ^ (prefixWord ++ tailWord_1651298).sum := by decide
  have hdescent : baseEnd_1651298 < baseStart_1651298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651301 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 2, 3, 3]
def baseStart_1651301 : Nat := 118140960795 + 1651301 * 2 ^ 59
def prefixEnd_1651301 : Nat := 4983230072969 + 3 ^ 40 * 1651301 * 2
def baseEnd_1651301 : Nat := 847911118250149010943311

theorem tailTrace_1651301 : CollatzResearch.WordTrace tailWord_1651301 prefixEnd_1651301 847911118250149010943311 := by
  unfold tailWord_1651301
  simp only [CollatzResearch.WordTrace]
  refine ⟨60227895390625971603169757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40151930260417314402113171 60227895390625971603169757)
  ·
    refine ⟨22585460771484739351188659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60227895390625971603169757 22585460771484739351188659)
    ·
      refine ⟨33878191157227109026782989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22585460771484739351188659 33878191157227109026782989)
      ·
        refine ⟨12704321683960165885043621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33878191157227109026782989 12704321683960165885043621)
        ·
          refine ⟨2382060315742531103445679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12704321683960165885043621 2382060315742531103445679)
          ·
            refine ⟨3573090473613796655168519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382060315742531103445679 3573090473613796655168519)
            ·
              refine ⟨5359635710420694982752779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573090473613796655168519 5359635710420694982752779)
              ·
                refine ⟨8039453565631042474129169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5359635710420694982752779 8039453565631042474129169)
                ·
                  refine ⟨6029590174223281855596877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8039453565631042474129169 6029590174223281855596877)
                  ·
                    refine ⟨2261096315333730695848829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6029590174223281855596877 2261096315333730695848829)
                    ·
                      refine ⟨847911118250149010943311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2261096315333730695848829 847911118250149010943311)
                      ·
                        rfl

theorem cell23_1651301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_1651301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651301 prefixEnd_1651301 := by exact prefixLift 1651301
  have htrace : WordTrace (prefixWord ++ tailWord_1651301) baseStart_1651301 baseEnd_1651301 := by
    simpa [prefixWord, tailWord_1651301, baseEnd_1651301] using wordTrace_append hprefix tailTrace_1651301
  have hstable : (prefixWord ++ tailWord_1651301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651301).length < 2 ^ (prefixWord ++ tailWord_1651301).sum := by decide
  have hdescent : baseEnd_1651301 < baseStart_1651301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651321 : List Nat := [1, 2, 1, 3, 3, 4, 1, 1, 2, 5]
def baseStart_1651321 : Nat := 118140960795 + 1651321 * 2 ^ 59
def prefixEnd_1651321 : Nat := 4983230072969 + 3 ^ 40 * 1651321 * 2
def baseEnd_1651321 : Nat := 282640462621079644231073

theorem tailTrace_1651321 : CollatzResearch.WordTrace tailWord_1651321 prefixEnd_1651321 282640462621079644231073 := by
  unfold tailWord_1651321
  simp only [CollatzResearch.WordTrace]
  refine ⟨60228624850553515018897817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40152416567035676679265211 60228624850553515018897817)
  ·
    refine ⟨45171468637915136264173363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60228624850553515018897817 45171468637915136264173363)
    ·
      refine ⟨67757202956872704396260045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45171468637915136264173363 67757202956872704396260045)
      ·
        refine ⟨25408951108827264148597517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67757202956872704396260045 25408951108827264148597517)
        ·
          refine ⟨9528356665810224055724069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25408951108827264148597517 9528356665810224055724069)
          ·
            refine ⟨1786566874839417010448263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9528356665810224055724069 1786566874839417010448263)
            ·
              refine ⟨2679850312259125515672395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1786566874839417010448263 2679850312259125515672395)
              ·
                refine ⟨4019775468388688273508593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2679850312259125515672395 4019775468388688273508593)
                ·
                  refine ⟨3014831601291516205131445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4019775468388688273508593 3014831601291516205131445)
                  ·
                    refine ⟨282640462621079644231073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3014831601291516205131445 282640462621079644231073)
                    ·
                      rfl

theorem cell23_1651321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 5].length) (baseStart_1651321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651321 prefixEnd_1651321 := by exact prefixLift 1651321
  have htrace : WordTrace (prefixWord ++ tailWord_1651321) baseStart_1651321 baseEnd_1651321 := by
    simpa [prefixWord, tailWord_1651321, baseEnd_1651321] using wordTrace_append hprefix tailTrace_1651321
  have hstable : (prefixWord ++ tailWord_1651321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651321).length < 2 ^ (prefixWord ++ tailWord_1651321).sum := by decide
  have hdescent : baseEnd_1651321 < baseStart_1651321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651327 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 5]
def baseStart_1651327 : Nat := 118140960795 + 1651327 * 2 ^ 59
def prefixEnd_1651327 : Nat := 4983230072969 + 3 ^ 40 * 1651327 * 2
def baseEnd_1651327 : Nat := 847924468747165909218191

theorem tailTrace_1651327 : CollatzResearch.WordTrace tailWord_1651327 prefixEnd_1651327 847924468747165909218191 := by
  unfold tailWord_1651327
  simp only [CollatzResearch.WordTrace]
  refine ⟨60228843688531778043616235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40152562459021185362410823 60228843688531778043616235)
  ·
    refine ⟨90343265532797667065424353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60228843688531778043616235 90343265532797667065424353)
    ·
      refine ⟨67757449149598250299068265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90343265532797667065424353 67757449149598250299068265)
      ·
        refine ⟨50818086862198687724301199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67757449149598250299068265 50818086862198687724301199)
        ·
          refine ⟨76227130293298031586451799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50818086862198687724301199 76227130293298031586451799)
          ·
            refine ⟨114340695439947047379677699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76227130293298031586451799 114340695439947047379677699)
            ·
              refine ⟨171511043159920571069516549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114340695439947047379677699 171511043159920571069516549)
              ·
                refine ⟨32158320592485107075534353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171511043159920571069516549 32158320592485107075534353)
                ·
                  refine ⟨24118740444363830306650765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32158320592485107075534353 24118740444363830306650765)
                  ·
                    refine ⟨9044527666636436364994037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24118740444363830306650765 9044527666636436364994037)
                    ·
                      refine ⟨847924468747165909218191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9044527666636436364994037 847924468747165909218191)
                      ·
                        rfl

theorem cell23_1651327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_1651327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651327 prefixEnd_1651327 := by exact prefixLift 1651327
  have htrace : WordTrace (prefixWord ++ tailWord_1651327) baseStart_1651327 baseEnd_1651327 := by
    simpa [prefixWord, tailWord_1651327, baseEnd_1651327] using wordTrace_append hprefix tailTrace_1651327
  have hstable : (prefixWord ++ tailWord_1651327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651327).length < 2 ^ (prefixWord ++ tailWord_1651327).sum := by decide
  have hdescent : baseEnd_1651327 < baseStart_1651327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651347 : List Nat := [1, 1, 1, 2, 1, 2, 2, 5, 8]
def baseStart_1651347 : Nat := 118140960795 + 1651347 * 2 ^ 59
def prefixEnd_1651347 : Nat := 4983230072969 + 3 ^ 40 * 1651347 * 2
def baseEnd_1651347 : Nat := 94214970928917314552011

theorem tailTrace_1651347 : CollatzResearch.WordTrace tailWord_1651347 prefixEnd_1651347 94214970928917314552011 := by
  unfold tailWord_1651347
  simp only [CollatzResearch.WordTrace]
  refine ⟨60229573148459321459344295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40153048765639547639562863 60229573148459321459344295)
  ·
    refine ⟨90344359722688982189016443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60229573148459321459344295 90344359722688982189016443)
    ·
      refine ⟨135516539584033473283524665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90344359722688982189016443 135516539584033473283524665)
      ·
        refine ⟨101637404688025104962643499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135516539584033473283524665 101637404688025104962643499)
        ·
          refine ⟨152456107032037657443965249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101637404688025104962643499 152456107032037657443965249)
          ·
            refine ⟨114342080274028243082973937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152456107032037657443965249 114342080274028243082973937)
            ·
              refine ⟨85756560205521182312230453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114342080274028243082973937 85756560205521182312230453)
              ·
                refine ⟨8039677519267610841771605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 85756560205521182312230453 8039677519267610841771605)
                ·
                  refine ⟨94214970928917314552011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8039677519267610841771605 94214970928917314552011)
                  ·
                    rfl

theorem cell23_1651347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 8].length) (baseStart_1651347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651347 prefixEnd_1651347 := by exact prefixLift 1651347
  have htrace : WordTrace (prefixWord ++ tailWord_1651347) baseStart_1651347 baseEnd_1651347 := by
    simpa [prefixWord, tailWord_1651347, baseEnd_1651347] using wordTrace_append hprefix tailTrace_1651347
  have hstable : (prefixWord ++ tailWord_1651347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651347).length < 2 ^ (prefixWord ++ tailWord_1651347).sum := by decide
  have hdescent : baseEnd_1651347 < baseStart_1651347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651351 : List Nat := [1, 1, 3, 3, 2, 1, 4, 1, 3, 4]
def baseStart_1651351 : Nat := 118140960795 + 1651351 * 2 ^ 59
def prefixEnd_1651351 : Nat := 4983230072969 + 3 ^ 40 * 1651351 * 2
def baseEnd_1651351 : Nat := 282645597427624605106027

theorem tailTrace_1651351 : CollatzResearch.WordTrace tailWord_1651351 prefixEnd_1651351 282645597427624605106027 := by
  unfold tailWord_1651351
  simp only [CollatzResearch.WordTrace]
  refine ⟨60229719040444830142489907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40153146026963220094993271 60229719040444830142489907)
  ·
    refine ⟨90344578560667245213734861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60229719040444830142489907 90344578560667245213734861)
    ·
      refine ⟨33879216960250216955150573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90344578560667245213734861 33879216960250216955150573)
      ·
        refine ⟨12704706360093831358181465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33879216960250216955150573 12704706360093831358181465)
        ·
          refine ⟨9528529770070373518636099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12704706360093831358181465 9528529770070373518636099)
          ·
            refine ⟨14292794655105560277954149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9528529770070373518636099 14292794655105560277954149)
            ·
              refine ⟨2679898997832292552116403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14292794655105560277954149 2679898997832292552116403)
              ·
                refine ⟨4019848496748438828174605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2679898997832292552116403 4019848496748438828174605)
                ·
                  refine ⟨1507443186280664560565477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4019848496748438828174605 1507443186280664560565477)
                  ·
                    refine ⟨282645597427624605106027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1507443186280664560565477 282645597427624605106027)
                    ·
                      rfl

theorem cell23_1651351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 4].length) (baseStart_1651351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651351 prefixEnd_1651351 := by exact prefixLift 1651351
  have htrace : WordTrace (prefixWord ++ tailWord_1651351) baseStart_1651351 baseEnd_1651351 := by
    simpa [prefixWord, tailWord_1651351, baseEnd_1651351] using wordTrace_append hprefix tailTrace_1651351
  have hstable : (prefixWord ++ tailWord_1651351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651351).length < 2 ^ (prefixWord ++ tailWord_1651351).sum := by decide
  have hdescent : baseEnd_1651351 < baseStart_1651351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651358 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 2, 4, 2]
def baseStart_1651358 : Nat := 118140960795 + 1651358 * 2 ^ 59
def prefixEnd_1651358 : Nat := 4983230072969 + 3 ^ 40 * 1651358 * 2
def baseEnd_1651358 : Nat := 847940386647455287930549

theorem tailTrace_1651358 : CollatzResearch.WordTrace tailWord_1651358 prefixEnd_1651358 847940386647455287930549 := by
  unfold tailWord_1651358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7528746793927433792249341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40153316234279646891996485 7528746793927433792249341)
  ·
    refine ⟨2823280047722787672093503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7528746793927433792249341 2823280047722787672093503)
    ·
      refine ⟨4234920071584181508140255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2823280047722787672093503 4234920071584181508140255)
      ·
        refine ⟨6352380107376272262210383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4234920071584181508140255 6352380107376272262210383)
        ·
          refine ⟨9528570161064408393315575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6352380107376272262210383 9528570161064408393315575)
          ·
            refine ⟨14292855241596612589973363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9528570161064408393315575 14292855241596612589973363)
            ·
              refine ⟨21439282862394918884960045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14292855241596612589973363 21439282862394918884960045)
              ·
                refine ⟨8039731073398094581860017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21439282862394918884960045 8039731073398094581860017)
                ·
                  refine ⟨6029798305048570936395013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8039731073398094581860017 6029798305048570936395013)
                  ·
                    refine ⟨1130587182196607050574065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6029798305048570936395013 1130587182196607050574065)
                    ·
                      refine ⟨847940386647455287930549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1130587182196607050574065 847940386647455287930549)
                      ·
                        rfl

theorem cell23_1651358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_1651358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651358 prefixEnd_1651358 := by exact prefixLift 1651358
  have htrace : WordTrace (prefixWord ++ tailWord_1651358) baseStart_1651358 baseEnd_1651358 := by
    simpa [prefixWord, tailWord_1651358, baseEnd_1651358] using wordTrace_append hprefix tailTrace_1651358
  have hstable : (prefixWord ++ tailWord_1651358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651358).length < 2 ^ (prefixWord ++ tailWord_1651358).sum := by decide
  have hdescent : baseEnd_1651358 < baseStart_1651358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651424 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 1, 6]
def baseStart_1651424 : Nat := 118140960795 + 1651424 * 2 ^ 59
def prefixEnd_1651424 : Nat := 4983230072969 + 3 ^ 40 * 1651424 * 2
def baseEnd_1651424 : Nat := 282658092123550676568415

theorem tailTrace_1651424 : CollatzResearch.WordTrace tailWord_1651424 prefixEnd_1651424 282658092123550676568415 := by
  unfold tailWord_1651424
  simp only [CollatzResearch.WordTrace]
  refine ⟨30116190784590181804948663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40154921046120242406598217 30116190784590181804948663)
  ·
    refine ⟨45174286176885272707422995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30116190784590181804948663 45174286176885272707422995)
    ·
      refine ⟨67761429265327909061134493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45174286176885272707422995 67761429265327909061134493)
      ·
        refine ⟨25410535974497965897925435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67761429265327909061134493 25410535974497965897925435)
        ·
          refine ⟨38115803961746948846888153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25410535974497965897925435 38115803961746948846888153)
          ·
            refine ⟨28586852971310211635166115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38115803961746948846888153 28586852971310211635166115)
            ·
              refine ⟨42880279456965317452749173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28586852971310211635166115 42880279456965317452749173)
              ·
                refine ⟨4020026199090498511195235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42880279456965317452749173 4020026199090498511195235)
                ·
                  refine ⟨6030039298635747766792853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4020026199090498511195235 6030039298635747766792853)
                  ·
                    refine ⟨282658092123550676568415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6030039298635747766792853 282658092123550676568415)
                    ·
                      rfl

theorem cell23_1651424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 1, 6].length) (baseStart_1651424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651424 prefixEnd_1651424 := by exact prefixLift 1651424
  have htrace : WordTrace (prefixWord ++ tailWord_1651424) baseStart_1651424 baseEnd_1651424 := by
    simpa [prefixWord, tailWord_1651424, baseEnd_1651424] using wordTrace_append hprefix tailTrace_1651424
  have hstable : (prefixWord ++ tailWord_1651424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651424).length < 2 ^ (prefixWord ++ tailWord_1651424).sum := by decide
  have hdescent : baseEnd_1651424 < baseStart_1651424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651428 : List Nat := [2, 3, 1, 1, 1, 6, 1, 2, 1, 5]
def baseStart_1651428 : Nat := 118140960795 + 1651428 * 2 ^ 59
def prefixEnd_1651428 : Nat := 4983230072969 + 3 ^ 40 * 1651428 * 2
def baseEnd_1651428 : Nat := 282658776764423338018409

theorem tailTrace_1651428 : CollatzResearch.WordTrace tailWord_1651428 prefixEnd_1651428 282658776764423338018409 := by
  unfold tailWord_1651428
  simp only [CollatzResearch.WordTrace]
  refine ⟨30116263730582936146521469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40155018307443914862028625 30116263730582936146521469)
  ·
    refine ⟨11293598898968601054945551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30116263730582936146521469 11293598898968601054945551)
    ·
      refine ⟨16940398348452901582418327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11293598898968601054945551 16940398348452901582418327)
      ·
        refine ⟨25410597522679352373627491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16940398348452901582418327 25410597522679352373627491)
        ·
          refine ⟨38115896284019028560441237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25410597522679352373627491 38115896284019028560441237)
          ·
            refine ⟨1786682638313391963770683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38115896284019028560441237 1786682638313391963770683)
            ·
              refine ⟨2680023957470087945656025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1786682638313391963770683 2680023957470087945656025)
              ·
                refine ⟨2010017968102565959242019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2680023957470087945656025 2010017968102565959242019)
                ·
                  refine ⟨3015026952153848938863029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010017968102565959242019 3015026952153848938863029)
                  ·
                    refine ⟨282658776764423338018409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3015026952153848938863029 282658776764423338018409)
                    ·
                      rfl

theorem cell23_1651428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 6, 1, 2, 1, 5].length) (baseStart_1651428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651428 prefixEnd_1651428 := by exact prefixLift 1651428
  have htrace : WordTrace (prefixWord ++ tailWord_1651428) baseStart_1651428 baseEnd_1651428 := by
    simpa [prefixWord, tailWord_1651428, baseEnd_1651428] using wordTrace_append hprefix tailTrace_1651428
  have hstable : (prefixWord ++ tailWord_1651428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651428).length < 2 ^ (prefixWord ++ tailWord_1651428).sum := by decide
  have hdescent : baseEnd_1651428 < baseStart_1651428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651448 : List Nat := [2, 1, 2, 1, 1, 2, 7, 1, 1, 1, 4]
def baseStart_1651448 : Nat := 118140960795 + 1651448 * 2 ^ 59
def prefixEnd_1651448 : Nat := 4983230072969 + 3 ^ 40 * 1651448 * 2
def baseEnd_1651448 : Nat := 847986599906359935805135

theorem tailTrace_1651448 : CollatzResearch.WordTrace tailWord_1651448 prefixEnd_1651448 847986599906359935805135 := by
  unfold tailWord_1651448
  simp only [CollatzResearch.WordTrace]
  refine ⟨30116628460546707854385499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40155504614062277139180665 30116628460546707854385499)
  ·
    refine ⟨45174942690820061781578249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30116628460546707854385499 45174942690820061781578249)
    ·
      refine ⟨33881207018115046336183687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45174942690820061781578249 33881207018115046336183687)
      ·
        refine ⟨50821810527172569504275531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33881207018115046336183687 50821810527172569504275531)
        ·
          refine ⟨76232715790758854256413297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50821810527172569504275531 76232715790758854256413297)
          ·
            refine ⟨57174536843069140692309973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76232715790758854256413297 57174536843069140692309973)
            ·
              refine ⟨1340028207259432984976015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 57174536843069140692309973 1340028207259432984976015)
              ·
                refine ⟨2010042310889149477464023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340028207259432984976015 2010042310889149477464023)
                ·
                  refine ⟨3015063466333724216196035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010042310889149477464023 3015063466333724216196035)
                  ·
                    refine ⟨4522595199500586324294053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3015063466333724216196035 4522595199500586324294053)
                    ·
                      refine ⟨847986599906359935805135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4522595199500586324294053 847986599906359935805135)
                      ·
                        rfl

theorem cell23_1651448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 1, 1, 1, 4].length) (baseStart_1651448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651448 prefixEnd_1651448 := by exact prefixLift 1651448
  have htrace : WordTrace (prefixWord ++ tailWord_1651448) baseStart_1651448 baseEnd_1651448 := by
    simpa [prefixWord, tailWord_1651448, baseEnd_1651448] using wordTrace_append hprefix tailTrace_1651448
  have hstable : (prefixWord ++ tailWord_1651448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651448).length < 2 ^ (prefixWord ++ tailWord_1651448).sum := by decide
  have hdescent : baseEnd_1651448 < baseStart_1651448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651502 : List Nat := [4, 1, 3, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_1651502 : Nat := 118140960795 + 1651502 * 2 ^ 59
def prefixEnd_1651502 : Nat := 4983230072969 + 3 ^ 40 * 1651502 * 2
def baseEnd_1651502 : Nat := 848014327861702724529887

theorem tailTrace_1651502 : CollatzResearch.WordTrace tailWord_1651502 prefixEnd_1651502 848014327861702724529887 := by
  unfold tailWord_1651502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7529403307862222866404595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40156817641931855287491173 7529403307862222866404595)
  ·
    refine ⟨11294104961793334299606893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7529403307862222866404595 11294104961793334299606893)
    ·
      refine ⟨4235289360672500362352585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11294104961793334299606893 4235289360672500362352585)
      ·
        refine ⟨3176467020504375271764439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4235289360672500362352585 3176467020504375271764439)
        ·
          refine ⟨4764700530756562907646659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3176467020504375271764439 4764700530756562907646659)
          ·
            refine ⟨7147050796134844361469989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4764700530756562907646659 7147050796134844361469989)
            ·
              refine ⟨1340072024275283317775623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7147050796134844361469989 1340072024275283317775623)
              ·
                refine ⟨2010108036412924976663435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340072024275283317775623 2010108036412924976663435)
                ·
                  refine ⟨3015162054619387464995153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010108036412924976663435 3015162054619387464995153)
                  ·
                    refine ⟨2261371540964540598746365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3015162054619387464995153 2261371540964540598746365)
                    ·
                      refine ⟨848014327861702724529887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2261371540964540598746365 848014327861702724529887)
                      ·
                        rfl

theorem cell23_1651502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_1651502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651502 prefixEnd_1651502 := by exact prefixLift 1651502
  have htrace : WordTrace (prefixWord ++ tailWord_1651502) baseStart_1651502 baseEnd_1651502 := by
    simpa [prefixWord, tailWord_1651502, baseEnd_1651502] using wordTrace_append hprefix tailTrace_1651502
  have hstable : (prefixWord ++ tailWord_1651502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651502).length < 2 ^ (prefixWord ++ tailWord_1651502).sum := by decide
  have hdescent : baseEnd_1651502 < baseStart_1651502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651532 : List Nat := [2, 2, 1, 3, 3, 2, 3, 1, 2, 1, 3]
def baseStart_1651532 : Nat := 118140960795 + 1651532 * 2 ^ 59
def prefixEnd_1651532 : Nat := 4983230072969 + 3 ^ 40 * 1651532 * 2
def baseEnd_1651532 : Nat := 848029732281337607154749

theorem tailTrace_1651532 : CollatzResearch.WordTrace tailWord_1651532 prefixEnd_1651532 848029732281337607154749 := by
  unfold tailWord_1651532
  simp only [CollatzResearch.WordTrace]
  refine ⟨30118160326394549027414425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40157547101859398703219233 30118160326394549027414425)
  ·
    refine ⟨22588620244795911770560819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30118160326394549027414425 22588620244795911770560819)
    ·
      refine ⟨33882930367193867655841229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22588620244795911770560819 33882930367193867655841229)
      ·
        refine ⟨12706098887697700370940461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33882930367193867655841229 12706098887697700370940461)
        ·
          refine ⟨4764787082886637639102673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12706098887697700370940461 4764787082886637639102673)
          ·
            refine ⟨3573590312164978229327005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4764787082886637639102673 3573590312164978229327005)
            ·
              refine ⟨1340096367061866835997627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3573590312164978229327005 1340096367061866835997627)
              ·
                refine ⟨2010144550592800253996441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340096367061866835997627 2010144550592800253996441)
                ·
                  refine ⟨1507608412944600190497331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2010144550592800253996441 1507608412944600190497331)
                  ·
                    refine ⟨2261412619416900285745997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1507608412944600190497331 2261412619416900285745997)
                    ·
                      refine ⟨848029732281337607154749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2261412619416900285745997 848029732281337607154749)
                      ·
                        rfl

theorem cell23_1651532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 2, 1, 3].length) (baseStart_1651532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651532 prefixEnd_1651532 := by exact prefixLift 1651532
  have htrace : WordTrace (prefixWord ++ tailWord_1651532) baseStart_1651532 baseEnd_1651532 := by
    simpa [prefixWord, tailWord_1651532, baseEnd_1651532] using wordTrace_append hprefix tailTrace_1651532
  have hstable : (prefixWord ++ tailWord_1651532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651532).length < 2 ^ (prefixWord ++ tailWord_1651532).sum := by decide
  have hdescent : baseEnd_1651532 < baseStart_1651532 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651541 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_1651541 : Nat := 118140960795 + 1651541 * 2 ^ 59
def prefixEnd_1651541 : Nat := 4983230072969 + 3 ^ 40 * 1651541 * 2
def baseEnd_1651541 : Nat := 848034353607228071942207

theorem tailTrace_1651541 : CollatzResearch.WordTrace tailWord_1651541 prefixEnd_1651541 848034353607228071942207 := by
  unfold tailWord_1651541
  simp only [CollatzResearch.WordTrace]
  refine ⟨60236648909756492591906477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40157765939837661727937651 60236648909756492591906477)
  ·
    refine ⟨22588743341158684721964929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60236648909756492591906477 22588743341158684721964929)
    ·
      refine ⟨16941557505869013541473697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22588743341158684721964929 16941557505869013541473697)
      ·
        refine ⟨12706168129401760156105273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16941557505869013541473697 12706168129401760156105273)
        ·
          refine ⟨9529626097051320117078955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12706168129401760156105273 9529626097051320117078955)
          ·
            refine ⟨14294439145576980175618433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9529626097051320117078955 14294439145576980175618433)
            ·
              refine ⟨10720829359182735131713825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14294439145576980175618433 10720829359182735131713825)
              ·
                refine ⟨8040622019387051348785369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10720829359182735131713825 8040622019387051348785369)
                ·
                  refine ⟨6030466514540288511589027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8040622019387051348785369 6030466514540288511589027)
                  ·
                    refine ⟨9045699771810432767383541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6030466514540288511589027 9045699771810432767383541)
                    ·
                      refine ⟨848034353607228071942207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9045699771810432767383541 848034353607228071942207)
                      ·
                        rfl

theorem cell23_1651541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_1651541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651541 prefixEnd_1651541 := by exact prefixLift 1651541
  have htrace : WordTrace (prefixWord ++ tailWord_1651541) baseStart_1651541 baseEnd_1651541 := by
    simpa [prefixWord, tailWord_1651541, baseEnd_1651541] using wordTrace_append hprefix tailTrace_1651541
  have hstable : (prefixWord ++ tailWord_1651541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651541).length < 2 ^ (prefixWord ++ tailWord_1651541).sum := by decide
  have hdescent : baseEnd_1651541 < baseStart_1651541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651555 : List Nat := [1, 1, 1, 5, 3, 1, 1, 2, 4, 2, 2]
def baseStart_1651555 : Nat := 118140960795 + 1651555 * 2 ^ 59
def prefixEnd_1651555 : Nat := 4983230072969 + 3 ^ 40 * 1651555 * 2
def baseEnd_1651555 : Nat := 848041542336391017167143

theorem tailTrace_1651555 : CollatzResearch.WordTrace tailWord_1651555 prefixEnd_1651555 848041542336391017167143 := by
  unfold tailWord_1651555
  simp only [CollatzResearch.WordTrace]
  refine ⟨60237159531705772982916119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40158106354470515321944079 60237159531705772982916119)
  ·
    refine ⟨90355739297558659474374179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60237159531705772982916119 90355739297558659474374179)
    ·
      refine ⟨135533608946337989211561269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90355739297558659474374179 135533608946337989211561269)
      ·
        refine ⟨12706275838719186488583869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135533608946337989211561269 12706275838719186488583869)
        ·
          refine ⟨4764853439519694933218951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12706275838719186488583869 4764853439519694933218951)
          ·
            refine ⟨7147280159279542399828427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4764853439519694933218951 7147280159279542399828427)
            ·
              refine ⟨10720920238919313599742641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7147280159279542399828427 10720920238919313599742641)
              ·
                refine ⟨8040690179189485199806981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10720920238919313599742641 8040690179189485199806981)
                ·
                  refine ⟨1507629408598028474963809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8040690179189485199806981 1507629408598028474963809)
                  ·
                    refine ⟨1130722056448521356222857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1507629408598028474963809 1130722056448521356222857)
                    ·
                      refine ⟨848041542336391017167143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1130722056448521356222857 848041542336391017167143)
                      ·
                        rfl

theorem cell23_1651555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_1651555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651555 prefixEnd_1651555 := by exact prefixLift 1651555
  have htrace : WordTrace (prefixWord ++ tailWord_1651555) baseStart_1651555 baseEnd_1651555 := by
    simpa [prefixWord, tailWord_1651555, baseEnd_1651555] using wordTrace_append hprefix tailTrace_1651555
  have hstable : (prefixWord ++ tailWord_1651555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651555).length < 2 ^ (prefixWord ++ tailWord_1651555).sum := by decide
  have hdescent : baseEnd_1651555 < baseStart_1651555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651571 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 3]
def baseStart_1651571 : Nat := 118140960795 + 1651571 * 2 ^ 59
def prefixEnd_1651571 : Nat := 4983230072969 + 3 ^ 40 * 1651571 * 2
def baseEnd_1651571 : Nat := 848049758026862954567069

theorem tailTrace_1651571 : CollatzResearch.WordTrace tailWord_1651571 prefixEnd_1651571 848049758026862954567069 := by
  unfold tailWord_1651571
  simp only [CollatzResearch.WordTrace]
  refine ⟨60237743099647807715498567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40158495399765205143665711 60237743099647807715498567)
  ·
    refine ⟨90356614649471711573247851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60237743099647807715498567 90356614649471711573247851)
    ·
      refine ⟨135534921974207567359871777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90356614649471711573247851 135534921974207567359871777)
      ·
        refine ⟨101651191480655675519903833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135534921974207567359871777 101651191480655675519903833)
        ·
          refine ⟨76238393610491756639927875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101651191480655675519903833 76238393610491756639927875)
          ·
            refine ⟨114357590415737634959891813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76238393610491756639927875 114357590415737634959891813)
            ·
              refine ⟨21442048202950806554979715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114357590415737634959891813 21442048202950806554979715)
              ·
                refine ⟨32163072304426209832469573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21442048202950806554979715 32163072304426209832469573)
                ·
                  refine ⟨6030576057079914343588045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32163072304426209832469573 6030576057079914343588045)
                  ·
                    refine ⟨2261466021404967878845517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6030576057079914343588045 2261466021404967878845517)
                    ·
                      refine ⟨848049758026862954567069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2261466021404967878845517 848049758026862954567069)
                      ·
                        rfl

theorem cell23_1651571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 3].length) (baseStart_1651571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651571 prefixEnd_1651571 := by exact prefixLift 1651571
  have htrace : WordTrace (prefixWord ++ tailWord_1651571) baseStart_1651571 baseEnd_1651571 := by
    simpa [prefixWord, tailWord_1651571, baseEnd_1651571] using wordTrace_append hprefix tailTrace_1651571
  have hstable : (prefixWord ++ tailWord_1651571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651571).length < 2 ^ (prefixWord ++ tailWord_1651571).sum := by decide
  have hdescent : baseEnd_1651571 < baseStart_1651571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651589 : List Nat := [1, 3, 1, 1, 3, 5, 2, 1, 2, 2, 2]
def baseStart_1651589 : Nat := 118140960795 + 1651589 * 2 ^ 59
def prefixEnd_1651589 : Nat := 4983230072969 + 3 ^ 40 * 1651589 * 2
def baseEnd_1651589 : Nat := 848059000678643884141987

theorem tailTrace_1651589 : CollatzResearch.WordTrace tailWord_1651589 prefixEnd_1651589 848059000678643884141987 := by
  unfold tailWord_1651589
  simp only [CollatzResearch.WordTrace]
  refine ⟨60238399613582596789653821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40158933075721731193102547 60238399613582596789653821)
  ·
    refine ⟨22589399855093473796120183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60238399613582596789653821 22589399855093473796120183)
    ·
      refine ⟨33884099782640210694180275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22589399855093473796120183 33884099782640210694180275)
      ·
        refine ⟨50826149673960316041270413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33884099782640210694180275 50826149673960316041270413)
        ·
          refine ⟨19059806127735118515476405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50826149673960316041270413 19059806127735118515476405)
          ·
            refine ⟨1786856824475167360825913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19059806127735118515476405 1786856824475167360825913)
            ·
              refine ⟨1340142618356375520619435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1786856824475167360825913 1340142618356375520619435)
              ·
                refine ⟨2010213927534563280929153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340142618356375520619435 2010213927534563280929153)
                ·
                  refine ⟨1507660445650922460696865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2010213927534563280929153 1507660445650922460696865)
                  ·
                    refine ⟨1130745334238191845522649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1507660445650922460696865 1130745334238191845522649)
                    ·
                      refine ⟨848059000678643884141987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1130745334238191845522649 848059000678643884141987)
                      ·
                        rfl

theorem cell23_1651589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 2, 1, 2, 2, 2].length) (baseStart_1651589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651589 prefixEnd_1651589 := by exact prefixLift 1651589
  have htrace : WordTrace (prefixWord ++ tailWord_1651589) baseStart_1651589 baseEnd_1651589 := by
    simpa [prefixWord, tailWord_1651589, baseEnd_1651589] using wordTrace_append hprefix tailTrace_1651589
  have hstable : (prefixWord ++ tailWord_1651589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651589).length < 2 ^ (prefixWord ++ tailWord_1651589).sum := by decide
  have hdescent : baseEnd_1651589 < baseStart_1651589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651618 : List Nat := [3, 3, 1, 2, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1651618 : Nat := 118140960795 + 1651618 * 2 ^ 59
def prefixEnd_1651618 : Nat := 4983230072969 + 3 ^ 40 * 1651618 * 2
def baseEnd_1651618 : Nat := 848073891617624270679353

theorem tailTrace_1651618 : CollatzResearch.WordTrace tailWord_1651618 prefixEnd_1651618 848073891617624270679353 := by
  unfold tailWord_1651618
  simp only [CollatzResearch.WordTrace]
  refine ⟨15059864332619383685614877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40159638220318356494973005 15059864332619383685614877)
  ·
    refine ⟨5647449124732268882105579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15059864332619383685614877 5647449124732268882105579)
    ·
      refine ⟨8471173687098403323158369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5647449124732268882105579 8471173687098403323158369)
      ·
        refine ⟨6353380265323802492368777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8471173687098403323158369 6353380265323802492368777)
        ·
          refine ⟨4765035198992851869276583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6353380265323802492368777 4765035198992851869276583)
          ·
            refine ⟨7147552798489277803914875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4765035198992851869276583 7147552798489277803914875)
            ·
              refine ⟨10721329197733916705872313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7147552798489277803914875 10721329197733916705872313)
              ·
                refine ⟨8040996898300437529404235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10721329197733916705872313 8040996898300437529404235)
                ·
                  refine ⟨12061495347450656294106353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8040996898300437529404235 12061495347450656294106353)
                  ·
                    refine ⟨9046121510587992220579765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12061495347450656294106353 9046121510587992220579765)
                    ·
                      refine ⟨848073891617624270679353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9046121510587992220579765 848073891617624270679353)
                      ·
                        rfl

theorem cell23_1651618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1651618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651618 prefixEnd_1651618 := by exact prefixLift 1651618
  have htrace : WordTrace (prefixWord ++ tailWord_1651618) baseStart_1651618 baseEnd_1651618 := by
    simpa [prefixWord, tailWord_1651618, baseEnd_1651618] using wordTrace_append hprefix tailTrace_1651618
  have hstable : (prefixWord ++ tailWord_1651618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651618).length < 2 ^ (prefixWord ++ tailWord_1651618).sum := by decide
  have hdescent : baseEnd_1651618 < baseStart_1651618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651628 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 4, 4, 2]
def baseStart_1651628 : Nat := 118140960795 + 1651628 * 2 ^ 59
def prefixEnd_1651628 : Nat := 4983230072969 + 3 ^ 40 * 1651628 * 2
def baseEnd_1651628 : Nat := 848079026424169231554307

theorem tailTrace_1651628 : CollatzResearch.WordTrace tailWord_1651628 prefixEnd_1651628 848079026424169231554307 := by
  unfold tailWord_1651628
  simp only [CollatzResearch.WordTrace]
  refine ⟨30119911030220653225161769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40159881373627537633549025 30119911030220653225161769)
  ·
    refine ⟨22589933272665489918871327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30119911030220653225161769 22589933272665489918871327)
    ·
      refine ⟨33884899908998234878306991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22589933272665489918871327 33884899908998234878306991)
      ·
        refine ⟨50827349863497352317460487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33884899908998234878306991 50827349863497352317460487)
        ·
          refine ⟨76241024795246028476190731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50827349863497352317460487 76241024795246028476190731)
          ·
            refine ⟨114361537192869042714286097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76241024795246028476190731 114361537192869042714286097)
            ·
              refine ⟨85771152894651782035714573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114361537192869042714286097 85771152894651782035714573)
              ·
                refine ⟨32164182335494418263392965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85771152894651782035714573 32164182335494418263392965)
                ·
                  refine ⟨6030784187905203424386181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32164182335494418263392965 6030784187905203424386181)
                  ·
                    refine ⟨1130772035232225642072409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6030784187905203424386181 1130772035232225642072409)
                    ·
                      refine ⟨848079026424169231554307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1130772035232225642072409 848079026424169231554307)
                      ·
                        rfl

theorem cell23_1651628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 4, 2].length) (baseStart_1651628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651628 prefixEnd_1651628 := by exact prefixLift 1651628
  have htrace : WordTrace (prefixWord ++ tailWord_1651628) baseStart_1651628 baseEnd_1651628 := by
    simpa [prefixWord, tailWord_1651628, baseEnd_1651628] using wordTrace_append hprefix tailTrace_1651628
  have hstable : (prefixWord ++ tailWord_1651628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651628).length < 2 ^ (prefixWord ++ tailWord_1651628).sum := by decide
  have hdescent : baseEnd_1651628 < baseStart_1651628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651672 : List Nat := [2, 1, 2, 2, 2, 4, 2, 3, 1, 4]
def baseStart_1651672 : Nat := 118140960795 + 1651672 * 2 ^ 59
def prefixEnd_1651672 : Nat := 4983230072969 + 3 ^ 40 * 1651672 * 2
def baseEnd_1651672 : Nat := 282700539857655686468035

theorem tailTrace_1651672 : CollatzResearch.WordTrace tailWord_1651672 prefixEnd_1651672 282700539857655686468035 := by
  unfold tailWord_1651672
  simp only [CollatzResearch.WordTrace]
  refine ⟨30120713436140950982462635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40160951248187934643283513 30120713436140950982462635)
  ·
    refine ⟨45181070154211426473693953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30120713436140950982462635 45181070154211426473693953)
    ·
      refine ⟨33885802615658569855270465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45181070154211426473693953 33885802615658569855270465)
      ·
        refine ⟨25414351961743927391452849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33885802615658569855270465 25414351961743927391452849)
        ·
          refine ⟨19060763971307945543589637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25414351961743927391452849 19060763971307945543589637)
          ·
            refine ⟨3573893244620239789423057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19060763971307945543589637 3573893244620239789423057)
            ·
              refine ⟨2680419933465179842067293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3573893244620239789423057 2680419933465179842067293)
              ·
                refine ⟨1005157475049442440775235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2680419933465179842067293 1005157475049442440775235)
                ·
                  refine ⟨1507736212574163661162853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005157475049442440775235 1507736212574163661162853)
                  ·
                    refine ⟨282700539857655686468035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1507736212574163661162853 282700539857655686468035)
                    ·
                      rfl

theorem cell23_1651672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 1, 4].length) (baseStart_1651672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651672 prefixEnd_1651672 := by exact prefixLift 1651672
  have htrace : WordTrace (prefixWord ++ tailWord_1651672) baseStart_1651672 baseEnd_1651672 := by
    simpa [prefixWord, tailWord_1651672, baseEnd_1651672] using wordTrace_append hprefix tailTrace_1651672
  have hstable : (prefixWord ++ tailWord_1651672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651672).length < 2 ^ (prefixWord ++ tailWord_1651672).sum := by decide
  have hdescent : baseEnd_1651672 < baseStart_1651672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651685 : List Nat := [1, 3, 1, 6, 1, 1, 1, 1, 8]
def baseStart_1651685 : Nat := 118140960795 + 1651685 * 2 ^ 59
def prefixEnd_1651685 : Nat := 4983230072969 + 3 ^ 40 * 1651685 * 2
def baseEnd_1651685 : Nat := 94234254980163945393505

theorem tailTrace_1651685 : CollatzResearch.WordTrace tailWord_1651685 prefixEnd_1651685 94234254980163945393505 := by
  unfold tailWord_1651685
  simp only [CollatzResearch.WordTrace]
  refine ⟨60241901021234805185148509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40161267347489870123432339 60241901021234805185148509)
  ·
    refine ⟨22590712882963051944430691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60241901021234805185148509 22590712882963051944430691)
    ·
      refine ⟨33886069324444577916646037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22590712882963051944430691 33886069324444577916646037)
      ·
        refine ⟨1588409499583339589842783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33886069324444577916646037 1588409499583339589842783)
        ·
          refine ⟨2382614249375009384764175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1588409499583339589842783 2382614249375009384764175)
          ·
            refine ⟨3573921374062514077146263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2382614249375009384764175 3573921374062514077146263)
            ·
              refine ⟨5360882061093771115719395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3573921374062514077146263 5360882061093771115719395)
              ·
                refine ⟨8041323091640656673579093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5360882061093771115719395 8041323091640656673579093)
                ·
                  refine ⟨94234254980163945393505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8041323091640656673579093 94234254980163945393505)
                  ·
                    rfl

theorem cell23_1651685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 8].length) (baseStart_1651685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651685 prefixEnd_1651685 := by exact prefixLift 1651685
  have htrace : WordTrace (prefixWord ++ tailWord_1651685) baseStart_1651685 baseEnd_1651685 := by
    simpa [prefixWord, tailWord_1651685, baseEnd_1651685] using wordTrace_append hprefix tailTrace_1651685
  have hstable : (prefixWord ++ tailWord_1651685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651685).length < 2 ^ (prefixWord ++ tailWord_1651685).sum := by decide
  have hdescent : baseEnd_1651685 < baseStart_1651685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651695 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 3, 1, 3]
def baseStart_1651695 : Nat := 118140960795 + 1651695 * 2 ^ 59
def prefixEnd_1651695 : Nat := 4983230072969 + 3 ^ 40 * 1651695 * 2
def baseEnd_1651695 : Nat := 848113429628020469416499

theorem tailTrace_1651695 : CollatzResearch.WordTrace tailWord_1651695 prefixEnd_1651695 848113429628020469416499 := by
  unfold tailWord_1651695
  simp only [CollatzResearch.WordTrace]
  refine ⟨60242265751198576893012539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40161510500799051262008359 60242265751198576893012539)
  ·
    refine ⟨90363398626797865339518809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60242265751198576893012539 90363398626797865339518809)
    ·
      refine ⟨67772548970098399004639107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90363398626797865339518809 67772548970098399004639107)
      ·
        refine ⟨101658823455147598506958661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67772548970098399004639107 101658823455147598506958661)
        ·
          refine ⟨19061029397840174720054749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101658823455147598506958661 19061029397840174720054749)
          ·
            refine ⟨7147886024190065520020531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19061029397840174720054749 7147886024190065520020531)
            ·
              refine ⟨10721829036285098280030797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7147886024190065520020531 10721829036285098280030797)
              ·
                refine ⟨4020685888606911855011549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10721829036285098280030797 4020685888606911855011549)
                ·
                  refine ⟨1507757208227591945629331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4020685888606911855011549 1507757208227591945629331)
                  ·
                    refine ⟨2261635812341387918443997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1507757208227591945629331 2261635812341387918443997)
                    ·
                      refine ⟨848113429628020469416499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2261635812341387918443997 848113429628020469416499)
                      ·
                        rfl

theorem cell23_1651695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 3, 1, 3].length) (baseStart_1651695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651695 prefixEnd_1651695 := by exact prefixLift 1651695
  have htrace : WordTrace (prefixWord ++ tailWord_1651695) baseStart_1651695 baseEnd_1651695 := by
    simpa [prefixWord, tailWord_1651695, baseEnd_1651695] using wordTrace_append hprefix tailTrace_1651695
  have hstable : (prefixWord ++ tailWord_1651695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651695).length < 2 ^ (prefixWord ++ tailWord_1651695).sum := by decide
  have hdescent : baseEnd_1651695 < baseStart_1651695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651702 : List Nat := [5, 1, 1, 1, 3, 2, 3, 1, 6]
def baseStart_1651702 : Nat := 118140960795 + 1651702 * 2 ^ 59
def prefixEnd_1651702 : Nat := 4983230072969 + 3 ^ 40 * 1651702 * 2
def baseEnd_1651702 : Nat := 94235224888066882447663

theorem tailTrace_1651702 : CollatzResearch.WordTrace tailWord_1651702 prefixEnd_1651702 94235224888066882447663 := by
  unfold tailWord_1651702
  simp only [CollatzResearch.WordTrace]
  refine ⟨3765157566385826068032335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40161680708115478059011573 3765157566385826068032335)
  ·
    refine ⟨5647736349578739102048503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3765157566385826068032335 5647736349578739102048503)
    ·
      refine ⟨8471604524368108653072755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5647736349578739102048503 8471604524368108653072755)
      ·
        refine ⟨12707406786552162979609133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8471604524368108653072755 12707406786552162979609133)
        ·
          refine ⟨4765277544957061117353425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12707406786552162979609133 4765277544957061117353425)
          ·
            refine ⟨3573958158717795838015069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4765277544957061117353425 3573958158717795838015069)
            ·
              refine ⟨1340234309519173439255651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3573958158717795838015069 1340234309519173439255651)
              ·
                refine ⟨2010351464278760158883477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340234309519173439255651 2010351464278760158883477)
                ·
                  refine ⟨94235224888066882447663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2010351464278760158883477 94235224888066882447663)
                  ·
                    rfl

theorem cell23_1651702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_1651702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651702 prefixEnd_1651702 := by exact prefixLift 1651702
  have htrace : WordTrace (prefixWord ++ tailWord_1651702) baseStart_1651702 baseEnd_1651702 := by
    simpa [prefixWord, tailWord_1651702, baseEnd_1651702] using wordTrace_append hprefix tailTrace_1651702
  have hstable : (prefixWord ++ tailWord_1651702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651702).length < 2 ^ (prefixWord ++ tailWord_1651702).sum := by decide
  have hdescent : baseEnd_1651702 < baseStart_1651702 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651745 : List Nat := [1, 2, 3, 2, 3, 1, 2, 1, 4, 4]
def baseStart_1651745 : Nat := 118140960795 + 1651745 * 2 ^ 59
def prefixEnd_1651745 : Nat := 4983230072969 + 3 ^ 40 * 1651745 * 2
def baseEnd_1651745 : Nat := 282713034553581757930423

theorem tailTrace_1651745 : CollatzResearch.WordTrace tailWord_1651745 prefixEnd_1651745 282713034553581757930423 := by
  unfold tailWord_1651745
  simp only [CollatzResearch.WordTrace]
  refine ⟨60244089401017435432332689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40162726267344956954888459 60244089401017435432332689)
  ·
    refine ⟨45183067050763076574249517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60244089401017435432332689 45183067050763076574249517)
    ·
      refine ⟨16943650144036153715343569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45183067050763076574249517 16943650144036153715343569)
      ·
        refine ⟨12707737608027115286507677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16943650144036153715343569 12707737608027115286507677)
        ·
          refine ⟨4765401603010168232440379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12707737608027115286507677 4765401603010168232440379)
          ·
            refine ⟨7148102404515252348660569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4765401603010168232440379 7148102404515252348660569)
            ·
              refine ⟨5361076803386439261495427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7148102404515252348660569 5361076803386439261495427)
              ·
                refine ⟨8041615205079658892243141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5361076803386439261495427 8041615205079658892243141)
                ·
                  refine ⟨1507802850952436042295589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8041615205079658892243141 1507802850952436042295589)
                  ·
                    refine ⟨282713034553581757930423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1507802850952436042295589 282713034553581757930423)
                    ·
                      rfl

theorem cell23_1651745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_1651745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651745 prefixEnd_1651745 := by exact prefixLift 1651745
  have htrace : WordTrace (prefixWord ++ tailWord_1651745) baseStart_1651745 baseEnd_1651745 := by
    simpa [prefixWord, tailWord_1651745, baseEnd_1651745] using wordTrace_append hprefix tailTrace_1651745
  have hstable : (prefixWord ++ tailWord_1651745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651745).length < 2 ^ (prefixWord ++ tailWord_1651745).sum := by decide
  have hdescent : baseEnd_1651745 < baseStart_1651745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651746 : List Nat := [3, 3, 1, 1, 1, 4, 3, 2, 1, 1, 3]
def baseStart_1651746 : Nat := 118140960795 + 1651746 * 2 ^ 59
def prefixEnd_1651746 : Nat := 4983230072969 + 3 ^ 40 * 1651746 * 2
def baseEnd_1651746 : Nat := 848139617141399769878765

theorem tailTrace_1651746 : CollatzResearch.WordTrace tailWord_1651746 prefixEnd_1651746 848139617141399769878765 := by
  unfold tailWord_1651746
  simp only [CollatzResearch.WordTrace]
  refine ⟨15061031468503453150779773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40162750582675875068746061 15061031468503453150779773)
  ·
    refine ⟨5647886800688794931542415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15061031468503453150779773 5647886800688794931542415)
    ·
      refine ⟨8471830201033192397313623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5647886800688794931542415 8471830201033192397313623)
      ·
        refine ⟨12707745301549788595970435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8471830201033192397313623 12707745301549788595970435)
        ·
          refine ⟨19061617952324682893955653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12707745301549788595970435 19061617952324682893955653)
          ·
            refine ⟨3574053366060878042616685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19061617952324682893955653 3574053366060878042616685)
            ·
              refine ⟨1340270012272829265981257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3574053366060878042616685 1340270012272829265981257)
              ·
                refine ⟨1005202509204621949485943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1340270012272829265981257 1005202509204621949485943)
                ·
                  refine ⟨1507803763806932924228915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005202509204621949485943 1507803763806932924228915)
                  ·
                    refine ⟨2261705645710399386343373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1507803763806932924228915 2261705645710399386343373)
                    ·
                      refine ⟨848139617141399769878765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2261705645710399386343373 848139617141399769878765)
                      ·
                        rfl

theorem cell23_1651746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_1651746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651746 prefixEnd_1651746 := by exact prefixLift 1651746
  have htrace : WordTrace (prefixWord ++ tailWord_1651746) baseStart_1651746 baseEnd_1651746 := by
    simpa [prefixWord, tailWord_1651746, baseEnd_1651746] using wordTrace_append hprefix tailTrace_1651746
  have hstable : (prefixWord ++ tailWord_1651746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651746).length < 2 ^ (prefixWord ++ tailWord_1651746).sum := by decide
  have hdescent : baseEnd_1651746 < baseStart_1651746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651772 : List Nat := [2, 2, 2, 2, 2, 2, 3, 2, 1, 2, 3]
def baseStart_1651772 : Nat := 118140960795 + 1651772 * 2 ^ 59
def prefixEnd_1651772 : Nat := 4983230072969 + 3 ^ 40 * 1651772 * 2
def baseEnd_1651772 : Nat := 848152967638416668153645

theorem tailTrace_1651772 : CollatzResearch.WordTrace tailWord_1651772 prefixEnd_1651772 848152967638416668153645 := by
  unfold tailWord_1651772
  simp only [CollatzResearch.WordTrace]
  refine ⟨30122537085959809521782785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40163382781279746029043713 30122537085959809521782785)
  ·
    refine ⟨22591902814469857141337089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30122537085959809521782785 22591902814469857141337089)
    ·
      refine ⟨16943927110852392856002817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22591902814469857141337089 16943927110852392856002817)
      ·
        refine ⟨12707945333139294642002113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16943927110852392856002817 12707945333139294642002113)
        ·
          refine ⟨9530958999854470981501585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12707945333139294642002113 9530958999854470981501585)
          ·
            refine ⟨7148219249890853236126189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9530958999854470981501585 7148219249890853236126189)
            ·
              refine ⟨2680582218709069963547321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7148219249890853236126189 2680582218709069963547321)
              ·
                refine ⟨2010436664031802472660491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2680582218709069963547321 2010436664031802472660491)
                ·
                  refine ⟨3015654996047703708990737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010436664031802472660491 3015654996047703708990737)
                  ·
                    refine ⟨2261741247035777781743053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3015654996047703708990737 2261741247035777781743053)
                    ·
                      refine ⟨848152967638416668153645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2261741247035777781743053 848152967638416668153645)
                      ·
                        rfl

theorem cell23_1651772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_1651772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651772 prefixEnd_1651772 := by exact prefixLift 1651772
  have htrace : WordTrace (prefixWord ++ tailWord_1651772) baseStart_1651772 baseEnd_1651772 := by
    simpa [prefixWord, tailWord_1651772, baseEnd_1651772] using wordTrace_append hprefix tailTrace_1651772
  have hstable : (prefixWord ++ tailWord_1651772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651772).length < 2 ^ (prefixWord ++ tailWord_1651772).sum := by decide
  have hdescent : baseEnd_1651772 < baseStart_1651772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651782 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1651782 : Nat := 118140960795 + 1651782 * 2 ^ 59
def prefixEnd_1651782 : Nat := 4983230072969 + 3 ^ 40 * 1651782 * 2
def baseEnd_1651782 : Nat := 848158102444961629028599

theorem tailTrace_1651782 : CollatzResearch.WordTrace tailWord_1651782 prefixEnd_1651782 848158102444961629028599 := by
  unfold tailWord_1651782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1882669965683855960982175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40163625934588927167619733 1882669965683855960982175)
  ·
    refine ⟨2824004948525783941473263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1882669965683855960982175 2824004948525783941473263)
    ·
      refine ⟨4236007422788675912209895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2824004948525783941473263 4236007422788675912209895)
      ·
        refine ⟨6354011134183013868314843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4236007422788675912209895 6354011134183013868314843)
        ·
          refine ⟨9531016701274520802472265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6354011134183013868314843 9531016701274520802472265)
          ·
            refine ⟨7148262525955890601854199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9531016701274520802472265 7148262525955890601854199)
            ·
              refine ⟨10722393788933835902781299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7148262525955890601854199 10722393788933835902781299)
              ·
                refine ⟨16083590683400753854171949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10722393788933835902781299 16083590683400753854171949)
                ·
                  refine ⟨6031346506275282695314481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16083590683400753854171949 6031346506275282695314481)
                  ·
                    refine ⟨4523509879706462021485861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6031346506275282695314481 4523509879706462021485861)
                    ·
                      refine ⟨848158102444961629028599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4523509879706462021485861 848158102444961629028599)
                      ·
                        rfl

theorem cell23_1651782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1651782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651782 prefixEnd_1651782 := by exact prefixLift 1651782
  have htrace : WordTrace (prefixWord ++ tailWord_1651782) baseStart_1651782 baseEnd_1651782 := by
    simpa [prefixWord, tailWord_1651782, baseEnd_1651782] using wordTrace_append hprefix tailTrace_1651782
  have hstable : (prefixWord ++ tailWord_1651782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651782).length < 2 ^ (prefixWord ++ tailWord_1651782).sum := by decide
  have hdescent : baseEnd_1651782 < baseStart_1651782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651785 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 4, 1, 3]
def baseStart_1651785 : Nat := 118140960795 + 1651785 * 2 ^ 59
def prefixEnd_1651785 : Nat := 4983230072969 + 3 ^ 40 * 1651785 * 2
def baseEnd_1651785 : Nat := 848159642886925117291085

theorem tailTrace_1651785 : CollatzResearch.WordTrace tailWord_1651785 prefixEnd_1651785 848159642886925117291085 := by
  unfold tailWord_1651785
  simp only [CollatzResearch.WordTrace]
  refine ⟨60245548320872522263788809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40163698880581681509192539 60245548320872522263788809)
  ·
    refine ⟨45184161240654391697841607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60245548320872522263788809 45184161240654391697841607)
    ·
      refine ⟨67776241860981587546762411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45184161240654391697841607 67776241860981587546762411)
      ·
        refine ⟨101664362791472381320143617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67776241860981587546762411 101664362791472381320143617)
        ·
          refine ⟨76248272093604285990107713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101664362791472381320143617 76248272093604285990107713)
          ·
            refine ⟨57186204070203214492580785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76248272093604285990107713 57186204070203214492580785)
            ·
              refine ⟨42889653052652410869435589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57186204070203214492580785 42889653052652410869435589)
              ·
                refine ⟨8041809947372327038019173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42889653052652410869435589 8041809947372327038019173)
                ·
                  refine ⟨1507839365132311319628595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8041809947372327038019173 1507839365132311319628595)
                  ·
                    refine ⟨2261759047698466979442893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1507839365132311319628595 2261759047698466979442893)
                    ·
                      refine ⟨848159642886925117291085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2261759047698466979442893 848159642886925117291085)
                      ·
                        rfl

theorem cell23_1651785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 4, 1, 3].length) (baseStart_1651785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651785 prefixEnd_1651785 := by exact prefixLift 1651785
  have htrace : WordTrace (prefixWord ++ tailWord_1651785) baseStart_1651785 baseEnd_1651785 := by
    simpa [prefixWord, tailWord_1651785, baseEnd_1651785] using wordTrace_append hprefix tailTrace_1651785
  have hstable : (prefixWord ++ tailWord_1651785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651785).length < 2 ^ (prefixWord ++ tailWord_1651785).sum := by decide
  have hdescent : baseEnd_1651785 < baseStart_1651785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651795 : List Nat := [1, 1, 1, 2, 1, 1, 2, 4, 5, 3, 2]
def baseStart_1651795 : Nat := 118140960795 + 1651795 * 2 ^ 59
def prefixEnd_1651795 : Nat := 4983230072969 + 3 ^ 40 * 1651795 * 2
def baseEnd_1651795 : Nat := 848164777693470078166039

theorem tailTrace_1651795 : CollatzResearch.WordTrace tailWord_1651795 prefixEnd_1651795 848164777693470078166039 := by
  unfold tailWord_1651795
  simp only [CollatzResearch.WordTrace]
  refine ⟨60245913050836293971652839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40163942033890862647768559 60245913050836293971652839)
  ·
    refine ⟨90368869576254440957479259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60245913050836293971652839 90368869576254440957479259)
    ·
      refine ⟨135553304364381661436218889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90368869576254440957479259 135553304364381661436218889)
      ·
        refine ⟨101664978273286246077164167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135553304364381661436218889 101664978273286246077164167)
        ·
          refine ⟨152497467409929369115746251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101664978273286246077164167 152497467409929369115746251)
          ·
            refine ⟨228746201114894053673619377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152497467409929369115746251 228746201114894053673619377)
            ·
              refine ⟨171559650836170540255214533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228746201114894053673619377 171559650836170540255214533)
              ·
                refine ⟨32167434531781976297852725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171559650836170540255214533 32167434531781976297852725)
                ·
                  refine ⟨3015696987354560277923693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32167434531781976297852725 3015696987354560277923693)
                  ·
                    refine ⟨1130886370257960104221385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3015696987354560277923693 1130886370257960104221385)
                    ·
                      refine ⟨848164777693470078166039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1130886370257960104221385 848164777693470078166039)
                      ·
                        rfl

theorem cell23_1651795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 3, 2].length) (baseStart_1651795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651795 prefixEnd_1651795 := by exact prefixLift 1651795
  have htrace : WordTrace (prefixWord ++ tailWord_1651795) baseStart_1651795 baseEnd_1651795 := by
    simpa [prefixWord, tailWord_1651795, baseEnd_1651795] using wordTrace_append hprefix tailTrace_1651795
  have hstable : (prefixWord ++ tailWord_1651795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651795).length < 2 ^ (prefixWord ++ tailWord_1651795).sum := by decide
  have hdescent : baseEnd_1651795 < baseStart_1651795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651808 : List Nat := [2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 4]
def baseStart_1651808 : Nat := 118140960795 + 1651808 * 2 ^ 59
def prefixEnd_1651808 : Nat := 4983230072969 + 3 ^ 40 * 1651808 * 2
def baseEnd_1651808 : Nat := 848171452941978527303479

theorem tailTrace_1651808 : CollatzResearch.WordTrace tailWord_1651808 prefixEnd_1651808 848171452941978527303479 := by
  unfold tailWord_1651808
  simp only [CollatzResearch.WordTrace]
  refine ⟨30123193599894598595938039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40164258133192798127917385 30123193599894598595938039)
  ·
    refine ⟨45184790399841897893907059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30123193599894598595938039 45184790399841897893907059)
    ·
      refine ⟨67777185599762846840860589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45184790399841897893907059 67777185599762846840860589)
      ·
        refine ⟨25416444599911067565322721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67777185599762846840860589 25416444599911067565322721)
        ·
          refine ⟨19062333449933300673992041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25416444599911067565322721 19062333449933300673992041)
          ·
            refine ⟨14296750087449975505494031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19062333449933300673992041 14296750087449975505494031)
            ·
              refine ⟨21445125131174963258241047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14296750087449975505494031 21445125131174963258241047)
              ·
                refine ⟨32167687696762444887361571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21445125131174963258241047 32167687696762444887361571)
                ·
                  refine ⟨48251531545143667331042357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32167687696762444887361571 48251531545143667331042357)
                  ·
                    refine ⟨4523581082357218812285221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48251531545143667331042357 4523581082357218812285221)
                    ·
                      refine ⟨848171452941978527303479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4523581082357218812285221 848171452941978527303479)
                      ·
                        rfl

theorem cell23_1651808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_1651808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651808 prefixEnd_1651808 := by exact prefixLift 1651808
  have htrace : WordTrace (prefixWord ++ tailWord_1651808) baseStart_1651808 baseEnd_1651808 := by
    simpa [prefixWord, tailWord_1651808, baseEnd_1651808] using wordTrace_append hprefix tailTrace_1651808
  have hstable : (prefixWord ++ tailWord_1651808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651808).length < 2 ^ (prefixWord ++ tailWord_1651808).sum := by decide
  have hdescent : baseEnd_1651808 < baseStart_1651808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651859 : List Nat := [1, 1, 1, 2, 1, 2, 7, 2, 2, 2, 2]
def baseStart_1651859 : Nat := 118140960795 + 1651859 * 2 ^ 59
def prefixEnd_1651859 : Nat := 4983230072969 + 3 ^ 40 * 1651859 * 2
def baseEnd_1651859 : Nat := 848197640455357827765745

theorem tailTrace_1651859 : CollatzResearch.WordTrace tailWord_1651859 prefixEnd_1651859 848197640455357827765745 := by
  unfold tailWord_1651859
  simp only [CollatzResearch.WordTrace]
  refine ⟨60248247322604432901982631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40165498215069621934655087 60248247322604432901982631)
  ·
    refine ⟨90372370983906649352973947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60248247322604432901982631 90372370983906649352973947)
    ·
      refine ⟨135558556475859974029460921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90372370983906649352973947 135558556475859974029460921)
      ·
        refine ⟨101668917356894980522095691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135558556475859974029460921 101668917356894980522095691)
        ·
          refine ⟨152503376035342470783143537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101668917356894980522095691 152503376035342470783143537)
          ·
            refine ⟨114377532026506853087357653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152503376035342470783143537 114377532026506853087357653)
            ·
              refine ⟨2680723406871254369234945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 114377532026506853087357653 2680723406871254369234945)
              ·
                refine ⟨2010542555153440776926209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2680723406871254369234945 2010542555153440776926209)
                ·
                  refine ⟨1507906916365080582694657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2010542555153440776926209 1507906916365080582694657)
                  ·
                    refine ⟨1130930187273810437020993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1507906916365080582694657 1130930187273810437020993)
                    ·
                      refine ⟨848197640455357827765745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1130930187273810437020993 848197640455357827765745)
                      ·
                        rfl

theorem cell23_1651859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 7, 2, 2, 2, 2].length) (baseStart_1651859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651859 prefixEnd_1651859 := by exact prefixLift 1651859
  have htrace : WordTrace (prefixWord ++ tailWord_1651859) baseStart_1651859 baseEnd_1651859 := by
    simpa [prefixWord, tailWord_1651859, baseEnd_1651859] using wordTrace_append hprefix tailTrace_1651859
  have hstable : (prefixWord ++ tailWord_1651859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651859).length < 2 ^ (prefixWord ++ tailWord_1651859).sum := by decide
  have hdescent : baseEnd_1651859 < baseStart_1651859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651882 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 7]
def baseStart_1651882 : Nat := 118140960795 + 1651882 * 2 ^ 59
def prefixEnd_1651882 : Nat := 4983230072969 + 3 ^ 40 * 1651882 * 2
def baseEnd_1651882 : Nat := 94245494501156804197571

theorem tailTrace_1651882 : CollatzResearch.WordTrace tailWord_1651882 prefixEnd_1651882 94245494501156804197571 := by
  unfold tailWord_1651882
  simp only [CollatzResearch.WordTrace]
  refine ⟨15062271550380276957517475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40166057467680738553379933 15062271550380276957517475)
  ·
    refine ⟨22593407325570415436276213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15062271550380276957517475 22593407325570415436276213)
    ·
      refine ⟨2118131936772226447150895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22593407325570415436276213 2118131936772226447150895)
      ·
        refine ⟨3177197905158339670726343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2118131936772226447150895 3177197905158339670726343)
        ·
          refine ⟨4765796857737509506089515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3177197905158339670726343 4765796857737509506089515)
          ·
            refine ⟨7148695286606264259134273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4765796857737509506089515 7148695286606264259134273)
            ·
              refine ⟨5361521464954698194350705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7148695286606264259134273 5361521464954698194350705)
              ·
                refine ⟨4021141098716023645763029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5361521464954698194350705 4021141098716023645763029)
                ·
                  refine ⟨94245494501156804197571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4021141098716023645763029 94245494501156804197571)
                  ·
                    rfl

theorem cell23_1651882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 7].length) (baseStart_1651882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651882 prefixEnd_1651882 := by exact prefixLift 1651882
  have htrace : WordTrace (prefixWord ++ tailWord_1651882) baseStart_1651882 baseEnd_1651882 := by
    simpa [prefixWord, tailWord_1651882, baseEnd_1651882] using wordTrace_append hprefix tailTrace_1651882
  have hstable : (prefixWord ++ tailWord_1651882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651882).length < 2 ^ (prefixWord ++ tailWord_1651882).sum := by decide
  have hdescent : baseEnd_1651882 < baseStart_1651882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651888 : List Nat := [2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 7]
def baseStart_1651888 : Nat := 118140960795 + 1651888 * 2 ^ 59
def prefixEnd_1651888 : Nat := 4983230072969 + 3 ^ 40 * 1651888 * 2
def baseEnd_1651888 : Nat := 848212531394338214303111

theorem tailTrace_1651888 : CollatzResearch.WordTrace tailWord_1651888 prefixEnd_1651888 848212531394338214303111 := by
  unfold tailWord_1651888
  simp only [CollatzResearch.WordTrace]
  refine ⟨30124652519749685427394159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40166203359666247236525545 30124652519749685427394159)
  ·
    refine ⟨45186978779624528141091239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30124652519749685427394159 45186978779624528141091239)
    ·
      refine ⟨67780468169436792211636859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45186978779624528141091239 67780468169436792211636859)
      ·
        refine ⟨101670702254155188317455289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67780468169436792211636859 101670702254155188317455289)
        ·
          refine ⟨76253026690616391238091467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101670702254155188317455289 76253026690616391238091467)
          ·
            refine ⟨114379540035924586857137201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76253026690616391238091467 114379540035924586857137201)
            ·
              refine ⟨85784655026943440142852901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114379540035924586857137201 85784655026943440142852901)
              ·
                refine ⟨16084622817551895026784919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85784655026943440142852901 16084622817551895026784919)
                ·
                  refine ⟨24126934226327842540177379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16084622817551895026784919 24126934226327842540177379)
                  ·
                    refine ⟨36190401339491763810266069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24126934226327842540177379 36190401339491763810266069)
                    ·
                      refine ⟨848212531394338214303111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36190401339491763810266069 848212531394338214303111)
                      ·
                        rfl

theorem cell23_1651888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 7].length) (baseStart_1651888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651888 prefixEnd_1651888 := by exact prefixLift 1651888
  have htrace : WordTrace (prefixWord ++ tailWord_1651888) baseStart_1651888 baseEnd_1651888 := by
    simpa [prefixWord, tailWord_1651888, baseEnd_1651888] using wordTrace_append hprefix tailTrace_1651888
  have hstable : (prefixWord ++ tailWord_1651888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651888).length < 2 ^ (prefixWord ++ tailWord_1651888).sum := by decide
  have hdescent : baseEnd_1651888 < baseStart_1651888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651895 : List Nat := [1, 1, 3, 1, 4, 1, 2, 3, 2, 5]
def baseStart_1651895 : Nat := 118140960795 + 1651895 * 2 ^ 59
def prefixEnd_1651895 : Nat := 4983230072969 + 3 ^ 40 * 1651895 * 2
def baseEnd_1651895 : Nat := 282738708586306562305193

theorem tailTrace_1651895 : CollatzResearch.WordTrace tailWord_1651895 prefixEnd_1651895 282738708586306562305193 := by
  unfold tailWord_1651895
  simp only [CollatzResearch.WordTrace]
  refine ⟨60249560350474011050293139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40166373566982674033528759 60249560350474011050293139)
  ·
    refine ⟨90374340525711016575439709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60249560350474011050293139 90374340525711016575439709)
    ·
      refine ⟨33890377697141631215789891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90374340525711016575439709 33890377697141631215789891)
      ·
        refine ⟨50835566545712446823684837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33890377697141631215789891 50835566545712446823684837)
        ·
          refine ⟨9531668727321083779440907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50835566545712446823684837 9531668727321083779440907)
          ·
            refine ⟨14297503090981625669161361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9531668727321083779440907 14297503090981625669161361)
            ·
              refine ⟨10723127318236219251871021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14297503090981625669161361 10723127318236219251871021)
              ·
                refine ⟨4021172744338582219451633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10723127318236219251871021 4021172744338582219451633)
                ·
                  refine ⟨3015879558253936664588725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4021172744338582219451633 3015879558253936664588725)
                  ·
                    refine ⟨282738708586306562305193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3015879558253936664588725 282738708586306562305193)
                    ·
                      rfl

theorem cell23_1651895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 5].length) (baseStart_1651895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651895 prefixEnd_1651895 := by exact prefixLift 1651895
  have htrace : WordTrace (prefixWord ++ tailWord_1651895) baseStart_1651895 baseEnd_1651895 := by
    simpa [prefixWord, tailWord_1651895, baseEnd_1651895] using wordTrace_append hprefix tailTrace_1651895
  have hstable : (prefixWord ++ tailWord_1651895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651895).length < 2 ^ (prefixWord ++ tailWord_1651895).sum := by decide
  have hdescent : baseEnd_1651895 < baseStart_1651895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651935 : List Nat := [1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 3]
def baseStart_1651935 : Nat := 118140960795 + 1651935 * 2 ^ 59
def prefixEnd_1651935 : Nat := 4983230072969 + 3 ^ 40 * 1651935 * 2
def baseEnd_1651935 : Nat := 848236664985099530415395

theorem tailTrace_1651935 : CollatzResearch.WordTrace tailWord_1651935 prefixEnd_1651935 848236664985099530415395 := by
  unfold tailWord_1651935
  simp only [CollatzResearch.WordTrace]
  refine ⟨60251019270329097881749259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40167346180219398587832839 60251019270329097881749259)
  ·
    refine ⟨90376528905493646822623889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60251019270329097881749259 90376528905493646822623889)
    ·
      refine ⟨67782396679120235116967917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90376528905493646822623889 67782396679120235116967917)
      ·
        refine ⟨25418398754670088168862969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67782396679120235116967917 25418398754670088168862969)
        ·
          refine ⟨19063799066002566126647227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25418398754670088168862969 19063799066002566126647227)
          ·
            refine ⟨28595698599003849189970841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19063799066002566126647227 28595698599003849189970841)
            ·
              refine ⟨21446773949252886892478131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28595698599003849189970841 21446773949252886892478131)
              ·
                refine ⟨32170160923879330338717197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21446773949252886892478131 32170160923879330338717197)
                ·
                  refine ⟨12063810346454748877018949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32170160923879330338717197 12063810346454748877018949)
                  ·
                    refine ⟨2261964439960265414441053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12063810346454748877018949 2261964439960265414441053)
                    ·
                      refine ⟨848236664985099530415395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2261964439960265414441053 848236664985099530415395)
                      ·
                        rfl

theorem cell23_1651935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_1651935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651935 prefixEnd_1651935 := by exact prefixLift 1651935
  have htrace : WordTrace (prefixWord ++ tailWord_1651935) baseStart_1651935 baseEnd_1651935 := by
    simpa [prefixWord, tailWord_1651935, baseEnd_1651935] using wordTrace_append hprefix tailTrace_1651935
  have hstable : (prefixWord ++ tailWord_1651935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651935).length < 2 ^ (prefixWord ++ tailWord_1651935).sum := by decide
  have hdescent : baseEnd_1651935 < baseStart_1651935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651949 : List Nat := [1, 5, 1, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_1651949 : Nat := 118140960795 + 1651949 * 2 ^ 59
def prefixEnd_1651949 : Nat := 4983230072969 + 3 ^ 40 * 1651949 * 2
def baseEnd_1651949 : Nat := 848243853714262475640331

theorem tailTrace_1651949 : CollatzResearch.WordTrace tailWord_1651949 prefixEnd_1651949 848243853714262475640331 := by
  unfold tailWord_1651949
  simp only [CollatzResearch.WordTrace]
  refine ⟨60251529892278378272758901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40167686594852252181839267 60251529892278378272758901)
  ·
    refine ⟨5648580927401097963071147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60251529892278378272758901 5648580927401097963071147)
    ·
      refine ⟨8472871391101646944606721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5648580927401097963071147 8472871391101646944606721)
      ·
        refine ⟨6354653543326235208455041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8472871391101646944606721 6354653543326235208455041)
        ·
          refine ⟨4765990157494676406341281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6354653543326235208455041 4765990157494676406341281)
          ·
            refine ⟨3574492618121007304755961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4765990157494676406341281 3574492618121007304755961)
            ·
              refine ⟨2680869463590755478566971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3574492618121007304755961 2680869463590755478566971)
              ·
                refine ⟨4021304195386133217850457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2680869463590755478566971 4021304195386133217850457)
                ·
                  refine ⟨3015978146539599913387843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4021304195386133217850457 3015978146539599913387843)
                  ·
                    refine ⟨4523967219809399870081765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3015978146539599913387843 4523967219809399870081765)
                    ·
                      refine ⟨848243853714262475640331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4523967219809399870081765 848243853714262475640331)
                      ·
                        rfl

theorem cell23_1651949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_1651949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651949 prefixEnd_1651949 := by exact prefixLift 1651949
  have htrace : WordTrace (prefixWord ++ tailWord_1651949) baseStart_1651949 baseEnd_1651949 := by
    simpa [prefixWord, tailWord_1651949, baseEnd_1651949] using wordTrace_append hprefix tailTrace_1651949
  have hstable : (prefixWord ++ tailWord_1651949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651949).length < 2 ^ (prefixWord ++ tailWord_1651949).sum := by decide
  have hdescent : baseEnd_1651949 < baseStart_1651949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651972 : List Nat := [2, 3, 2, 2, 2, 1, 1, 4, 6]
def baseStart_1651972 : Nat := 118140960795 + 1651972 * 2 ^ 59
def prefixEnd_1651972 : Nat := 4983230072969 + 3 ^ 40 * 1651972 * 2
def baseEnd_1651972 : Nat := 94250629307701765072525

theorem tailTrace_1651972 : CollatzResearch.WordTrace tailWord_1651972 prefixEnd_1651972 94250629307701765072525 := by
  unfold tailWord_1651972
  simp only [CollatzResearch.WordTrace]
  refine ⟨30126184385597526600423085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40168245847463368800564113 30126184385597526600423085)
  ·
    refine ⟨11297319144599072475158657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30126184385597526600423085 11297319144599072475158657)
    ·
      refine ⟨8472989358449304356368993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11297319144599072475158657 8472989358449304356368993)
      ·
        refine ⟨6354742018836978267276745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8472989358449304356368993 6354742018836978267276745)
        ·
          refine ⟨4766056514127733700457559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6354742018836978267276745 4766056514127733700457559)
          ·
            refine ⟨7149084771191600550686339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4766056514127733700457559 7149084771191600550686339)
            ·
              refine ⟨10723627156787400826029509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7149084771191600550686339 10723627156787400826029509)
              ·
                refine ⟨2010680091897637654880533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10723627156787400826029509 2010680091897637654880533)
                ·
                  refine ⟨94250629307701765072525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2010680091897637654880533 94250629307701765072525)
                  ·
                    rfl

theorem cell23_1651972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 6].length) (baseStart_1651972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651972 prefixEnd_1651972 := by exact prefixLift 1651972
  have htrace : WordTrace (prefixWord ++ tailWord_1651972) baseStart_1651972 baseEnd_1651972 := by
    simpa [prefixWord, tailWord_1651972, baseEnd_1651972] using wordTrace_append hprefix tailTrace_1651972
  have hstable : (prefixWord ++ tailWord_1651972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651972).length < 2 ^ (prefixWord ++ tailWord_1651972).sum := by decide
  have hdescent : baseEnd_1651972 < baseStart_1651972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651976 : List Nat := [2, 1, 3, 2, 4, 1, 1, 4, 1, 4]
def baseStart_1651976 : Nat := 118140960795 + 1651976 * 2 ^ 59
def prefixEnd_1651976 : Nat := 4983230072969 + 3 ^ 40 * 1651976 * 2
def baseEnd_1651976 : Nat := 282752572563977956667569

theorem tailTrace_1651976 : CollatzResearch.WordTrace tailWord_1651976 prefixEnd_1651976 282752572563977956667569 := by
  unfold tailWord_1651976
  simp only [CollatzResearch.WordTrace]
  refine ⟨30126257331590280941995891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40168343108787041255994521 30126257331590280941995891)
  ·
    refine ⟨45189385997385421412993837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30126257331590280941995891 45189385997385421412993837)
    ·
      refine ⟨16946019749019533029872689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45189385997385421412993837 16946019749019533029872689)
      ·
        refine ⟨12709514811764649772404517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16946019749019533029872689 12709514811764649772404517)
        ·
          refine ⟨2383034027205871832325847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12709514811764649772404517 2383034027205871832325847)
          ·
            refine ⟨3574551040808807748488771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2383034027205871832325847 3574551040808807748488771)
            ·
              refine ⟨5361826561213211622733157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3574551040808807748488771 5361826561213211622733157)
              ·
                refine ⟨1005342480227477179262467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5361826561213211622733157 1005342480227477179262467)
                ·
                  refine ⟨1508013720341215768893701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005342480227477179262467 1508013720341215768893701)
                  ·
                    refine ⟨282752572563977956667569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1508013720341215768893701 282752572563977956667569)
                    ·
                      rfl

theorem cell23_1651976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 4, 1, 4].length) (baseStart_1651976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651976 prefixEnd_1651976 := by exact prefixLift 1651976
  have htrace : WordTrace (prefixWord ++ tailWord_1651976) baseStart_1651976 baseEnd_1651976 := by
    simpa [prefixWord, tailWord_1651976, baseEnd_1651976] using wordTrace_append hprefix tailTrace_1651976
  have hstable : (prefixWord ++ tailWord_1651976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651976).length < 2 ^ (prefixWord ++ tailWord_1651976).sum := by decide
  have hdescent : baseEnd_1651976 < baseStart_1651976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1651985 : List Nat := [1, 2, 2, 1, 1, 4, 1, 1, 5, 5]
def baseStart_1651985 : Nat := 118140960795 + 1651985 * 2 ^ 59
def prefixEnd_1651985 : Nat := 4983230072969 + 3 ^ 40 * 1651985 * 2
def baseEnd_1651985 : Nat := 282754113005941444930055

theorem tailTrace_1651985 : CollatzResearch.WordTrace tailWord_1651985 prefixEnd_1651985 282754113005941444930055 := by
  unfold tailWord_1651985
  simp only [CollatzResearch.WordTrace]
  refine ⟨60252842920147956421069409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40168561946765304280712939 60252842920147956421069409)
  ·
    refine ⟨45189632190110967315802057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60252842920147956421069409 45189632190110967315802057)
    ·
      refine ⟨33892224142583225486851543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45189632190110967315802057 33892224142583225486851543)
      ·
        refine ⟨50838336213874838230277315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33892224142583225486851543 50838336213874838230277315)
        ·
          refine ⟨76257504320812257345415973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50838336213874838230277315 76257504320812257345415973)
          ·
            refine ⟨14298282060152298252265495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76257504320812257345415973 14298282060152298252265495)
            ·
              refine ⟨21447423090228447378398243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14298282060152298252265495 21447423090228447378398243)
              ·
                refine ⟨32171134635342671067597365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21447423090228447378398243 32171134635342671067597365)
                ·
                  refine ⟨3016043872063375412587253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32171134635342671067597365 3016043872063375412587253)
                  ·
                    refine ⟨282754113005941444930055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3016043872063375412587253 282754113005941444930055)
                    ·
                      rfl

theorem cell23_1651985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_1651985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1651985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1651985 prefixEnd_1651985 := by exact prefixLift 1651985
  have htrace : WordTrace (prefixWord ++ tailWord_1651985) baseStart_1651985 baseEnd_1651985 := by
    simpa [prefixWord, tailWord_1651985, baseEnd_1651985] using wordTrace_append hprefix tailTrace_1651985
  have hstable : (prefixWord ++ tailWord_1651985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1651985).length < 2 ^ (prefixWord ++ tailWord_1651985).sum := by decide
  have hdescent : baseEnd_1651985 < baseStart_1651985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1651985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652016 : List Nat := [2, 1, 1, 1, 2, 2, 6, 3, 1, 1, 3]
def baseStart_1652016 : Nat := 118140960795 + 1652016 * 2 ^ 59
def prefixEnd_1652016 : Nat := 4983230072969 + 3 ^ 40 * 1652016 * 2
def baseEnd_1652016 : Nat := 848278256918113713502523

theorem tailTrace_1652016 : CollatzResearch.WordTrace tailWord_1652016 prefixEnd_1652016 848278256918113713502523 := by
  unfold tailWord_1652016
  simp only [CollatzResearch.WordTrace]
  refine ⟨30126986791517824357723951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40169315722023765810298601 30126986791517824357723951)
  ·
    refine ⟨45190480187276736536585927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30126986791517824357723951 45190480187276736536585927)
    ·
      refine ⟨67785720280915104804878891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45190480187276736536585927 67785720280915104804878891)
      ·
        refine ⟨101678580421372657207318337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67785720280915104804878891 101678580421372657207318337)
        ·
          refine ⟨76258935316029492905488753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101678580421372657207318337 76258935316029492905488753)
          ·
            refine ⟨57194201487022119679116565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76258935316029492905488753 57194201487022119679116565)
            ·
              refine ⟨2680978194704161859958589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57194201487022119679116565 2680978194704161859958589)
              ·
                refine ⟨1005366823014060697484471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2680978194704161859958589 1005366823014060697484471)
                ·
                  refine ⟨1508050234521091046226707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005366823014060697484471 1508050234521091046226707)
                  ·
                    refine ⟨2262075351781636569340061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1508050234521091046226707 2262075351781636569340061)
                    ·
                      refine ⟨848278256918113713502523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2262075351781636569340061 848278256918113713502523)
                      ·
                        rfl

theorem cell23_1652016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 1, 1, 3].length) (baseStart_1652016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652016 prefixEnd_1652016 := by exact prefixLift 1652016
  have htrace : WordTrace (prefixWord ++ tailWord_1652016) baseStart_1652016 baseEnd_1652016 := by
    simpa [prefixWord, tailWord_1652016, baseEnd_1652016] using wordTrace_append hprefix tailTrace_1652016
  have hstable : (prefixWord ++ tailWord_1652016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652016).length < 2 ^ (prefixWord ++ tailWord_1652016).sum := by decide
  have hdescent : baseEnd_1652016 < baseStart_1652016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652019 : List Nat := [1, 1, 1, 2, 5, 2, 4, 1, 1, 5]
def baseStart_1652019 : Nat := 118140960795 + 1652019 * 2 ^ 59
def prefixEnd_1652019 : Nat := 4983230072969 + 3 ^ 40 * 1652019 * 2
def baseEnd_1652019 : Nat := 282759932453359067255003

theorem tailTrace_1652019 : CollatzResearch.WordTrace tailWord_1652019 prefixEnd_1652019 282759932453359067255003 := by
  unfold tailWord_1652019
  simp only [CollatzResearch.WordTrace]
  refine ⟨60254083002024780227807111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40169388668016520151871407 60254083002024780227807111)
  ·
    refine ⟨90381124503037170341710667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60254083002024780227807111 90381124503037170341710667)
    ·
      refine ⟨135571686754555755512566001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90381124503037170341710667 135571686754555755512566001)
      ·
        refine ⟨101678765065916816634424501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135571686754555755512566001 101678765065916816634424501)
        ·
          refine ⟨9532384224929701559477297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101678765065916816634424501 9532384224929701559477297)
          ·
            refine ⟨7149288168697276169607973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9532384224929701559477297 7149288168697276169607973)
            ·
              refine ⟨1340491531630739281801495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7149288168697276169607973 1340491531630739281801495)
              ·
                refine ⟨2010737297446108922702243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340491531630739281801495 2010737297446108922702243)
                ·
                  refine ⟨3016105946169163384053365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010737297446108922702243 3016105946169163384053365)
                  ·
                    refine ⟨282759932453359067255003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3016105946169163384053365 282759932453359067255003)
                    ·
                      rfl

theorem cell23_1652019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 4, 1, 1, 5].length) (baseStart_1652019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652019 prefixEnd_1652019 := by exact prefixLift 1652019
  have htrace : WordTrace (prefixWord ++ tailWord_1652019) baseStart_1652019 baseEnd_1652019 := by
    simpa [prefixWord, tailWord_1652019, baseEnd_1652019] using wordTrace_append hprefix tailTrace_1652019
  have hstable : (prefixWord ++ tailWord_1652019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652019).length < 2 ^ (prefixWord ++ tailWord_1652019).sum := by decide
  have hdescent : baseEnd_1652019 < baseStart_1652019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652032 : List Nat := [2, 1, 1, 2, 2, 1, 5, 1, 4, 4]
def baseStart_1652032 : Nat := 118140960795 + 1652032 * 2 ^ 59
def prefixEnd_1652032 : Nat := 4983230072969 + 3 ^ 40 * 1652032 * 2
def baseEnd_1652032 : Nat := 282762157536195216967483

theorem tailTrace_1652032 : CollatzResearch.WordTrace tailWord_1652032 prefixEnd_1652032 282762157536195216967483 := by
  unfold tailWord_1652032
  simp only [CollatzResearch.WordTrace]
  refine ⟨30127278575488841724015175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40169704767318455632020233 30127278575488841724015175)
  ·
    refine ⟨45190917863233262586022763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30127278575488841724015175 45190917863233262586022763)
    ·
      refine ⟨67786376794849893879034145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45190917863233262586022763 67786376794849893879034145)
      ·
        refine ⟨50839782596137420409275609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67786376794849893879034145 50839782596137420409275609)
        ·
          refine ⟨38129836947103065306956707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50839782596137420409275609 38129836947103065306956707)
          ·
            refine ⟨57194755420654597960435061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38129836947103065306956707 57194755420654597960435061)
            ·
              refine ⟨5362008320686368558790787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57194755420654597960435061 5362008320686368558790787)
              ·
                refine ⟨8043012481029552838186181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5362008320686368558790787 8043012481029552838186181)
                ·
                  refine ⟨1508064840193041157159909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8043012481029552838186181 1508064840193041157159909)
                  ·
                    refine ⟨282762157536195216967483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1508064840193041157159909 282762157536195216967483)
                    ·
                      rfl

theorem cell23_1652032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 1, 4, 4].length) (baseStart_1652032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652032 prefixEnd_1652032 := by exact prefixLift 1652032
  have htrace : WordTrace (prefixWord ++ tailWord_1652032) baseStart_1652032 baseEnd_1652032 := by
    simpa [prefixWord, tailWord_1652032, baseEnd_1652032] using wordTrace_append hprefix tailTrace_1652032
  have hstable : (prefixWord ++ tailWord_1652032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652032).length < 2 ^ (prefixWord ++ tailWord_1652032).sum := by decide
  have hdescent : baseEnd_1652032 < baseStart_1652032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652033 : List Nat := [1, 2, 5, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_1652033 : Nat := 118140960795 + 1652033 * 2 ^ 59
def prefixEnd_1652033 : Nat := 4983230072969 + 3 ^ 40 * 1652033 * 2
def baseEnd_1652033 : Nat := 848286986089240146989945

theorem tailTrace_1652033 : CollatzResearch.WordTrace tailWord_1652033 prefixEnd_1652033 848286986089240146989945 := by
  unfold tailWord_1652033
  simp only [CollatzResearch.WordTrace]
  refine ⟨60254593623974060618816753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40169729082649373745877835 60254593623974060618816753)
  ·
    refine ⟨45190945217980545464112565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60254593623974060618816753 45190945217980545464112565)
    ·
      refine ⟨4236651114185676137260553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45190945217980545464112565 4236651114185676137260553)
      ·
        refine ⟨3177488335639257102945415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4236651114185676137260553 3177488335639257102945415)
        ·
          refine ⟨4766232503458885654418123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3177488335639257102945415 4766232503458885654418123)
          ·
            refine ⟨7149348755188328481627185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4766232503458885654418123 7149348755188328481627185)
            ·
              refine ⟨5362011566391246361220389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7149348755188328481627185 5362011566391246361220389)
              ·
                refine ⟨1005377168698358692728823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5362011566391246361220389 1005377168698358692728823)
                ·
                  refine ⟨1508065753047538039093235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005377168698358692728823 1508065753047538039093235)
                  ·
                    refine ⟨2262098629571307058639853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1508065753047538039093235 2262098629571307058639853)
                    ·
                      refine ⟨848286986089240146989945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2262098629571307058639853 848286986089240146989945)
                      ·
                        rfl

theorem cell23_1652033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_1652033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652033 prefixEnd_1652033 := by exact prefixLift 1652033
  have htrace : WordTrace (prefixWord ++ tailWord_1652033) baseStart_1652033 baseEnd_1652033 := by
    simpa [prefixWord, tailWord_1652033, baseEnd_1652033] using wordTrace_append hprefix tailTrace_1652033
  have hstable : (prefixWord ++ tailWord_1652033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652033).length < 2 ^ (prefixWord ++ tailWord_1652033).sum := by decide
  have hdescent : baseEnd_1652033 < baseStart_1652033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652035 : List Nat := [1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 6]
def baseStart_1652035 : Nat := 118140960795 + 1652035 * 2 ^ 59
def prefixEnd_1652035 : Nat := 4983230072969 + 3 ^ 40 * 1652035 * 2
def baseEnd_1652035 : Nat := 848288013050549139164935

theorem tailTrace_1652035 : CollatzResearch.WordTrace tailWord_1652035 prefixEnd_1652035 848288013050549139164935 := by
  unfold tailWord_1652035
  simp only [CollatzResearch.WordTrace]
  refine ⟨60254666569966814960389559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40169777713311209973593039 60254666569966814960389559)
  ·
    refine ⟨90381999854950222440584339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60254666569966814960389559 90381999854950222440584339)
    ·
      refine ⟨135572999782425333660876509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90381999854950222440584339 135572999782425333660876509)
      ·
        refine ⟨50839874918409500122828691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135572999782425333660876509 50839874918409500122828691)
        ·
          refine ⟨76259812377614250184243037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50839874918409500122828691 76259812377614250184243037)
          ·
            refine ⟨28597429641605343819091139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76259812377614250184243037 28597429641605343819091139)
            ·
              refine ⟨42896144462408015728636709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28597429641605343819091139 42896144462408015728636709)
              ·
                refine ⟨8043027086701502949119383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42896144462408015728636709 8043027086701502949119383)
                ·
                  refine ⟨12064540630052254423679075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8043027086701502949119383 12064540630052254423679075)
                  ·
                    refine ⟨18096810945078381635518613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12064540630052254423679075 18096810945078381635518613)
                    ·
                      refine ⟨848288013050549139164935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18096810945078381635518613 848288013050549139164935)
                      ·
                        rfl

theorem cell23_1652035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 6].length) (baseStart_1652035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652035 prefixEnd_1652035 := by exact prefixLift 1652035
  have htrace : WordTrace (prefixWord ++ tailWord_1652035) baseStart_1652035 baseEnd_1652035 := by
    simpa [prefixWord, tailWord_1652035, baseEnd_1652035] using wordTrace_append hprefix tailTrace_1652035
  have hstable : (prefixWord ++ tailWord_1652035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652035).length < 2 ^ (prefixWord ++ tailWord_1652035).sum := by decide
  have hdescent : baseEnd_1652035 < baseStart_1652035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652042 : List Nat := [3, 1, 2, 1, 1, 1, 1, 3, 5, 2, 3]
def baseStart_1652042 : Nat := 118140960795 + 1652042 * 2 ^ 59
def prefixEnd_1652042 : Nat := 4983230072969 + 3 ^ 40 * 1652042 * 2
def baseEnd_1652042 : Nat := 848291607415130611777403

theorem tailTrace_1652042 : CollatzResearch.WordTrace tailWord_1652042 prefixEnd_1652042 848291607415130611777403 := by
  unfold tailWord_1652042
  simp only [CollatzResearch.WordTrace]
  refine ⟨15063730470235363788973595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40169947920627636770596253 15063730470235363788973595)
  ·
    refine ⟨22595595705353045683460393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15063730470235363788973595 22595595705353045683460393)
    ·
      refine ⟨16946696779014784262595295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22595595705353045683460393 16946696779014784262595295)
      ·
        refine ⟨25420045168522176393892943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16946696779014784262595295 25420045168522176393892943)
        ·
          refine ⟨38130067752783264590839415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25420045168522176393892943 38130067752783264590839415)
          ·
            refine ⟨57195101629174896886259123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38130067752783264590839415 57195101629174896886259123)
            ·
              refine ⟨85792652443762345329388685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57195101629174896886259123 85792652443762345329388685)
              ·
                refine ⟨32172244666410879498520757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85792652443762345329388685 32172244666410879498520757)
                ·
                  refine ⟨3016147937476019952986321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32172244666410879498520757 3016147937476019952986321)
                  ·
                    refine ⟨2262110953107014964739741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3016147937476019952986321 2262110953107014964739741)
                    ·
                      refine ⟨848291607415130611777403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2262110953107014964739741 848291607415130611777403)
                      ·
                        rfl

theorem cell23_1652042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 5, 2, 3].length) (baseStart_1652042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652042 prefixEnd_1652042 := by exact prefixLift 1652042
  have htrace : WordTrace (prefixWord ++ tailWord_1652042) baseStart_1652042 baseEnd_1652042 := by
    simpa [prefixWord, tailWord_1652042, baseEnd_1652042] using wordTrace_append hprefix tailTrace_1652042
  have hstable : (prefixWord ++ tailWord_1652042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652042).length < 2 ^ (prefixWord ++ tailWord_1652042).sum := by decide
  have hdescent : baseEnd_1652042 < baseStart_1652042 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652052 : List Nat := [2, 4, 1, 1, 2, 1, 3, 1, 1, 1, 6]
def baseStart_1652052 : Nat := 118140960795 + 1652052 * 2 ^ 59
def prefixEnd_1652052 : Nat := 4983230072969 + 3 ^ 40 * 1652052 * 2
def baseEnd_1652052 : Nat := 848296742221675572652357

theorem tailTrace_1652052 : CollatzResearch.WordTrace tailWord_1652052 prefixEnd_1652052 848296742221675572652357 := by
  unfold tailWord_1652052
  simp only [CollatzResearch.WordTrace]
  refine ⟨30127643305452613431879205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40170191073936817909172273 30127643305452613431879205)
  ·
    refine ⟨5648933119772365018477351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30127643305452613431879205 5648933119772365018477351)
    ·
      refine ⟨8473399679658547527716027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5648933119772365018477351 8473399679658547527716027)
      ·
        refine ⟨12710099519487821291574041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8473399679658547527716027 12710099519487821291574041)
        ·
          refine ⟨9532574639615865968680531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12710099519487821291574041 9532574639615865968680531)
          ·
            refine ⟨14298861959423798953020797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9532574639615865968680531 14298861959423798953020797)
            ·
              refine ⟨5362073234783924607382799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14298861959423798953020797 5362073234783924607382799)
              ·
                refine ⟨8043109852175886911074199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5362073234783924607382799 8043109852175886911074199)
                ·
                  refine ⟨12064664778263830366611299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8043109852175886911074199 12064664778263830366611299)
                  ·
                    refine ⟨18096997167395745549916949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12064664778263830366611299 18096997167395745549916949)
                    ·
                      refine ⟨848296742221675572652357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18096997167395745549916949 848296742221675572652357)
                      ·
                        rfl

theorem cell23_1652052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_1652052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652052 prefixEnd_1652052 := by exact prefixLift 1652052
  have htrace : WordTrace (prefixWord ++ tailWord_1652052) baseStart_1652052 baseEnd_1652052 := by
    simpa [prefixWord, tailWord_1652052, baseEnd_1652052] using wordTrace_append hprefix tailTrace_1652052
  have hstable : (prefixWord ++ tailWord_1652052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652052).length < 2 ^ (prefixWord ++ tailWord_1652052).sum := by decide
  have hdescent : baseEnd_1652052 < baseStart_1652052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652065 : List Nat := [1, 2, 3, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_1652065 : Nat := 118140960795 + 1652065 * 2 ^ 59
def prefixEnd_1652065 : Nat := 4983230072969 + 3 ^ 40 * 1652065 * 2
def baseEnd_1652065 : Nat := 848303417470184021789797

theorem tailTrace_1652065 : CollatzResearch.WordTrace tailWord_1652065 prefixEnd_1652065 848303417470184021789797 := by
  unfold tailWord_1652065
  simp only [CollatzResearch.WordTrace]
  refine ⟨60255760759858130083981649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40170507173238753389321099 60255760759858130083981649)
  ·
    refine ⟨45191820569893597562986237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60255760759858130083981649 45191820569893597562986237)
    ·
      refine ⟨16946932713710099086119839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45191820569893597562986237 16946932713710099086119839)
      ·
        refine ⟨25420399070565148629179759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16946932713710099086119839 25420399070565148629179759)
        ·
          refine ⟨38130598605847722943769639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25420399070565148629179759 38130598605847722943769639)
          ·
            refine ⟨57195897908771584415654459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38130598605847722943769639 57195897908771584415654459)
            ·
              refine ⟨85793846863157376623481689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57195897908771584415654459 85793846863157376623481689)
              ·
                refine ⟨64345385147368032467611267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85793846863157376623481689 64345385147368032467611267)
                ·
                  refine ⟨96518077721052048701416901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64345385147368032467611267 96518077721052048701416901)
                  ·
                    refine ⟨18097139572697259131515669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96518077721052048701416901 18097139572697259131515669)
                    ·
                      refine ⟨848303417470184021789797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18097139572697259131515669 848303417470184021789797)
                      ·
                        rfl

theorem cell23_1652065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_1652065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652065 prefixEnd_1652065 := by exact prefixLift 1652065
  have htrace : WordTrace (prefixWord ++ tailWord_1652065) baseStart_1652065 baseEnd_1652065 := by
    simpa [prefixWord, tailWord_1652065, baseEnd_1652065] using wordTrace_append hprefix tailTrace_1652065
  have hstable : (prefixWord ++ tailWord_1652065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652065).length < 2 ^ (prefixWord ++ tailWord_1652065).sum := by decide
  have hdescent : baseEnd_1652065 < baseStart_1652065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652089 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 4, 1, 3]
def baseStart_1652089 : Nat := 118140960795 + 1652089 * 2 ^ 59
def prefixEnd_1652089 : Nat := 4983230072969 + 3 ^ 40 * 1652089 * 2
def baseEnd_1652089 : Nat := 848315741005891927889687

theorem tailTrace_1652089 : CollatzResearch.WordTrace tailWord_1652089 prefixEnd_1652089 848315741005891927889687 := by
  unfold tailWord_1652089
  simp only [CollatzResearch.WordTrace]
  refine ⟨60256636111771182182855321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40171090741180788121903547 60256636111771182182855321)
  ·
    refine ⟨45192477083828386637141491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60256636111771182182855321 45192477083828386637141491)
    ·
      refine ⟨67788715625742579955712237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45192477083828386637141491 67788715625742579955712237)
      ·
        refine ⟨25420768359653467483392089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67788715625742579955712237 25420768359653467483392089)
        ·
          refine ⟨19065576269740100612544067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25420768359653467483392089 19065576269740100612544067)
          ·
            refine ⟨28598364404610150918816101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19065576269740100612544067 28598364404610150918816101)
            ·
              refine ⟨5362193325864403297278019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28598364404610150918816101 5362193325864403297278019)
              ·
                refine ⟨8043289988796604945917029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5362193325864403297278019 8043289988796604945917029)
                ·
                  refine ⟨1508116872899363427359443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8043289988796604945917029 1508116872899363427359443)
                  ·
                    refine ⟨2262175309349045141039165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1508116872899363427359443 2262175309349045141039165)
                    ·
                      refine ⟨848315741005891927889687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2262175309349045141039165 848315741005891927889687)
                      ·
                        rfl

theorem cell23_1652089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_1652089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652089 prefixEnd_1652089 := by exact prefixLift 1652089
  have htrace : WordTrace (prefixWord ++ tailWord_1652089) baseStart_1652089 baseEnd_1652089 := by
    simpa [prefixWord, tailWord_1652089, baseEnd_1652089] using wordTrace_append hprefix tailTrace_1652089
  have hstable : (prefixWord ++ tailWord_1652089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652089).length < 2 ^ (prefixWord ++ tailWord_1652089).sum := by decide
  have hdescent : baseEnd_1652089 < baseStart_1652089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652110 : List Nat := [4, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3]
def baseStart_1652110 : Nat := 118140960795 + 1652110 * 2 ^ 59
def prefixEnd_1652110 : Nat := 4983230072969 + 3 ^ 40 * 1652110 * 2
def baseEnd_1652110 : Nat := 848326524099636345727091

theorem tailTrace_1652110 : CollatzResearch.WordTrace tailWord_1652110 prefixEnd_1652110 848326524099636345727091 := by
  unfold tailWord_1652110
  simp only [CollatzResearch.WordTrace]
  refine ⟨7532175255586887846171223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40171601363130068512913189 7532175255586887846171223)
  ·
    refine ⟨11298262883380331769256835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7532175255586887846171223 11298262883380331769256835)
    ·
      refine ⟨16947394325070497653885253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11298262883380331769256835 16947394325070497653885253)
      ·
        refine ⟨3177636435950718310103485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16947394325070497653885253 3177636435950718310103485)
        ·
          refine ⟨1191613663481519366288807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3177636435950718310103485 1191613663481519366288807)
          ·
            refine ⟨1787420495222279049433211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191613663481519366288807 1787420495222279049433211)
            ·
              refine ⟨2681130742833418574149817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1787420495222279049433211 2681130742833418574149817)
              ·
                refine ⟨2010848057125063930612363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2681130742833418574149817 2010848057125063930612363)
                ·
                  refine ⟨3016272085687595895918545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2010848057125063930612363 3016272085687595895918545)
                  ·
                    refine ⟨2262204064265696921938909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3016272085687595895918545 2262204064265696921938909)
                    ·
                      refine ⟨848326524099636345727091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2262204064265696921938909 848326524099636345727091)
                      ·
                        rfl

theorem cell23_1652110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_1652110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652110 prefixEnd_1652110 := by exact prefixLift 1652110
  have htrace : WordTrace (prefixWord ++ tailWord_1652110) baseStart_1652110 baseEnd_1652110 := by
    simpa [prefixWord, tailWord_1652110, baseEnd_1652110] using wordTrace_append hprefix tailTrace_1652110
  have hstable : (prefixWord ++ tailWord_1652110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652110).length < 2 ^ (prefixWord ++ tailWord_1652110).sum := by decide
  have hdescent : baseEnd_1652110 < baseStart_1652110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652115 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 9]
def baseStart_1652115 : Nat := 118140960795 + 1652115 * 2 ^ 59
def prefixEnd_1652115 : Nat := 4983230072969 + 3 ^ 40 * 1652115 * 2
def baseEnd_1652115 : Nat := 848329091502908826164567

theorem tailTrace_1652115 : CollatzResearch.WordTrace tailWord_1652115 prefixEnd_1652115 848329091502908826164567 := by
  unfold tailWord_1652115
  simp only [CollatzResearch.WordTrace]
  refine ⟨60257584409676988623301799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40171722939784659082201199 60257584409676988623301799)
  ·
    refine ⟨90386376614515482934952699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60257584409676988623301799 90386376614515482934952699)
    ·
      refine ⟨135579564921773224402429049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90386376614515482934952699 135579564921773224402429049)
      ·
        refine ⟨101684673691329918301821787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135579564921773224402429049 101684673691329918301821787)
        ·
          refine ⟨152527010536994877452732681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101684673691329918301821787 152527010536994877452732681)
          ·
            refine ⟨114395257902746158089549511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152527010536994877452732681 114395257902746158089549511)
            ·
              refine ⟨171592886854119237134324267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114395257902746158089549511 171592886854119237134324267)
              ·
                refine ⟨257389330281178855701486401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171592886854119237134324267 257389330281178855701486401)
                ·
                  refine ⟨193041997710884141776114801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257389330281178855701486401 193041997710884141776114801)
                  ·
                    refine ⟨144781498283163106332086101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 193041997710884141776114801 144781498283163106332086101)
                    ·
                      refine ⟨848329091502908826164567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 144781498283163106332086101 848329091502908826164567)
                      ·
                        rfl

theorem cell23_1652115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 9].length) (baseStart_1652115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652115 prefixEnd_1652115 := by exact prefixLift 1652115
  have htrace : WordTrace (prefixWord ++ tailWord_1652115) baseStart_1652115 baseEnd_1652115 := by
    simpa [prefixWord, tailWord_1652115, baseEnd_1652115] using wordTrace_append hprefix tailTrace_1652115
  have hstable : (prefixWord ++ tailWord_1652115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652115).length < 2 ^ (prefixWord ++ tailWord_1652115).sum := by decide
  have hdescent : baseEnd_1652115 < baseStart_1652115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652149 : List Nat := [1, 3, 3, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_1652149 : Nat := 118140960795 + 1652149 * 2 ^ 59
def prefixEnd_1652149 : Nat := 4983230072969 + 3 ^ 40 * 1652149 * 2
def baseEnd_1652149 : Nat := 848346549845161693139411

theorem tailTrace_1652149 : CollatzResearch.WordTrace tailWord_1652149 prefixEnd_1652149 848346549845161693139411 := by
  unfold tailWord_1652149
  simp only [CollatzResearch.WordTrace]
  refine ⟨60258824491553812430039501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40172549661035874953359667 60258824491553812430039501)
  ·
    refine ⟨22597059184332679661264813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60258824491553812430039501 22597059184332679661264813)
    ·
      refine ⟨8473897194124754872974305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22597059184332679661264813 8473897194124754872974305)
      ·
        refine ⟨6355422895593566154730729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8473897194124754872974305 6355422895593566154730729)
        ·
          refine ⟨4766567171695174616048047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6355422895593566154730729 4766567171695174616048047)
          ·
            refine ⟨7149850757542761924072071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4766567171695174616048047 7149850757542761924072071)
            ·
              refine ⟨10724776136314142886108107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7149850757542761924072071 10724776136314142886108107)
              ·
                refine ⟨16087164204471214329162161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10724776136314142886108107 16087164204471214329162161)
                ·
                  refine ⟨12065373153353410746871621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16087164204471214329162161 12065373153353410746871621)
                  ·
                    refine ⟨2262257466253764515038429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12065373153353410746871621 2262257466253764515038429)
                    ·
                      refine ⟨848346549845161693139411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2262257466253764515038429 848346549845161693139411)
                      ·
                        rfl

theorem cell23_1652149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_1652149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652149 prefixEnd_1652149 := by exact prefixLift 1652149
  have htrace : WordTrace (prefixWord ++ tailWord_1652149) baseStart_1652149 baseEnd_1652149 := by
    simpa [prefixWord, tailWord_1652149, baseEnd_1652149] using wordTrace_append hprefix tailTrace_1652149
  have hstable : (prefixWord ++ tailWord_1652149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652149).length < 2 ^ (prefixWord ++ tailWord_1652149).sum := by decide
  have hdescent : baseEnd_1652149 < baseStart_1652149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652186 : List Nat := [3, 1, 1, 2, 3, 3, 2, 3, 5]
def baseStart_1652186 : Nat := 118140960795 + 1652186 * 2 ^ 59
def prefixEnd_1652186 : Nat := 4983230072969 + 3 ^ 40 * 1652186 * 2
def baseEnd_1652186 : Nat := 94262838736597560930749

theorem tailTrace_1652186 : CollatzResearch.WordTrace tailWord_1652186 prefixEnd_1652186 94262838736597560930749 := by
  unfold tailWord_1652186
  simp only [CollatzResearch.WordTrace]
  refine ⟨15065043498104941937284103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40173449328279845166090941 15065043498104941937284103)
  ·
    refine ⟨22597565247157412905926155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15065043498104941937284103 22597565247157412905926155)
    ·
      refine ⟨33896347870736119358889233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22597565247157412905926155 33896347870736119358889233)
      ·
        refine ⟨25422260903052089519166925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33896347870736119358889233 25422260903052089519166925)
        ·
          refine ⟨9533347838644533569687597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25422260903052089519166925 9533347838644533569687597)
          ·
            refine ⟨3575005439491700088632849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9533347838644533569687597 3575005439491700088632849)
            ·
              refine ⟨2681254079618775066474637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3575005439491700088632849 2681254079618775066474637)
              ·
                refine ⟨1005470279857040649927989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2681254079618775066474637 1005470279857040649927989)
                ·
                  refine ⟨94262838736597560930749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1005470279857040649927989 94262838736597560930749)
                  ·
                    rfl

theorem cell23_1652186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 5].length) (baseStart_1652186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652186 prefixEnd_1652186 := by exact prefixLift 1652186
  have htrace : WordTrace (prefixWord ++ tailWord_1652186) baseStart_1652186 baseEnd_1652186 := by
    simpa [prefixWord, tailWord_1652186, baseEnd_1652186] using wordTrace_append hprefix tailTrace_1652186
  have hstable : (prefixWord ++ tailWord_1652186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652186).length < 2 ^ (prefixWord ++ tailWord_1652186).sum := by decide
  have hdescent : baseEnd_1652186 < baseStart_1652186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652192 : List Nat := [2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 5]
def baseStart_1652192 : Nat := 118140960795 + 1652192 * 2 ^ 59
def prefixEnd_1652192 : Nat := 4983230072969 + 3 ^ 40 * 1652192 * 2
def baseEnd_1652192 : Nat := 848368629513305024901713

theorem tailTrace_1652192 : CollatzResearch.WordTrace tailWord_1652192 prefixEnd_1652192 848368629513305024901713 := by
  unfold tailWord_1652192
  simp only [CollatzResearch.WordTrace]
  refine ⟨30130196415199015386927415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40173595220265353849236553 30130196415199015386927415)
  ·
    refine ⟨45195294622798523080391123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30130196415199015386927415 45195294622798523080391123)
    ·
      refine ⟨67792941934197784620586685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45195294622798523080391123 67792941934197784620586685)
      ·
        refine ⟨25422353225324169232720007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67792941934197784620586685 25422353225324169232720007)
        ·
          refine ⟨38133529837986253849080011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25422353225324169232720007 38133529837986253849080011)
          ·
            refine ⟨57200294756979380773620017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38133529837986253849080011 57200294756979380773620017)
            ·
              refine ⟨42900221067734535580215013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57200294756979380773620017 42900221067734535580215013)
              ·
                refine ⟨8043791450200225421290315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42900221067734535580215013 8043791450200225421290315)
                ·
                  refine ⟨12065687175300338131935473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8043791450200225421290315 12065687175300338131935473)
                  ·
                    refine ⟨9049265381475253598951605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12065687175300338131935473 9049265381475253598951605)
                    ·
                      refine ⟨848368629513305024901713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9049265381475253598951605 848368629513305024901713)
                      ·
                        rfl

theorem cell23_1652192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_1652192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652192 prefixEnd_1652192 := by exact prefixLift 1652192
  have htrace : WordTrace (prefixWord ++ tailWord_1652192) baseStart_1652192 baseEnd_1652192 := by
    simpa [prefixWord, tailWord_1652192, baseEnd_1652192] using wordTrace_append hprefix tailTrace_1652192
  have hstable : (prefixWord ++ tailWord_1652192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652192).length < 2 ^ (prefixWord ++ tailWord_1652192).sum := by decide
  have hdescent : baseEnd_1652192 < baseStart_1652192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652237 : List Nat := [1, 7, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1652237 : Nat := 118140960795 + 1652237 * 2 ^ 59
def prefixEnd_1652237 : Nat := 4983230072969 + 3 ^ 40 * 1652237 * 2
def baseEnd_1652237 : Nat := 94265748460306372093223

theorem tailTrace_1652237 : CollatzResearch.WordTrace tailWord_1652237 prefixEnd_1652237 94265748460306372093223 := by
  unfold tailWord_1652237
  simp only [CollatzResearch.WordTrace]
  refine ⟨60262034115235003459242965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40174689410156668972828643 60262034115235003459242965)
  ·
    refine ⟨1412391424575820393576007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 60262034115235003459242965 1412391424575820393576007)
    ·
      refine ⟨2118587136863730590364011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1412391424575820393576007 2118587136863730590364011)
      ·
        refine ⟨3177880705295595885546017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2118587136863730590364011 3177880705295595885546017)
        ·
          refine ⟨2383410528971696914159513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3177880705295595885546017 2383410528971696914159513)
          ·
            refine ⟨1787557896728772685619635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2383410528971696914159513 1787557896728772685619635)
            ·
              refine ⟨2681336845093159028429453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1787557896728772685619635 2681336845093159028429453)
              ·
                refine ⟨1005501316909934635661045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2681336845093159028429453 1005501316909934635661045)
                ·
                  refine ⟨94265748460306372093223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1005501316909934635661045 94265748460306372093223)
                  ·
                    rfl

theorem cell23_1652237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1652237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652237 prefixEnd_1652237 := by exact prefixLift 1652237
  have htrace : WordTrace (prefixWord ++ tailWord_1652237) baseStart_1652237 baseEnd_1652237 := by
    simpa [prefixWord, tailWord_1652237, baseEnd_1652237] using wordTrace_append hprefix tailTrace_1652237
  have hstable : (prefixWord ++ tailWord_1652237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652237).length < 2 ^ (prefixWord ++ tailWord_1652237).sum := by decide
  have hdescent : baseEnd_1652237 < baseStart_1652237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652254 : List Nat := [4, 3, 3, 1, 1, 1, 3, 2, 5]
def baseStart_1652254 : Nat := 118140960795 + 1652254 * 2 ^ 59
def prefixEnd_1652254 : Nat := 4983230072969 + 3 ^ 40 * 1652254 * 2
def baseEnd_1652254 : Nat := 94266718368209309147381

theorem tailTrace_1652254 : CollatzResearch.WordTrace tailWord_1652254 prefixEnd_1652254 94266718368209309147381 := by
  unfold tailWord_1652254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7532831769521676920326477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40175102770782276908407877 7532831769521676920326477)
  ·
    refine ⟨2824811913570628845122429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7532831769521676920326477 2824811913570628845122429)
    ·
      refine ⟨1059304467588985816920911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2824811913570628845122429 1059304467588985816920911)
      ·
        refine ⟨1588956701383478725381367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1059304467588985816920911 1588956701383478725381367)
        ·
          refine ⟨2383435052075218088072051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1588956701383478725381367 2383435052075218088072051)
          ·
            refine ⟨3575152578112827132108077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2383435052075218088072051 3575152578112827132108077)
            ·
              refine ⟨1340682216792310174540529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3575152578112827132108077 1340682216792310174540529)
              ·
                refine ⟨1005511662594232630905397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1340682216792310174540529 1005511662594232630905397)
                ·
                  refine ⟨94266718368209309147381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1005511662594232630905397 94266718368209309147381)
                  ·
                    rfl

theorem cell23_1652254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_1652254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652254 prefixEnd_1652254 := by exact prefixLift 1652254
  have htrace : WordTrace (prefixWord ++ tailWord_1652254) baseStart_1652254 baseEnd_1652254 := by
    simpa [prefixWord, tailWord_1652254, baseEnd_1652254] using wordTrace_append hprefix tailTrace_1652254
  have hstable : (prefixWord ++ tailWord_1652254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652254).length < 2 ^ (prefixWord ++ tailWord_1652254).sum := by decide
  have hdescent : baseEnd_1652254 < baseStart_1652254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652256 : List Nat := [2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1652256 : Nat := 118140960795 + 1652256 * 2 ^ 59
def prefixEnd_1652256 : Nat := 4983230072969 + 3 ^ 40 * 1652256 * 2
def baseEnd_1652256 : Nat := 848401492275192774501419

theorem tailTrace_1652256 : CollatzResearch.WordTrace tailWord_1652256 prefixEnd_1652256 848401492275192774501419 := by
  unfold tailWord_1652256
  simp only [CollatzResearch.WordTrace]
  refine ⟨30131363551083084852092311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40175151401444113136123081 30131363551083084852092311)
  ·
    refine ⟨45197045326624627278138467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30131363551083084852092311 45197045326624627278138467)
    ·
      refine ⟨67795567989936940917207701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45197045326624627278138467 67795567989936940917207701)
      ·
        refine ⟨3177917249528294105494111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67795567989936940917207701 3177917249528294105494111)
        ·
          refine ⟨4766875874292441158241167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3177917249528294105494111 4766875874292441158241167)
          ·
            refine ⟨7150313811438661737361751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4766875874292441158241167 7150313811438661737361751)
            ·
              refine ⟨10725470717157992606042627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7150313811438661737361751 10725470717157992606042627)
              ·
                refine ⟨16088206075736988909063941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10725470717157992606042627 16088206075736988909063941)
                ·
                  refine ⟨3016538639200685420449489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16088206075736988909063941 3016538639200685420449489)
                  ·
                    refine ⟨2262403979400514065337117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3016538639200685420449489 2262403979400514065337117)
                    ·
                      refine ⟨848401492275192774501419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2262403979400514065337117 848401492275192774501419)
                      ·
                        rfl

theorem cell23_1652256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1652256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652256 prefixEnd_1652256 := by exact prefixLift 1652256
  have htrace : WordTrace (prefixWord ++ tailWord_1652256) baseStart_1652256 baseEnd_1652256 := by
    simpa [prefixWord, tailWord_1652256, baseEnd_1652256] using wordTrace_append hprefix tailTrace_1652256
  have hstable : (prefixWord ++ tailWord_1652256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652256).length < 2 ^ (prefixWord ++ tailWord_1652256).sum := by decide
  have hdescent : baseEnd_1652256 < baseStart_1652256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652272 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 2, 9]
def baseStart_1652272 : Nat := 118140960795 + 1652272 * 2 ^ 59
def prefixEnd_1652272 : Nat := 4983230072969 + 3 ^ 40 * 1652272 * 2
def baseEnd_1652272 : Nat := 282803235988554903967115

theorem tailTrace_1652272 : CollatzResearch.WordTrace tailWord_1652272 prefixEnd_1652272 282803235988554903967115 := by
  unfold tailWord_1652272
  simp only [CollatzResearch.WordTrace]
  refine ⟨30131655335054102218383535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40175540446738802957844713 30131655335054102218383535)
  ·
    refine ⟨45197483002581153327575303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30131655335054102218383535 45197483002581153327575303)
    ·
      refine ⟨67796224503871729991362955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45197483002581153327575303 67796224503871729991362955)
      ·
        refine ⟨101694336755807594987044433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67796224503871729991362955 101694336755807594987044433)
        ·
          refine ⟨76270752566855696240283325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101694336755807594987044433 76270752566855696240283325)
          ·
            refine ⟨28601532212570886090106247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76270752566855696240283325 28601532212570886090106247)
            ·
              refine ⟨42902298318856329135159371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28601532212570886090106247 42902298318856329135159371)
              ·
                refine ⟨64353447478284493702739057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42902298318856329135159371 64353447478284493702739057)
                ·
                  refine ⟨48265085608713370277054293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64353447478284493702739057 48265085608713370277054293)
                  ·
                    refine ⟨282803235988554903967115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 48265085608713370277054293 282803235988554903967115)
                    ·
                      rfl

theorem cell23_1652272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 9].length) (baseStart_1652272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652272 prefixEnd_1652272 := by exact prefixLift 1652272
  have htrace : WordTrace (prefixWord ++ tailWord_1652272) baseStart_1652272 baseEnd_1652272 := by
    simpa [prefixWord, tailWord_1652272, baseEnd_1652272] using wordTrace_append hprefix tailTrace_1652272
  have hstable : (prefixWord ++ tailWord_1652272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652272).length < 2 ^ (prefixWord ++ tailWord_1652272).sum := by decide
  have hdescent : baseEnd_1652272 < baseStart_1652272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652303 : List Nat := [1, 1, 2, 1, 1, 2, 3, 7, 1, 1, 3]
def baseStart_1652303 : Nat := 118140960795 + 1652303 * 2 ^ 59
def prefixEnd_1652303 : Nat := 4983230072969 + 3 ^ 40 * 1652303 * 2
def baseEnd_1652303 : Nat := 848425625865954090613703

theorem tailTrace_1652303 : CollatzResearch.WordTrace tailWord_1652303 prefixEnd_1652303 848425625865954090613703 := by
  unfold tailWord_1652303
  simp only [CollatzResearch.WordTrace]
  refine ⟨60264441332995896731145563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40176294221997264487430375 60264441332995896731145563)
  ·
    refine ⟨90396661999493845096718345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60264441332995896731145563 90396661999493845096718345)
    ·
      refine ⟨67797496499620383822538759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90396661999493845096718345 67797496499620383822538759)
      ·
        refine ⟨101696244749430575733808139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67797496499620383822538759 101696244749430575733808139)
        ·
          refine ⟨152544367124145863600712209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101696244749430575733808139 152544367124145863600712209)
          ·
            refine ⟨114408275343109397700534157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152544367124145863600712209 114408275343109397700534157)
            ·
              refine ⟨42903103253666024137700309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114408275343109397700534157 42903103253666024137700309)
              ·
                refine ⟨1005541482507797440727351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 42903103253666024137700309 1005541482507797440727351)
                ·
                  refine ⟨1508312223761696161091027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005541482507797440727351 1508312223761696161091027)
                  ·
                    refine ⟨2262468335642544241636541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1508312223761696161091027 2262468335642544241636541)
                    ·
                      refine ⟨848425625865954090613703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2262468335642544241636541 848425625865954090613703)
                      ·
                        rfl

theorem cell23_1652303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 1, 1, 3].length) (baseStart_1652303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652303 prefixEnd_1652303 := by exact prefixLift 1652303
  have htrace : WordTrace (prefixWord ++ tailWord_1652303) baseStart_1652303 baseEnd_1652303 := by
    simpa [prefixWord, tailWord_1652303, baseEnd_1652303] using wordTrace_append hprefix tailTrace_1652303
  have hstable : (prefixWord ++ tailWord_1652303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652303).length < 2 ^ (prefixWord ++ tailWord_1652303).sum := by decide
  have hdescent : baseEnd_1652303 < baseStart_1652303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652329 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 1, 1, 5]
def baseStart_1652329 : Nat := 118140960795 + 1652329 * 2 ^ 59
def prefixEnd_1652329 : Nat := 4983230072969 + 3 ^ 40 * 1652329 * 2
def baseEnd_1652329 : Nat := 848438976362970988888583

theorem tailTrace_1652329 : CollatzResearch.WordTrace tailWord_1652329 prefixEnd_1652329 848438976362970988888583 := by
  unfold tailWord_1652329
  simp only [CollatzResearch.WordTrace]
  refine ⟨60265389630901703171592041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40176926420601135447728027 60265389630901703171592041)
  ·
    refine ⟨45199042223176277378694031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60265389630901703171592041 45199042223176277378694031)
    ·
      refine ⟨67798563334764416068041047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45199042223176277378694031 67798563334764416068041047)
      ·
        refine ⟨101697845002146624102061571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67798563334764416068041047 101697845002146624102061571)
        ·
          refine ⟨152546767503219936153092357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101697845002146624102061571 152546767503219936153092357)
          ·
            refine ⟨28602518906853738028704817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152546767503219936153092357 28602518906853738028704817)
            ·
              refine ⟨21451889180140303521528613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28602518906853738028704817 21451889180140303521528613)
              ·
                refine ⟨4022229221276306910286615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21451889180140303521528613 4022229221276306910286615)
                ·
                  refine ⟨6033343831914460365429923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4022229221276306910286615 6033343831914460365429923)
                  ·
                    refine ⟨9050015747871690548144885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6033343831914460365429923 9050015747871690548144885)
                    ·
                      refine ⟨848438976362970988888583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9050015747871690548144885 848438976362970988888583)
                      ·
                        rfl

theorem cell23_1652329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_1652329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652329 prefixEnd_1652329 := by exact prefixLift 1652329
  have htrace : WordTrace (prefixWord ++ tailWord_1652329) baseStart_1652329 baseEnd_1652329 := by
    simpa [prefixWord, tailWord_1652329, baseEnd_1652329] using wordTrace_append hprefix tailTrace_1652329
  have hstable : (prefixWord ++ tailWord_1652329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652329).length < 2 ^ (prefixWord ++ tailWord_1652329).sum := by decide
  have hdescent : baseEnd_1652329 < baseStart_1652329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652336 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 1, 6]
def baseStart_1652336 : Nat := 118140960795 + 1652336 * 2 ^ 59
def prefixEnd_1652336 : Nat := 4983230072969 + 3 ^ 40 * 1652336 * 2
def baseEnd_1652336 : Nat := 282814190242517487167017

theorem tailTrace_1652336 : CollatzResearch.WordTrace tailWord_1652336 prefixEnd_1652336 282814190242517487167017 := by
  unfold tailWord_1652336
  simp only [CollatzResearch.WordTrace]
  refine ⟨30132822470938171683548431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40177096627917562244731241 30132822470938171683548431)
  ·
    refine ⟨45199233706407257525322647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30132822470938171683548431 45199233706407257525322647)
    ·
      refine ⟨67798850559610886287983971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45199233706407257525322647 67798850559610886287983971)
      ·
        refine ⟨101698275839416329431975957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67798850559610886287983971 101698275839416329431975957)
        ·
          refine ⟨4767106679972640442123873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101698275839416329431975957 4767106679972640442123873)
          ·
            refine ⟨3575330009979480331592905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4767106679972640442123873 3575330009979480331592905)
            ·
              refine ⟨2681497507484610248694679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3575330009979480331592905 2681497507484610248694679)
              ·
                refine ⟨4022246261226915373042019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2681497507484610248694679 4022246261226915373042019)
                ·
                  refine ⟨6033369391840373059563029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4022246261226915373042019 6033369391840373059563029)
                  ·
                    refine ⟨282814190242517487167017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6033369391840373059563029 282814190242517487167017)
                    ·
                      rfl

theorem cell23_1652336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 1, 6].length) (baseStart_1652336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652336 prefixEnd_1652336 := by exact prefixLift 1652336
  have htrace : WordTrace (prefixWord ++ tailWord_1652336) baseStart_1652336 baseEnd_1652336 := by
    simpa [prefixWord, tailWord_1652336, baseEnd_1652336] using wordTrace_append hprefix tailTrace_1652336
  have hstable : (prefixWord ++ tailWord_1652336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652336).length < 2 ^ (prefixWord ++ tailWord_1652336).sum := by decide
  have hdescent : baseEnd_1652336 < baseStart_1652336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652360 : List Nat := [2, 1, 3, 5, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1652360 : Nat := 118140960795 + 1652360 * 2 ^ 59
def prefixEnd_1652360 : Nat := 4983230072969 + 3 ^ 40 * 1652360 * 2
def baseEnd_1652360 : Nat := 848454894263260367600941

theorem tailTrace_1652360 : CollatzResearch.WordTrace tailWord_1652360 prefixEnd_1652360 848454894263260367600941 := by
  unfold tailWord_1652360
  simp only [CollatzResearch.WordTrace]
  refine ⟨30133260146894697732985267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40177680195859596977313689 30133260146894697732985267)
  ·
    refine ⟨45199890220342046599477901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30133260146894697732985267 45199890220342046599477901)
    ·
      refine ⟨16949958832628267474804213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45199890220342046599477901 16949958832628267474804213)
      ·
        refine ⟨1589058640558900075762895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16949958832628267474804213 1589058640558900075762895)
        ·
          refine ⟨2383587960838350113644343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589058640558900075762895 2383587960838350113644343)
          ·
            refine ⟨3575381941257525170466515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2383587960838350113644343 3575381941257525170466515)
            ·
              refine ⟨5363072911886287755699773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3575381941257525170466515 5363072911886287755699773)
              ·
                refine ⟨2011152341957357908387415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5363072911886287755699773 2011152341957357908387415)
                ·
                  refine ⟨3016728512936036862581123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011152341957357908387415 3016728512936036862581123)
                  ·
                    refine ⟨4525092769404055293871685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3016728512936036862581123 4525092769404055293871685)
                    ·
                      refine ⟨848454894263260367600941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4525092769404055293871685 848454894263260367600941)
                      ·
                        rfl

theorem cell23_1652360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1652360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652360 prefixEnd_1652360 := by exact prefixLift 1652360
  have htrace : WordTrace (prefixWord ++ tailWord_1652360) baseStart_1652360 baseEnd_1652360 := by
    simpa [prefixWord, tailWord_1652360, baseEnd_1652360] using wordTrace_append hprefix tailTrace_1652360
  have hstable : (prefixWord ++ tailWord_1652360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652360).length < 2 ^ (prefixWord ++ tailWord_1652360).sum := by decide
  have hdescent : baseEnd_1652360 < baseStart_1652360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652409 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 1, 8]
def baseStart_1652409 : Nat := 118140960795 + 1652409 * 2 ^ 59
def prefixEnd_1652409 : Nat := 4983230072969 + 3 ^ 40 * 1652409 * 2
def baseEnd_1652409 : Nat := 282826684938443558629405

theorem tailTrace_1652409 : CollatzResearch.WordTrace tailWord_1652409 prefixEnd_1652409 282826684938443558629405 := by
  unfold tailWord_1652409
  simp only [CollatzResearch.WordTrace]
  refine ⟨60268307470611876834504281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40178871647074584556336187 60268307470611876834504281)
  ·
    refine ⟨45201230602958907625878211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60268307470611876834504281 45201230602958907625878211)
    ·
      refine ⟨67801845904438361438817317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45201230602958907625878211 67801845904438361438817317)
      ·
        refine ⟨12712846107082192769778247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67801845904438361438817317 12712846107082192769778247)
        ·
          refine ⟨19069269160623289154667371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12712846107082192769778247 19069269160623289154667371)
          ·
            refine ⟨28603903740934933732001057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19069269160623289154667371 28603903740934933732001057)
            ·
              refine ⟨21452927805701200299000793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28603903740934933732001057 21452927805701200299000793)
              ·
                refine ⟨16089695854275900224250595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21452927805701200299000793 16089695854275900224250595)
                ·
                  refine ⟨24134543781413850336375893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16089695854275900224250595 24134543781413850336375893)
                  ·
                    refine ⟨282826684938443558629405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24134543781413850336375893 282826684938443558629405)
                    ·
                      rfl

theorem cell23_1652409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 8].length) (baseStart_1652409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652409 prefixEnd_1652409 := by exact prefixLift 1652409
  have htrace : WordTrace (prefixWord ++ tailWord_1652409) baseStart_1652409 baseEnd_1652409 := by
    simpa [prefixWord, tailWord_1652409, baseEnd_1652409] using wordTrace_append hprefix tailTrace_1652409
  have hstable : (prefixWord ++ tailWord_1652409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652409).length < 2 ^ (prefixWord ++ tailWord_1652409).sum := by decide
  have hdescent : baseEnd_1652409 < baseStart_1652409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652420 : List Nat := [2, 3, 3, 1, 1, 1, 1, 5, 1, 3, 2]
def baseStart_1652420 : Nat := 118140960795 + 1652420 * 2 ^ 59
def prefixEnd_1652420 : Nat := 4983230072969 + 3 ^ 40 * 1652420 * 2
def baseEnd_1652420 : Nat := 848485703102530132850665

theorem tailTrace_1652420 : CollatzResearch.WordTrace tailWord_1652420 prefixEnd_1652420 848485703102530132850665 := by
  unfold tailWord_1652420
  simp only [CollatzResearch.WordTrace]
  refine ⟨30134354336786012856577357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40179139115714683808769809 30134354336786012856577357)
  ·
    refine ⟨11300382876294754821216509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30134354336786012856577357 11300382876294754821216509)
    ·
      refine ⟨4237643578610533057956191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11300382876294754821216509 4237643578610533057956191)
      ·
        refine ⟨6356465367915799586934287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4237643578610533057956191 6356465367915799586934287)
        ·
          refine ⟨9534698051873699380401431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6356465367915799586934287 9534698051873699380401431)
          ·
            refine ⟨14302047077810549070602147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9534698051873699380401431 14302047077810549070602147)
            ·
              refine ⟨21453070616715823605903221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14302047077810549070602147 21453070616715823605903221)
              ·
                refine ⟨2011225370317108463053427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21453070616715823605903221 2011225370317108463053427)
                ·
                  refine ⟨3016838055475662694580141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011225370317108463053427 3016838055475662694580141)
                  ·
                    refine ⟨1131314270803373510467553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3016838055475662694580141 1131314270803373510467553)
                    ·
                      refine ⟨848485703102530132850665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1131314270803373510467553 848485703102530132850665)
                      ·
                        rfl

theorem cell23_1652420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_1652420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652420 prefixEnd_1652420 := by exact prefixLift 1652420
  have htrace : WordTrace (prefixWord ++ tailWord_1652420) baseStart_1652420 baseEnd_1652420 := by
    simpa [prefixWord, tailWord_1652420, baseEnd_1652420] using wordTrace_append hprefix tailTrace_1652420
  have hstable : (prefixWord ++ tailWord_1652420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652420).length < 2 ^ (prefixWord ++ tailWord_1652420).sum := by decide
  have hdescent : baseEnd_1652420 < baseStart_1652420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652490 : List Nat := [3, 1, 2, 2, 1, 3, 4, 2, 5]
def baseStart_1652490 : Nat := 118140960795 + 1652490 * 2 ^ 59
def prefixEnd_1652490 : Nat := 4983230072969 + 3 ^ 40 * 1652490 * 2
def baseEnd_1652490 : Nat := 94280182972038317663927

theorem tailTrace_1652490 : CollatzResearch.WordTrace tailWord_1652490 prefixEnd_1652490 94280182972038317663927 := by
  unfold tailWord_1652490
  simp only [CollatzResearch.WordTrace]
  refine ⟨15067815445829606917050731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40180841188878951778801949 15067815445829606917050731)
  ·
    refine ⟨22601723168744410375576097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15067815445829606917050731 22601723168744410375576097)
    ·
      refine ⟨16951292376558307781682073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22601723168744410375576097 16951292376558307781682073)
      ·
        refine ⟨12713469282418730836261555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16951292376558307781682073 12713469282418730836261555)
        ·
          refine ⟨19070203923628096254392333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12713469282418730836261555 19070203923628096254392333)
          ·
            refine ⟨7151326471360536095397125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19070203923628096254392333 7151326471360536095397125)
            ·
              refine ⟨1340873713380100517886961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7151326471360536095397125 1340873713380100517886961)
              ·
                refine ⟨1005655285035075388415221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1340873713380100517886961 1005655285035075388415221)
                ·
                  refine ⟨94280182972038317663927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1005655285035075388415221 94280182972038317663927)
                  ·
                    rfl

theorem cell23_1652490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 5].length) (baseStart_1652490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652490 prefixEnd_1652490 := by exact prefixLift 1652490
  have htrace : WordTrace (prefixWord ++ tailWord_1652490) baseStart_1652490 baseEnd_1652490 := by
    simpa [prefixWord, tailWord_1652490, baseEnd_1652490] using wordTrace_append hprefix tailTrace_1652490
  have hstable : (prefixWord ++ tailWord_1652490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652490).length < 2 ^ (prefixWord ++ tailWord_1652490).sum := by decide
  have hdescent : baseEnd_1652490 < baseStart_1652490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652520 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1652520 : Nat := 118140960795 + 1652520 * 2 ^ 59
def prefixEnd_1652520 : Nat := 4983230072969 + 3 ^ 40 * 1652520 * 2
def baseEnd_1652520 : Nat := 282845683722659913866735

theorem tailTrace_1652520 : CollatzResearch.WordTrace tailWord_1652520 prefixEnd_1652520 282845683722659913866735 := by
  unfold tailWord_1652520
  simp only [CollatzResearch.WordTrace]
  refine ⟨30136177986604871395897507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40181570648806495194530009 30136177986604871395897507)
  ·
    refine ⟨45204266979907307093846261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30136177986604871395897507 45204266979907307093846261)
    ·
      refine ⟨4237900029366310040048087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45204266979907307093846261 4237900029366310040048087)
      ·
        refine ⟨6356850044049465060072131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4237900029366310040048087 6356850044049465060072131)
        ·
          refine ⟨9535275066074197590108197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6356850044049465060072131 9535275066074197590108197)
          ·
            refine ⟨1787864074888912048145287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9535275066074197590108197 1787864074888912048145287)
            ·
              refine ⟨2681796112333368072217931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1787864074888912048145287 2681796112333368072217931)
              ·
                refine ⟨4022694168500052108326897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2681796112333368072217931 4022694168500052108326897)
                ·
                  refine ⟨3017020626375039081245173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4022694168500052108326897 3017020626375039081245173)
                  ·
                    refine ⟨282845683722659913866735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3017020626375039081245173 282845683722659913866735)
                    ·
                      rfl

theorem cell23_1652520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1652520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652520 prefixEnd_1652520 := by exact prefixLift 1652520
  have htrace : WordTrace (prefixWord ++ tailWord_1652520) baseStart_1652520 baseEnd_1652520 := by
    simpa [prefixWord, tailWord_1652520, baseEnd_1652520] using wordTrace_append hprefix tailTrace_1652520
  have hstable : (prefixWord ++ tailWord_1652520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652520).length < 2 ^ (prefixWord ++ tailWord_1652520).sum := by decide
  have hdescent : baseEnd_1652520 < baseStart_1652520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652536 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 2, 1, 6]
def baseStart_1652536 : Nat := 118140960795 + 1652536 * 2 ^ 59
def prefixEnd_1652536 : Nat := 4983230072969 + 3 ^ 40 * 1652536 * 2
def baseEnd_1652536 : Nat := 848545266858451679000131

theorem tailTrace_1652536 : CollatzResearch.WordTrace tailWord_1652536 prefixEnd_1652536 848545266858451679000131 := by
  unfold tailWord_1652536
  simp only [CollatzResearch.WordTrace]
  refine ⟨30136469770575888762188731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40181959694101185016251641 30136469770575888762188731)
  ·
    refine ⟨45204704655863833143283097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30136469770575888762188731 45204704655863833143283097)
    ·
      refine ⟨33903528491897874857462323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45204704655863833143283097 33903528491897874857462323)
      ·
        refine ⟨50855292737846812286193485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33903528491897874857462323 50855292737846812286193485)
        ·
          refine ⟨19070734776692554607322557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50855292737846812286193485 19070734776692554607322557)
          ·
            refine ⟨7151525541259707977745959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19070734776692554607322557 7151525541259707977745959)
            ·
              refine ⟨10727288311889561966618939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7151525541259707977745959 10727288311889561966618939)
              ·
                refine ⟨16090932467834342949928409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10727288311889561966618939 16090932467834342949928409)
                ·
                  refine ⟨12068199350875757212446307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16090932467834342949928409 12068199350875757212446307)
                  ·
                    refine ⟨18102299026313635818669461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12068199350875757212446307 18102299026313635818669461)
                    ·
                      refine ⟨848545266858451679000131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18102299026313635818669461 848545266858451679000131)
                      ·
                        rfl

theorem cell23_1652536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 2, 1, 6].length) (baseStart_1652536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652536 prefixEnd_1652536 := by exact prefixLift 1652536
  have htrace : WordTrace (prefixWord ++ tailWord_1652536) baseStart_1652536 baseEnd_1652536 := by
    simpa [prefixWord, tailWord_1652536, baseEnd_1652536] using wordTrace_append hprefix tailTrace_1652536
  have hstable : (prefixWord ++ tailWord_1652536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652536).length < 2 ^ (prefixWord ++ tailWord_1652536).sum := by decide
  have hdescent : baseEnd_1652536 < baseStart_1652536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652557 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_1652557 : Nat := 118140960795 + 1652557 * 2 ^ 59
def prefixEnd_1652557 : Nat := 4983230072969 + 3 ^ 40 * 1652557 * 2
def baseEnd_1652557 : Nat := 848556049952196096837535

theorem tailTrace_1652557 : CollatzResearch.WordTrace tailWord_1652557 prefixEnd_1652557 848556049952196096837535 := by
  unfold tailWord_1652557
  simp only [CollatzResearch.WordTrace]
  refine ⟨60273705474075698110891925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40182470316050465407261283 60273705474075698110891925)
  ·
    refine ⟨2825329944097298348948059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 60273705474075698110891925 2825329944097298348948059)
    ·
      refine ⟨4237994916145947523422089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2825329944097298348948059 4237994916145947523422089)
      ·
        refine ⟨3178496187109460642566567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4237994916145947523422089 3178496187109460642566567)
        ·
          refine ⟨4767744280664190963849851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3178496187109460642566567 4767744280664190963849851)
          ·
            refine ⟨7151616420996286445774777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767744280664190963849851 7151616420996286445774777)
            ·
              refine ⟨5363712315747214834331083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7151616420996286445774777 5363712315747214834331083)
              ·
                refine ⟨8045568473620822251496625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5363712315747214834331083 8045568473620822251496625)
                ·
                  refine ⟨6034176355215616688622469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8045568473620822251496625 6034176355215616688622469)
                  ·
                    refine ⟨1131408066602928129116713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6034176355215616688622469 1131408066602928129116713)
                    ·
                      refine ⟨848556049952196096837535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1131408066602928129116713 848556049952196096837535)
                      ·
                        rfl

theorem cell23_1652557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_1652557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652557 prefixEnd_1652557 := by exact prefixLift 1652557
  have htrace : WordTrace (prefixWord ++ tailWord_1652557) baseStart_1652557 baseEnd_1652557 := by
    simpa [prefixWord, tailWord_1652557, baseEnd_1652557] using wordTrace_append hprefix tailTrace_1652557
  have hstable : (prefixWord ++ tailWord_1652557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652557).length < 2 ^ (prefixWord ++ tailWord_1652557).sum := by decide
  have hdescent : baseEnd_1652557 < baseStart_1652557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652593 : List Nat := [1, 2, 2, 2, 1, 3, 1, 5, 1, 5]
def baseStart_1652593 : Nat := 118140960795 + 1652593 * 2 ^ 59
def prefixEnd_1652593 : Nat := 4983230072969 + 3 ^ 40 * 1652593 * 2
def baseEnd_1652593 : Nat := 282858178418585985329123

theorem tailTrace_1652593 : CollatzResearch.WordTrace tailWord_1652593 prefixEnd_1652593 282858178418585985329123 := by
  unfold tailWord_1652593
  simp only [CollatzResearch.WordTrace]
  refine ⟨60275018501945276259202433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40183345667963517506134955 60275018501945276259202433)
  ·
    refine ⟨45206263876458957194401825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60275018501945276259202433 45206263876458957194401825)
    ·
      refine ⟨33904697907344217895801369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45206263876458957194401825 33904697907344217895801369)
      ·
        refine ⟨25428523430508163421851027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33904697907344217895801369 25428523430508163421851027)
        ·
          refine ⟨38142785145762245132776541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25428523430508163421851027 38142785145762245132776541)
          ·
            refine ⟨14303544429660841924791203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38142785145762245132776541 14303544429660841924791203)
            ·
              refine ⟨21455316644491262887186805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14303544429660841924791203 21455316644491262887186805)
              ·
                refine ⟨2011435935421055895673763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21455316644491262887186805 2011435935421055895673763)
                ·
                  refine ⟨3017153903131583843510645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011435935421055895673763 3017153903131583843510645)
                  ·
                    refine ⟨282858178418585985329123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3017153903131583843510645 282858178418585985329123)
                    ·
                      rfl

theorem cell23_1652593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_1652593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652593 prefixEnd_1652593 := by exact prefixLift 1652593
  have htrace : WordTrace (prefixWord ++ tailWord_1652593) baseStart_1652593 baseEnd_1652593 := by
    simpa [prefixWord, tailWord_1652593, baseEnd_1652593] using wordTrace_append hprefix tailTrace_1652593
  have hstable : (prefixWord ++ tailWord_1652593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652593).length < 2 ^ (prefixWord ++ tailWord_1652593).sum := by decide
  have hdescent : baseEnd_1652593 < baseStart_1652593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652613 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 3, 1, 4]
def baseStart_1652613 : Nat := 118140960795 + 1652613 * 2 ^ 59
def prefixEnd_1652613 : Nat := 4983230072969 + 3 ^ 40 * 1652613 * 2
def baseEnd_1652613 : Nat := 848584804868847877737277

theorem tailTrace_1652613 : CollatzResearch.WordTrace tailWord_1652613 prefixEnd_1652613 848584804868847877737277 := by
  unfold tailWord_1652613
  simp only [CollatzResearch.WordTrace]
  refine ⟨60275747961872819674930493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40183831974581879783286995 60275747961872819674930493)
  ·
    refine ⟨22603405485702307378098935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60275747961872819674930493 22603405485702307378098935)
    ·
      refine ⟨33905108228553461067148403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22603405485702307378098935 33905108228553461067148403)
      ·
        refine ⟨50857662342830191600722605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33905108228553461067148403 50857662342830191600722605)
        ·
          refine ⟨19071623378561321850270977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50857662342830191600722605 19071623378561321850270977)
          ·
            refine ⟨14303717533920991387703233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19071623378561321850270977 14303717533920991387703233)
            ·
              refine ⟨10727788150440743540777425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14303717533920991387703233 10727788150440743540777425)
              ·
                refine ⟨8045841112830557655583069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10727788150440743540777425 8045841112830557655583069)
                ·
                  refine ⟨3017190417311459120843651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8045841112830557655583069 3017190417311459120843651)
                  ·
                    refine ⟨4525785625967188681265477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3017190417311459120843651 4525785625967188681265477)
                    ·
                      refine ⟨848584804868847877737277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4525785625967188681265477 848584804868847877737277)
                      ·
                        rfl

theorem cell23_1652613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_1652613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652613 prefixEnd_1652613 := by exact prefixLift 1652613
  have htrace : WordTrace (prefixWord ++ tailWord_1652613) baseStart_1652613 baseEnd_1652613 := by
    simpa [prefixWord, tailWord_1652613, baseEnd_1652613] using wordTrace_append hprefix tailTrace_1652613
  have hstable : (prefixWord ++ tailWord_1652613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652613).length < 2 ^ (prefixWord ++ tailWord_1652613).sum := by decide
  have hdescent : baseEnd_1652613 < baseStart_1652613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652656 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 8]
def baseStart_1652656 : Nat := 118140960795 + 1652656 * 2 ^ 59
def prefixEnd_1652656 : Nat := 4983230072969 + 3 ^ 40 * 1652656 * 2
def baseEnd_1652656 : Nat := 848606884536991209499579

theorem tailTrace_1652656 : CollatzResearch.WordTrace tailWord_1652656 prefixEnd_1652656 848606884536991209499579 := by
  unfold tailWord_1652656
  simp only [CollatzResearch.WordTrace]
  refine ⟨30138658150358519009372911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40184877533811358679163881 30138658150358519009372911)
  ·
    refine ⟨45207987225537778514059367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30138658150358519009372911 45207987225537778514059367)
    ·
      refine ⟨67811980838306667771089051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45207987225537778514059367 67811980838306667771089051)
      ·
        refine ⟨101717971257460001656633577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67811980838306667771089051 101717971257460001656633577)
        ·
          refine ⟨76288478443095001242475183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101717971257460001656633577 76288478443095001242475183)
          ·
            refine ⟨114432717664642501863712775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76288478443095001242475183 114432717664642501863712775)
            ·
              refine ⟨171649076496963752795569163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114432717664642501863712775 171649076496963752795569163)
              ·
                refine ⟨257473614745445629193353745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171649076496963752795569163 257473614745445629193353745)
                ·
                  refine ⟨193105211059084221895015309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257473614745445629193353745 193105211059084221895015309)
                  ·
                    refine ⟨72414454147156583210630741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 193105211059084221895015309 72414454147156583210630741)
                    ·
                      refine ⟨848606884536991209499579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 72414454147156583210630741 848606884536991209499579)
                      ·
                        rfl

theorem cell23_1652656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 8].length) (baseStart_1652656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652656 prefixEnd_1652656 := by exact prefixLift 1652656
  have htrace : WordTrace (prefixWord ++ tailWord_1652656) baseStart_1652656 baseEnd_1652656 := by
    simpa [prefixWord, tailWord_1652656, baseEnd_1652656] using wordTrace_append hprefix tailTrace_1652656
  have hstable : (prefixWord ++ tailWord_1652656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652656).length < 2 ^ (prefixWord ++ tailWord_1652656).sum := by decide
  have hdescent : baseEnd_1652656 < baseStart_1652656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652657 : List Nat := [1, 2, 2, 4, 2, 2, 2, 2, 2, 4]
def baseStart_1652657 : Nat := 118140960795 + 1652657 * 2 ^ 59
def prefixEnd_1652657 : Nat := 4983230072969 + 3 ^ 40 * 1652657 * 2
def baseEnd_1652657 : Nat := 282869132672548568529025

theorem tailTrace_1652657 : CollatzResearch.WordTrace tailWord_1652657 prefixEnd_1652657 282869132672548568529025 := by
  unfold tailWord_1652657
  simp only [CollatzResearch.WordTrace]
  refine ⟨60277352773713415189532225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40184901849142276793021483 60277352773713415189532225)
  ·
    refine ⟨45208014580285061392149169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60277352773713415189532225 45208014580285061392149169)
    ·
      refine ⟨33906010935213796044111877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45208014580285061392149169 33906010935213796044111877)
      ·
        refine ⟨6357377050352586758270977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33906010935213796044111877 6357377050352586758270977)
        ·
          refine ⟨4768032787764440068703233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6357377050352586758270977 4768032787764440068703233)
          ·
            refine ⟨3576024590823330051527425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4768032787764440068703233 3576024590823330051527425)
            ·
              refine ⟨2682018443117497538645569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3576024590823330051527425 2682018443117497538645569)
              ·
                refine ⟨2011513832338123153984177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2682018443117497538645569 2011513832338123153984177)
                ·
                  refine ⟨1508635374253592365488133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2011513832338123153984177 1508635374253592365488133)
                  ·
                    refine ⟨282869132672548568529025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1508635374253592365488133 282869132672548568529025)
                    ·
                      rfl

theorem cell23_1652657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_1652657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652657 prefixEnd_1652657 := by exact prefixLift 1652657
  have htrace : WordTrace (prefixWord ++ tailWord_1652657) baseStart_1652657 baseEnd_1652657 := by
    simpa [prefixWord, tailWord_1652657, baseEnd_1652657] using wordTrace_append hprefix tailTrace_1652657
  have hstable : (prefixWord ++ tailWord_1652657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652657).length < 2 ^ (prefixWord ++ tailWord_1652657).sum := by decide
  have hdescent : baseEnd_1652657 < baseStart_1652657 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652663 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 3]
def baseStart_1652663 : Nat := 118140960795 + 1652663 * 2 ^ 59
def prefixEnd_1652663 : Nat := 4983230072969 + 3 ^ 40 * 1652663 * 2
def baseEnd_1652663 : Nat := 848610478901572682112047

theorem tailTrace_1652663 : CollatzResearch.WordTrace tailWord_1652663 prefixEnd_1652663 848610478901572682112047 := by
  unfold tailWord_1652663
  simp only [CollatzResearch.WordTrace]
  refine ⟨60277571611691678214250643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40185047741127785476167095 60277571611691678214250643)
  ·
    refine ⟨90416357417537517321375965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60277571611691678214250643 90416357417537517321375965)
    ·
      refine ⟨33906134031576568995515987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90416357417537517321375965 33906134031576568995515987)
      ·
        refine ⟨50859201047364853493273981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33906134031576568995515987 50859201047364853493273981)
        ·
          refine ⟨19072200392761820059977743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50859201047364853493273981 19072200392761820059977743)
          ·
            refine ⟨28608300589142730089966615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19072200392761820059977743 28608300589142730089966615)
            ·
              refine ⟨42912450883714095134949923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28608300589142730089966615 42912450883714095134949923)
              ·
                refine ⟨64368676325571142702424885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42912450883714095134949923 64368676325571142702424885)
                ·
                  refine ⟨6034563405522294628352333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64368676325571142702424885 6034563405522294628352333)
                  ·
                    refine ⟨2262961277070860485632125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6034563405522294628352333 2262961277070860485632125)
                    ·
                      refine ⟨848610478901572682112047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2262961277070860485632125 848610478901572682112047)
                      ·
                        rfl

theorem cell23_1652663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_1652663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652663 prefixEnd_1652663 := by exact prefixLift 1652663
  have htrace : WordTrace (prefixWord ++ tailWord_1652663) baseStart_1652663 baseEnd_1652663 := by
    simpa [prefixWord, tailWord_1652663, baseEnd_1652663] using wordTrace_append hprefix tailTrace_1652663
  have hstable : (prefixWord ++ tailWord_1652663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652663).length < 2 ^ (prefixWord ++ tailWord_1652663).sum := by decide
  have hdescent : baseEnd_1652663 < baseStart_1652663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652664 : List Nat := [2, 1, 2, 1, 2, 3, 3, 4, 1, 2, 2]
def baseStart_1652664 : Nat := 118140960795 + 1652664 * 2 ^ 59
def prefixEnd_1652664 : Nat := 4983230072969 + 3 ^ 40 * 1652664 * 2
def baseEnd_1652664 : Nat := 848610992382227178199543

theorem tailTrace_1652664 : CollatzResearch.WordTrace tailWord_1652664 prefixEnd_1652664 848610992382227178199543 := by
  unfold tailWord_1652664
  simp only [CollatzResearch.WordTrace]
  refine ⟨30138804042344027692518523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40185072056458703590024697 30138804042344027692518523)
  ·
    refine ⟨45208206063516041538777785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30138804042344027692518523 45208206063516041538777785)
    ·
      refine ⟨33906154547637031154083339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45208206063516041538777785 33906154547637031154083339)
      ·
        refine ⟨50859231821455546731125009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33906154547637031154083339 50859231821455546731125009)
        ·
          refine ⟨38144423866091660048343757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50859231821455546731125009 38144423866091660048343757)
          ·
            refine ⟨14304158949784372518128909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38144423866091660048343757 14304158949784372518128909)
            ·
              refine ⟨5364059606169139694298341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14304158949784372518128909 5364059606169139694298341)
              ·
                refine ⟨1005761176156713692680939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5364059606169139694298341 1005761176156713692680939)
                ·
                  refine ⟨1508641764235070539021409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005761176156713692680939 1508641764235070539021409)
                  ·
                    refine ⟨1131481323176302904266057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1508641764235070539021409 1131481323176302904266057)
                    ·
                      refine ⟨848610992382227178199543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1131481323176302904266057 848610992382227178199543)
                      ·
                        rfl

theorem cell23_1652664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 4, 1, 2, 2].length) (baseStart_1652664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652664 prefixEnd_1652664 := by exact prefixLift 1652664
  have htrace : WordTrace (prefixWord ++ tailWord_1652664) baseStart_1652664 baseEnd_1652664 := by
    simpa [prefixWord, tailWord_1652664, baseEnd_1652664] using wordTrace_append hprefix tailTrace_1652664
  have hstable : (prefixWord ++ tailWord_1652664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652664).length < 2 ^ (prefixWord ++ tailWord_1652664).sum := by decide
  have hdescent : baseEnd_1652664 < baseStart_1652664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652670 : List Nat := [4, 2, 1, 1, 1, 5, 1, 8]
def baseStart_1652670 : Nat := 118140960795 + 1652670 * 2 ^ 59
def prefixEnd_1652670 : Nat := 4983230072969 + 3 ^ 40 * 1652670 * 2
def baseEnd_1652670 : Nat := 31430150861709413137945

theorem tailTrace_1652670 : CollatzResearch.WordTrace tailWord_1652670 prefixEnd_1652670 31430150861709413137945 := by
  unfold tailWord_1652670
  simp only [CollatzResearch.WordTrace]
  refine ⟨7534728365333289801219433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40185217948444212273170309 7534728365333289801219433)
  ·
    refine ⟨5651046273999967350914575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7534728365333289801219433 5651046273999967350914575)
    ·
      refine ⟨8476569410999951026371863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5651046273999967350914575 8476569410999951026371863)
      ·
        refine ⟨12714854116499926539557795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8476569410999951026371863 12714854116499926539557795)
        ·
          refine ⟨19072281174749889809336693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12714854116499926539557795 19072281174749889809336693)
          ·
            refine ⟨1788026360132802169625315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19072281174749889809336693 1788026360132802169625315)
            ·
              refine ⟨2682039540199203254437973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788026360132802169625315 2682039540199203254437973)
              ·
                refine ⟨31430150861709413137945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2682039540199203254437973 31430150861709413137945)
                ·
                  rfl

theorem cell23_1652670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 8].length) (baseStart_1652670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652670 prefixEnd_1652670 := by exact prefixLift 1652670
  have htrace : WordTrace (prefixWord ++ tailWord_1652670) baseStart_1652670 baseEnd_1652670 := by
    simpa [prefixWord, tailWord_1652670, baseEnd_1652670] using wordTrace_append hprefix tailTrace_1652670
  have hstable : (prefixWord ++ tailWord_1652670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652670).length < 2 ^ (prefixWord ++ tailWord_1652670).sum := by decide
  have hdescent : baseEnd_1652670 < baseStart_1652670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652680 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 1, 3, 3]
def baseStart_1652680 : Nat := 118140960795 + 1652680 * 2 ^ 59
def prefixEnd_1652680 : Nat := 4983230072969 + 3 ^ 40 * 1652680 * 2
def baseEnd_1652680 : Nat := 848619208072699115599469

theorem tailTrace_1652680 : CollatzResearch.WordTrace tailWord_1652680 prefixEnd_1652680 848619208072699115599469 := by
  unfold tailWord_1652680
  simp only [CollatzResearch.WordTrace]
  refine ⟨30139095826315045058809747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40185461101753393411746329 30139095826315045058809747)
  ·
    refine ⟨45208643739472567588214621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30139095826315045058809747 45208643739472567588214621)
    ·
      refine ⟨16953241402302212845580483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45208643739472567588214621 16953241402302212845580483)
      ·
        refine ⟨25429862103453319268370725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16953241402302212845580483 25429862103453319268370725)
        ·
          refine ⟨4768099144397497362819511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25429862103453319268370725 4768099144397497362819511)
          ·
            refine ⟨7152148716596246044229267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4768099144397497362819511 7152148716596246044229267)
            ·
              refine ⟨10728223074894369066343901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7152148716596246044229267 10728223074894369066343901)
              ·
                refine ⟨4023083653085388399878963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10728223074894369066343901 4023083653085388399878963)
                ·
                  refine ⟨6034625479628082599818445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4023083653085388399878963 6034625479628082599818445)
                  ·
                    refine ⟨2262984554860530974931917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6034625479628082599818445 2262984554860530974931917)
                    ·
                      refine ⟨848619208072699115599469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2262984554860530974931917 848619208072699115599469)
                      ·
                        rfl

theorem cell23_1652680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 1, 3, 3].length) (baseStart_1652680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652680 prefixEnd_1652680 := by exact prefixLift 1652680
  have htrace : WordTrace (prefixWord ++ tailWord_1652680) baseStart_1652680 baseEnd_1652680 := by
    simpa [prefixWord, tailWord_1652680, baseEnd_1652680] using wordTrace_append hprefix tailTrace_1652680
  have hstable : (prefixWord ++ tailWord_1652680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652680).length < 2 ^ (prefixWord ++ tailWord_1652680).sum := by decide
  have hdescent : baseEnd_1652680 < baseStart_1652680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652701 : List Nat := [1, 4, 3, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_1652701 : Nat := 118140960795 + 1652701 * 2 ^ 59
def prefixEnd_1652701 : Nat := 4983230072969 + 3 ^ 40 * 1652701 * 2
def baseEnd_1652701 : Nat := 848629991166443533436873

theorem tailTrace_1652701 : CollatzResearch.WordTrace tailWord_1652701 prefixEnd_1652701 848629991166443533436873 := by
  unfold tailWord_1652701
  simp only [CollatzResearch.WordTrace]
  refine ⟨60278957585554010704133957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40185971723702673802755971 60278957585554010704133957)
  ·
    refine ⟨11302304547291377007025117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60278957585554010704133957 11302304547291377007025117)
    ·
      refine ⟨4238364205234266377634419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11302304547291377007025117 4238364205234266377634419)
      ·
        refine ⟨6357546307851399566451629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4238364205234266377634419 6357546307851399566451629)
        ·
          refine ⟨2384079865444274837419361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6357546307851399566451629 2384079865444274837419361)
          ·
            refine ⟨1788059899083206128064521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2384079865444274837419361 1788059899083206128064521)
            ·
              refine ⟨1341044924312404596048391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788059899083206128064521 1341044924312404596048391)
              ·
                refine ⟨2011567386468606894072587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341044924312404596048391 2011567386468606894072587)
                ·
                  refine ⟨3017351079702910341108881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2011567386468606894072587 3017351079702910341108881)
                  ·
                    refine ⟨2263013309777182755831661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3017351079702910341108881 2263013309777182755831661)
                    ·
                      refine ⟨848629991166443533436873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2263013309777182755831661 848629991166443533436873)
                      ·
                        rfl

theorem cell23_1652701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_1652701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652701 prefixEnd_1652701 := by exact prefixLift 1652701
  have htrace : WordTrace (prefixWord ++ tailWord_1652701) baseStart_1652701 baseEnd_1652701 := by
    simpa [prefixWord, tailWord_1652701, baseEnd_1652701] using wordTrace_append hprefix tailTrace_1652701
  have hstable : (prefixWord ++ tailWord_1652701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652701).length < 2 ^ (prefixWord ++ tailWord_1652701).sum := by decide
  have hdescent : baseEnd_1652701 < baseStart_1652701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652720 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 3, 4, 2]
def baseStart_1652720 : Nat := 118140960795 + 1652720 * 2 ^ 59
def prefixEnd_1652720 : Nat := 4983230072969 + 3 ^ 40 * 1652720 * 2
def baseEnd_1652720 : Nat := 848639747298878959099285

theorem tailTrace_1652720 : CollatzResearch.WordTrace tailWord_1652720 prefixEnd_1652720 848639747298878959099285 := by
  unfold tailWord_1652720
  simp only [CollatzResearch.WordTrace]
  refine ⟨30139825286242588474537807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40186433714990117966050409 30139825286242588474537807)
  ·
    refine ⟨45209737929363882711806711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30139825286242588474537807 45209737929363882711806711)
    ·
      refine ⟨67814606894045824067710067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45209737929363882711806711 67814606894045824067710067)
      ·
        refine ⟨101721910341068736101565101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67814606894045824067710067 101721910341068736101565101)
        ·
          refine ⟨38145716377900776038086913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101721910341068736101565101 38145716377900776038086913)
          ·
            refine ⟨28609287283425582028565185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38145716377900776038086913 28609287283425582028565185)
            ·
              refine ⟨21456965462569186521423889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28609287283425582028565185 21456965462569186521423889)
              ·
                refine ⟨16092724096926889891067917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21456965462569186521423889 16092724096926889891067917)
                ·
                  refine ⟨6034771536347583709150469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16092724096926889891067917 6034771536347583709150469)
                  ·
                    refine ⟨1131519663065171945465713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6034771536347583709150469 1131519663065171945465713)
                    ·
                      refine ⟨848639747298878959099285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1131519663065171945465713 848639747298878959099285)
                      ·
                        rfl

theorem cell23_1652720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 3, 4, 2].length) (baseStart_1652720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652720 prefixEnd_1652720 := by exact prefixLift 1652720
  have htrace : WordTrace (prefixWord ++ tailWord_1652720) baseStart_1652720 baseEnd_1652720 := by
    simpa [prefixWord, tailWord_1652720, baseEnd_1652720] using wordTrace_append hprefix tailTrace_1652720
  have hstable : (prefixWord ++ tailWord_1652720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652720).length < 2 ^ (prefixWord ++ tailWord_1652720).sum := by decide
  have hdescent : baseEnd_1652720 < baseStart_1652720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652723 : List Nat := [1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 3]
def baseStart_1652723 : Nat := 118140960795 + 1652723 * 2 ^ 59
def prefixEnd_1652723 : Nat := 4983230072969 + 3 ^ 40 * 1652723 * 2
def baseEnd_1652723 : Nat := 848641287740842447361771

theorem tailTrace_1652723 : CollatzResearch.WordTrace tailWord_1652723 prefixEnd_1652723 848641287740842447361771 := by
  unfold tailWord_1652723
  simp only [CollatzResearch.WordTrace]
  refine ⟨60279759991474308461434823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40186506660982872307623215 60279759991474308461434823)
  ·
    refine ⟨90419639987211462692152235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60279759991474308461434823 90419639987211462692152235)
    ·
      refine ⟨135629459980817194038228353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90419639987211462692152235 135629459980817194038228353)
      ·
        refine ⟨101722094985612895528671265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135629459980817194038228353 101722094985612895528671265)
        ·
          refine ⟨76291571239209671646503449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101722094985612895528671265 76291571239209671646503449)
          ·
            refine ⟨57218678429407253734877587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76291571239209671646503449 57218678429407253734877587)
            ·
              refine ⟨85828017644110880602316381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57218678429407253734877587 85828017644110880602316381)
              ·
                refine ⟨32185506616541580225868643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85828017644110880602316381 32185506616541580225868643)
                ·
                  refine ⟨48278259924812370338802965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32185506616541580225868643 48278259924812370338802965)
                  ·
                    refine ⟨2263043433975579859631389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48278259924812370338802965 2263043433975579859631389)
                    ·
                      refine ⟨848641287740842447361771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2263043433975579859631389 848641287740842447361771)
                      ·
                        rfl

theorem cell23_1652723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 6, 3].length) (baseStart_1652723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652723 prefixEnd_1652723 := by exact prefixLift 1652723
  have htrace : WordTrace (prefixWord ++ tailWord_1652723) baseStart_1652723 baseEnd_1652723 := by
    simpa [prefixWord, tailWord_1652723, baseEnd_1652723] using wordTrace_append hprefix tailTrace_1652723
  have hstable : (prefixWord ++ tailWord_1652723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652723).length < 2 ^ (prefixWord ++ tailWord_1652723).sum := by decide
  have hdescent : baseEnd_1652723 < baseStart_1652723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652749 : List Nat := [1, 7, 1, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_1652749 : Nat := 118140960795 + 1652749 * 2 ^ 59
def prefixEnd_1652749 : Nat := 4983230072969 + 3 ^ 40 * 1652749 * 2
def baseEnd_1652749 : Nat := 848654638237859345636653

theorem tailTrace_1652749 : CollatzResearch.WordTrace tailWord_1652749 prefixEnd_1652749 848654638237859345636653 := by
  unfold tailWord_1652749
  simp only [CollatzResearch.WordTrace]
  refine ⟨60280708289380114901881301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40187138859586743267920867 60280708289380114901881301)
  ·
    refine ⟨1412829100532346443012843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 60280708289380114901881301 1412829100532346443012843)
    ·
      refine ⟨2119243650798519664519265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1412829100532346443012843 2119243650798519664519265)
      ·
        refine ⟨1589432738098889748389449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2119243650798519664519265 1589432738098889748389449)
        ·
          refine ⟨1192074553574167311292087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1589432738098889748389449 1192074553574167311292087)
          ·
            refine ⟨1788111830361250966938131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192074553574167311292087 1788111830361250966938131)
            ·
              refine ⟨2682167745541876450407197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788111830361250966938131 2682167745541876450407197)
              ·
                refine ⟨1005812904578203668902699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2682167745541876450407197 1005812904578203668902699)
                ·
                  refine ⟨1508719356867305503354049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005812904578203668902699 1508719356867305503354049)
                  ·
                    refine ⟨1131539517650479127515537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1508719356867305503354049 1131539517650479127515537)
                    ·
                      refine ⟨848654638237859345636653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1131539517650479127515537 848654638237859345636653)
                      ·
                        rfl

theorem cell23_1652749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_1652749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652749 prefixEnd_1652749 := by exact prefixLift 1652749
  have htrace : WordTrace (prefixWord ++ tailWord_1652749) baseStart_1652749 baseEnd_1652749 := by
    simpa [prefixWord, tailWord_1652749, baseEnd_1652749] using wordTrace_append hprefix tailTrace_1652749
  have hstable : (prefixWord ++ tailWord_1652749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652749).length < 2 ^ (prefixWord ++ tailWord_1652749).sum := by decide
  have hdescent : baseEnd_1652749 < baseStart_1652749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652788 : List Nat := [2, 5, 1, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_1652788 : Nat := 118140960795 + 1652788 * 2 ^ 59
def prefixEnd_1652788 : Nat := 4983230072969 + 3 ^ 40 * 1652788 * 2
def baseEnd_1652788 : Nat := 848674663983384693048973

theorem tailTrace_1652788 : CollatzResearch.WordTrace tailWord_1652788 prefixEnd_1652788 848674663983384693048973 := by
  unfold tailWord_1652788
  simp only [CollatzResearch.WordTrace]
  refine ⟨30141065368119412281275509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40188087157492549708367345 30141065368119412281275509)
  ·
    refine ⟨2825724878261194901369579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30141065368119412281275509 2825724878261194901369579)
    ·
      refine ⟨4238587317391792352054369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2825724878261194901369579 4238587317391792352054369)
      ·
        refine ⟨3178940488043844264040777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4238587317391792352054369 3178940488043844264040777)
        ·
          refine ⟨2384205366032883198030583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3178940488043844264040777 2384205366032883198030583)
          ·
            refine ⟨3576308049049324797045875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384205366032883198030583 3576308049049324797045875)
            ·
              refine ⟨5364462073573987195568813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3576308049049324797045875 5364462073573987195568813)
              ·
                refine ⟨2011673277590245198338305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5364462073573987195568813 2011673277590245198338305)
                ·
                  refine ⟨1508754958192683898753729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2011673277590245198338305 1508754958192683898753729)
                  ·
                    refine ⟨1131566218644512924065297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1508754958192683898753729 1131566218644512924065297)
                    ·
                      refine ⟨848674663983384693048973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1131566218644512924065297 848674663983384693048973)
                      ·
                        rfl

theorem cell23_1652788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_1652788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652788 prefixEnd_1652788 := by exact prefixLift 1652788
  have htrace : WordTrace (prefixWord ++ tailWord_1652788) baseStart_1652788 baseEnd_1652788 := by
    simpa [prefixWord, tailWord_1652788, baseEnd_1652788] using wordTrace_append hprefix tailTrace_1652788
  have hstable : (prefixWord ++ tailWord_1652788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652788).length < 2 ^ (prefixWord ++ tailWord_1652788).sum := by decide
  have hdescent : baseEnd_1652788 < baseStart_1652788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652854 : List Nat := [5, 1, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_1652854 : Nat := 118140960795 + 1652854 * 2 ^ 59
def prefixEnd_1652854 : Nat := 4983230072969 + 3 ^ 40 * 1652854 * 2
def baseEnd_1652854 : Nat := 282902851235527144941223

theorem tailTrace_1652854 : CollatzResearch.WordTrace tailWord_1652854 prefixEnd_1652854 282902851235527144941223 := by
  unfold tailWord_1652854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3767783622124982364653351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40189691969333145222969077 3767783622124982364653351)
  ·
    refine ⟨5651675433187473546980027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3767783622124982364653351 5651675433187473546980027)
    ·
      refine ⟨8477513149781210320470041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5651675433187473546980027 8477513149781210320470041)
      ·
        refine ⟨6358134862335907740352531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8477513149781210320470041 6358134862335907740352531)
        ·
          refine ⟨9537202293503861610528797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6358134862335907740352531 9537202293503861610528797)
          ·
            refine ⟨3576450860063948103948299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9537202293503861610528797 3576450860063948103948299)
            ·
              refine ⟨5364676290095922155922449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3576450860063948103948299 5364676290095922155922449)
              ·
                refine ⟨4023507217571941616941837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5364676290095922155922449 4023507217571941616941837)
                ·
                  refine ⟨1508815206589478106353189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4023507217571941616941837 1508815206589478106353189)
                  ·
                    refine ⟨282902851235527144941223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1508815206589478106353189 282902851235527144941223)
                    ·
                      rfl

theorem cell23_1652854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_1652854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652854 prefixEnd_1652854 := by exact prefixLift 1652854
  have htrace : WordTrace (prefixWord ++ tailWord_1652854) baseStart_1652854 baseEnd_1652854 := by
    simpa [prefixWord, tailWord_1652854, baseEnd_1652854] using wordTrace_append hprefix tailTrace_1652854
  have hstable : (prefixWord ++ tailWord_1652854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652854).length < 2 ^ (prefixWord ++ tailWord_1652854).sum := by decide
  have hdescent : baseEnd_1652854 < baseStart_1652854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652884 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 8]
def baseStart_1652884 : Nat := 118140960795 + 1652884 * 2 ^ 59
def prefixEnd_1652884 : Nat := 4983230072969 + 3 ^ 40 * 1652884 * 2
def baseEnd_1652884 : Nat := 94302662014024035272059

theorem tailTrace_1652884 : CollatzResearch.WordTrace tailWord_1652884 prefixEnd_1652884 94302662014024035272059 := by
  unfold tailWord_1652884
  simp only [CollatzResearch.WordTrace]
  refine ⟨30142816071945516479022853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40190421429260688638697137 30142816071945516479022853)
  ·
    refine ⟨5651778013489784339816785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30142816071945516479022853 5651778013489784339816785)
    ·
      refine ⟨4238833510117338254862589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5651778013489784339816785 4238833510117338254862589)
      ·
        refine ⟨1589562566294001845573471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4238833510117338254862589 1589562566294001845573471)
        ·
          refine ⟨2384343849441002768360207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589562566294001845573471 2384343849441002768360207)
          ·
            refine ⟨3576515774161504152540311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384343849441002768360207 3576515774161504152540311)
            ·
              refine ⟨5364773661242256228810467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3576515774161504152540311 5364773661242256228810467)
              ·
                refine ⟨8047160491863384343215701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5364773661242256228810467 8047160491863384343215701)
                ·
                  refine ⟨94302662014024035272059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8047160491863384343215701 94302662014024035272059)
                  ·
                    rfl

theorem cell23_1652884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_1652884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652884 prefixEnd_1652884 := by exact prefixLift 1652884
  have htrace : WordTrace (prefixWord ++ tailWord_1652884) baseStart_1652884 baseEnd_1652884 := by
    simpa [prefixWord, tailWord_1652884, baseEnd_1652884] using wordTrace_append hprefix tailTrace_1652884
  have hstable : (prefixWord ++ tailWord_1652884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652884).length < 2 ^ (prefixWord ++ tailWord_1652884).sum := by decide
  have hdescent : baseEnd_1652884 < baseStart_1652884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652920 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 3, 1, 5]
def baseStart_1652920 : Nat := 118140960795 + 1652920 * 2 ^ 59
def prefixEnd_1652920 : Nat := 4983230072969 + 3 ^ 40 * 1652920 * 2
def baseEnd_1652920 : Nat := 848742443429778176598365

theorem tailTrace_1652920 : CollatzResearch.WordTrace tailWord_1652920 prefixEnd_1652920 848742443429778176598365 := by
  unfold tailWord_1652920
  simp only [CollatzResearch.WordTrace]
  refine ⟨30143472585880305553178107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40191296781173740737570809 30143472585880305553178107)
  ·
    refine ⟨45215208878820458329767161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30143472585880305553178107 45215208878820458329767161)
    ·
      refine ⟨33911406659115343747325371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45215208878820458329767161 33911406659115343747325371)
      ·
        refine ⟨50867109988673015620988057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33911406659115343747325371 50867109988673015620988057)
        ·
          refine ⟨38150332491504761715741043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50867109988673015620988057 38150332491504761715741043)
          ·
            refine ⟨57225498737257142573611565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38150332491504761715741043 57225498737257142573611565)
            ·
              refine ⟨21459562026471428465104337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57225498737257142573611565 21459562026471428465104337)
              ·
                refine ⟨16094671519853571348828253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21459562026471428465104337 16094671519853571348828253)
                ·
                  refine ⟨6035501819945089255810595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16094671519853571348828253 6035501819945089255810595)
                  ·
                    refine ⟨9053252729917633883715893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6035501819945089255810595 9053252729917633883715893)
                    ·
                      refine ⟨848742443429778176598365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9053252729917633883715893 848742443429778176598365)
                      ·
                        rfl

theorem cell23_1652920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 3, 1, 5].length) (baseStart_1652920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652920 prefixEnd_1652920 := by exact prefixLift 1652920
  have htrace : WordTrace (prefixWord ++ tailWord_1652920) baseStart_1652920 baseEnd_1652920 := by
    simpa [prefixWord, tailWord_1652920, baseEnd_1652920] using wordTrace_append hprefix tailTrace_1652920
  have hstable : (prefixWord ++ tailWord_1652920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652920).length < 2 ^ (prefixWord ++ tailWord_1652920).sum := by decide
  have hdescent : baseEnd_1652920 < baseStart_1652920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652928 : List Nat := [2, 1, 1, 2, 5, 3, 1, 3, 1, 1, 3]
def baseStart_1652928 : Nat := 118140960795 + 1652928 * 2 ^ 59
def prefixEnd_1652928 : Nat := 4983230072969 + 3 ^ 40 * 1652928 * 2
def baseEnd_1652928 : Nat := 848746551275014145298329

theorem tailTrace_1652928 : CollatzResearch.WordTrace tailWord_1652928 prefixEnd_1652928 848746551275014145298329 := by
  unfold tailWord_1652928
  simp only [CollatzResearch.WordTrace]
  refine ⟨30143618477865814236323719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40191491303821085648431625 30143618477865814236323719)
  ·
    refine ⟨45215427716798721354485579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30143618477865814236323719 45215427716798721354485579)
    ·
      refine ⟨67823141575198082031728369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45215427716798721354485579 67823141575198082031728369)
      ·
        refine ⟨50867356181398561523796277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67823141575198082031728369 50867356181398561523796277)
        ·
          refine ⟨4768814642006115142855901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50867356181398561523796277 4768814642006115142855901)
          ·
            refine ⟨1788305490752293178570963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4768814642006115142855901 1788305490752293178570963)
            ·
              refine ⟨2682458236128439767856445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788305490752293178570963 2682458236128439767856445)
              ·
                refine ⟨1005921838548164912946167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2682458236128439767856445 1005921838548164912946167)
                ·
                  refine ⟨1508882757822247369419251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005921838548164912946167 1508882757822247369419251)
                  ·
                    refine ⟨2263324136733371054128877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1508882757822247369419251 2263324136733371054128877)
                    ·
                      refine ⟨848746551275014145298329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2263324136733371054128877 848746551275014145298329)
                      ·
                        rfl

theorem cell23_1652928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 1, 1, 3].length) (baseStart_1652928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652928 prefixEnd_1652928 := by exact prefixLift 1652928
  have htrace : WordTrace (prefixWord ++ tailWord_1652928) baseStart_1652928 baseEnd_1652928 := by
    simpa [prefixWord, tailWord_1652928, baseEnd_1652928] using wordTrace_append hprefix tailTrace_1652928
  have hstable : (prefixWord ++ tailWord_1652928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652928).length < 2 ^ (prefixWord ++ tailWord_1652928).sum := by decide
  have hdescent : baseEnd_1652928 < baseStart_1652928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652957 : List Nat := [1, 4, 3, 2, 1, 1, 1, 10]
def baseStart_1652957 : Nat := 118140960795 + 1652957 * 2 ^ 59
def prefixEnd_1652957 : Nat := 4983230072969 + 3 ^ 40 * 1652957 * 2
def baseEnd_1652957 : Nat := 31435608970888686364285

theorem tailTrace_1652957 : CollatzResearch.WordTrace tailWord_1652957 prefixEnd_1652957 31435608970888686364285 := by
  unfold tailWord_1652957
  simp only [CollatzResearch.WordTrace]
  refine ⟨60288294672626566425453125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40192196448417710950302083 60288294672626566425453125)
  ·
    refine ⟨11304055251117481204772461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60288294672626566425453125 11304055251117481204772461)
    ·
      refine ⟨4239020719169055451789673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11304055251117481204772461 4239020719169055451789673)
      ·
        refine ⟨3179265539376791588842255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4239020719169055451789673 3179265539376791588842255)
        ·
          refine ⟨4768898309065187383263383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3179265539376791588842255 4768898309065187383263383)
          ·
            refine ⟨7153347463597781074895075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4768898309065187383263383 7153347463597781074895075)
            ·
              refine ⟨10730021195396671612342613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7153347463597781074895075 10730021195396671612342613)
              ·
                refine ⟨31435608970888686364285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10730021195396671612342613 31435608970888686364285)
                ·
                  rfl

theorem cell23_1652957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 10].length) (baseStart_1652957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652957 prefixEnd_1652957 := by exact prefixLift 1652957
  have htrace : WordTrace (prefixWord ++ tailWord_1652957) baseStart_1652957 baseEnd_1652957 := by
    simpa [prefixWord, tailWord_1652957, baseEnd_1652957] using wordTrace_append hprefix tailTrace_1652957
  have hstable : (prefixWord ++ tailWord_1652957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652957).length < 2 ^ (prefixWord ++ tailWord_1652957).sum := by decide
  have hdescent : baseEnd_1652957 < baseStart_1652957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1652960 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 6]
def baseStart_1652960 : Nat := 118140960795 + 1652960 * 2 ^ 59
def prefixEnd_1652960 : Nat := 4983230072969 + 3 ^ 40 * 1652960 * 2
def baseEnd_1652960 : Nat := 848762982655958020098181

theorem tailTrace_1652960 : CollatzResearch.WordTrace tailWord_1652960 prefixEnd_1652960 848762982655958020098181 := by
  unfold tailWord_1652960
  simp only [CollatzResearch.WordTrace]
  refine ⟨30144202045807848968906167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40192269394410465291874889 30144202045807848968906167)
  ·
    refine ⟨45216303068711773453359251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30144202045807848968906167 45216303068711773453359251)
    ·
      refine ⟨67824454603067660180038877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45216303068711773453359251 67824454603067660180038877)
      ·
        refine ⟨25434170476150372567514579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67824454603067660180038877 25434170476150372567514579)
        ·
          refine ⟨38151255714225558851271869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25434170476150372567514579 38151255714225558851271869)
          ·
            refine ⟨14306720892834584569226951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38151255714225558851271869 14306720892834584569226951)
            ·
              refine ⟨21460081339251876853840427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14306720892834584569226951 21460081339251876853840427)
              ·
                refine ⟨32190122008877815280760641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21460081339251876853840427 32190122008877815280760641)
                ·
                  refine ⟨24142591506658361460570481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32190122008877815280760641 24142591506658361460570481)
                  ·
                    refine ⟨18106943629993771095427861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24142591506658361460570481 18106943629993771095427861)
                    ·
                      refine ⟨848762982655958020098181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18106943629993771095427861 848762982655958020098181)
                      ·
                        rfl

theorem cell23_1652960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_1652960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1652960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1652960 prefixEnd_1652960 := by exact prefixLift 1652960
  have htrace : WordTrace (prefixWord ++ tailWord_1652960) baseStart_1652960 baseEnd_1652960 := by
    simpa [prefixWord, tailWord_1652960, baseEnd_1652960] using wordTrace_append hprefix tailTrace_1652960
  have hstable : (prefixWord ++ tailWord_1652960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1652960).length < 2 ^ (prefixWord ++ tailWord_1652960).sum := by decide
  have hdescent : baseEnd_1652960 < baseStart_1652960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1652960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653001 : List Nat := [1, 2, 1, 1, 3, 5, 2, 2, 2, 1, 3]
def baseStart_1653001 : Nat := 118140960795 + 1653001 * 2 ^ 59
def prefixEnd_1653001 : Nat := 4983230072969 + 3 ^ 40 * 1653001 * 2
def baseEnd_1653001 : Nat := 848784035362792359685493

theorem tailTrace_1653001 : CollatzResearch.WordTrace tailWord_1653001 prefixEnd_1653001 848784035362792359685493 := by
  unfold tailWord_1653001
  simp only [CollatzResearch.WordTrace]
  refine ⟨60289899484467161940054857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40193266322978107960036571 60289899484467161940054857)
  ·
    refine ⟨45217424613350371455041143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60289899484467161940054857 45217424613350371455041143)
    ·
      refine ⟨67826136920025557182561715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45217424613350371455041143 67826136920025557182561715)
      ·
        refine ⟨101739205380038335773842573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67826136920025557182561715 101739205380038335773842573)
        ·
          refine ⟨38152202017514375915190965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101739205380038335773842573 38152202017514375915190965)
          ·
            refine ⟨3576768939141972742049153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38152202017514375915190965 3576768939141972742049153)
            ·
              refine ⟨2682576704356479556536865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3576768939141972742049153 2682576704356479556536865)
              ·
                refine ⟨2011932528267359667402649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2682576704356479556536865 2011932528267359667402649)
                ·
                  refine ⟨1508949396200519750551987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2011932528267359667402649 1508949396200519750551987)
                  ·
                    refine ⟨2263424094300779625827981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1508949396200519750551987 2263424094300779625827981)
                    ·
                      refine ⟨848784035362792359685493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2263424094300779625827981 848784035362792359685493)
                      ·
                        rfl

theorem cell23_1653001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 2, 1, 3].length) (baseStart_1653001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653001 prefixEnd_1653001 := by exact prefixLift 1653001
  have htrace : WordTrace (prefixWord ++ tailWord_1653001) baseStart_1653001 baseEnd_1653001 := by
    simpa [prefixWord, tailWord_1653001, baseEnd_1653001] using wordTrace_append hprefix tailTrace_1653001
  have hstable : (prefixWord ++ tailWord_1653001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653001).length < 2 ^ (prefixWord ++ tailWord_1653001).sum := by decide
  have hdescent : baseEnd_1653001 < baseStart_1653001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653027 : List Nat := [1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 3]
def baseStart_1653027 : Nat := 118140960795 + 1653027 * 2 ^ 59
def prefixEnd_1653027 : Nat := 4983230072969 + 3 ^ 40 * 1653027 * 2
def baseEnd_1653027 : Nat := 848797385859809257960373

theorem tailTrace_1653027 : CollatzResearch.WordTrace tailWord_1653027 prefixEnd_1653027 848797385859809257960373 := by
  unfold tailWord_1653027
  simp only [CollatzResearch.WordTrace]
  refine ⟨60290847782372968380501335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40193898521581978920334223 60290847782372968380501335)
  ·
    refine ⟨90436271673559452570752003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60290847782372968380501335 90436271673559452570752003)
    ·
      refine ⟨135654407510339178856128005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90436271673559452570752003 135654407510339178856128005)
      ·
        refine ⟨25435201408188596035524001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135654407510339178856128005 25435201408188596035524001)
        ·
          refine ⟨19076401056141447026643001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25435201408188596035524001 19076401056141447026643001)
          ·
            refine ⟨14307300792106085269982251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19076401056141447026643001 14307300792106085269982251)
            ·
              refine ⟨21460951188159127904973377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14307300792106085269982251 21460951188159127904973377)
              ·
                refine ⟨16095713391119345928730033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21460951188159127904973377 16095713391119345928730033)
                ·
                  refine ⟨12071785043339509446547525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16095713391119345928730033 12071785043339509446547525)
                  ·
                    refine ⟨2263459695626158021227661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12071785043339509446547525 2263459695626158021227661)
                    ·
                      refine ⟨848797385859809257960373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2263459695626158021227661 848797385859809257960373)
                      ·
                        rfl

theorem cell23_1653027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_1653027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653027 prefixEnd_1653027 := by exact prefixLift 1653027
  have htrace : WordTrace (prefixWord ++ tailWord_1653027) baseStart_1653027 baseEnd_1653027 := by
    simpa [prefixWord, tailWord_1653027, baseEnd_1653027] using wordTrace_append hprefix tailTrace_1653027
  have hstable : (prefixWord ++ tailWord_1653027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653027).length < 2 ^ (prefixWord ++ tailWord_1653027).sum := by decide
  have hdescent : baseEnd_1653027 < baseStart_1653027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653054 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_1653054 : Nat := 118140960795 + 1653054 * 2 ^ 59
def prefixEnd_1653054 : Nat := 4983230072969 + 3 ^ 40 * 1653054 * 2
def baseEnd_1653054 : Nat := 848811249837480652322749

theorem tailTrace_1653054 : CollatzResearch.WordTrace tailWord_1653054 prefixEnd_1653054 848811249837480652322749 := by
  unfold tailWord_1653054
  simp only [CollatzResearch.WordTrace]
  refine ⟨7536479069159393998966777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40194555035516767994489477 7536479069159393998966777)
  ·
    refine ⟨5652359301869545499225083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7536479069159393998966777 5652359301869545499225083)
    ·
      refine ⟨8478538952804318248837625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5652359301869545499225083 8478538952804318248837625)
      ·
        refine ⟨6358904214603238686628219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8478538952804318248837625 6358904214603238686628219)
        ·
          refine ⟨9538356321904858029942329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6358904214603238686628219 9538356321904858029942329)
          ·
            refine ⟨7153767241428643522456747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9538356321904858029942329 7153767241428643522456747)
            ·
              refine ⟨10730650862142965283685121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7153767241428643522456747 10730650862142965283685121)
              ·
                refine ⟨8047988146607223962763841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10730650862142965283685121 8047988146607223962763841)
                ·
                  refine ⟨6035991109955417972072881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8047988146607223962763841 6035991109955417972072881)
                  ·
                    refine ⟨4526993332466563479054661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6035991109955417972072881 4526993332466563479054661)
                    ·
                      refine ⟨848811249837480652322749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4526993332466563479054661 848811249837480652322749)
                      ·
                        rfl

theorem cell23_1653054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_1653054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653054 prefixEnd_1653054 := by exact prefixLift 1653054
  have htrace : WordTrace (prefixWord ++ tailWord_1653054) baseStart_1653054 baseEnd_1653054 := by
    simpa [prefixWord, tailWord_1653054, baseEnd_1653054] using wordTrace_append hprefix tailTrace_1653054
  have hstable : (prefixWord ++ tailWord_1653054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653054).length < 2 ^ (prefixWord ++ tailWord_1653054).sum := by decide
  have hdescent : baseEnd_1653054 < baseStart_1653054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653064 : List Nat := [2, 1, 3, 1, 1, 2, 4, 4, 5]
def baseStart_1653064 : Nat := 118140960795 + 1653064 * 2 ^ 59
def prefixEnd_1653064 : Nat := 4983230072969 + 3 ^ 40 * 1653064 * 2
def baseEnd_1653064 : Nat := 94312931627113957021967

theorem tailTrace_1653064 : CollatzResearch.WordTrace tailWord_1653064 prefixEnd_1653064 94312931627113957021967 := by
  unfold tailWord_1653064
  simp only [CollatzResearch.WordTrace]
  refine ⟨30146098641619461849799123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40194798188825949133065497 30146098641619461849799123)
  ·
    refine ⟨45219147962429192774698685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30146098641619461849799123 45219147962429192774698685)
    ·
      refine ⟨16957180485910947290512007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45219147962429192774698685 16957180485910947290512007)
      ·
        refine ⟨25435770728866420935768011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16957180485910947290512007 25435770728866420935768011)
        ·
          refine ⟨38153656093299631403652017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25435770728866420935768011 38153656093299631403652017)
          ·
            refine ⟨28615242069974723552739013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38153656093299631403652017 28615242069974723552739013)
            ·
              refine ⟨5365357888120260666138565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28615242069974723552739013 5365357888120260666138565)
              ·
                refine ⟨1006004604022548874900981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5365357888120260666138565 1006004604022548874900981)
                ·
                  refine ⟨94312931627113957021967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1006004604022548874900981 94312931627113957021967)
                  ·
                    rfl

theorem cell23_1653064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 5].length) (baseStart_1653064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653064 prefixEnd_1653064 := by exact prefixLift 1653064
  have htrace : WordTrace (prefixWord ++ tailWord_1653064) baseStart_1653064 baseEnd_1653064 := by
    simpa [prefixWord, tailWord_1653064, baseEnd_1653064] using wordTrace_append hprefix tailTrace_1653064
  have hstable : (prefixWord ++ tailWord_1653064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653064).length < 2 ^ (prefixWord ++ tailWord_1653064).sum := by decide
  have hdescent : baseEnd_1653064 < baseStart_1653064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653074 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3]
def baseStart_1653074 : Nat := 118140960795 + 1653074 * 2 ^ 59
def prefixEnd_1653074 : Nat := 4983230072969 + 3 ^ 40 * 1653074 * 2
def baseEnd_1653074 : Nat := 848821519450570574072657

theorem tailTrace_1653074 : CollatzResearch.WordTrace tailWord_1653074 prefixEnd_1653074 848821519450570574072657 := by
  unfold tailWord_1653074
  simp only [CollatzResearch.WordTrace]
  refine ⟨15073140503300673851865569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40195041342135130271641517 15073140503300673851865569)
  ·
    refine ⟨11304855377475505388899177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15073140503300673851865569 11304855377475505388899177)
    ·
      refine ⟨8478641533106629041674383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11304855377475505388899177 8478641533106629041674383)
      ·
        refine ⟨12717962299659943562511575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8478641533106629041674383 12717962299659943562511575)
        ·
          refine ⟨19076943449489915343767363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12717962299659943562511575 19076943449489915343767363)
          ·
            refine ⟨28615415174234873015651045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19076943449489915343767363 28615415174234873015651045)
            ·
              refine ⟨5365390345169038690434571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28615415174234873015651045 5365390345169038690434571)
              ·
                refine ⟨8048085517753558035651857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5365390345169038690434571 8048085517753558035651857)
                ·
                  refine ⟨6036064138315168526738893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8048085517753558035651857 6036064138315168526738893)
                  ·
                    refine ⟨2263524051868188197527085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6036064138315168526738893 2263524051868188197527085)
                    ·
                      refine ⟨848821519450570574072657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2263524051868188197527085 848821519450570574072657)
                      ·
                        rfl

theorem cell23_1653074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_1653074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653074 prefixEnd_1653074 := by exact prefixLift 1653074
  have htrace : WordTrace (prefixWord ++ tailWord_1653074) baseStart_1653074 baseEnd_1653074 := by
    simpa [prefixWord, tailWord_1653074, baseEnd_1653074] using wordTrace_append hprefix tailTrace_1653074
  have hstable : (prefixWord ++ tailWord_1653074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653074).length < 2 ^ (prefixWord ++ tailWord_1653074).sum := by decide
  have hdescent : baseEnd_1653074 < baseStart_1653074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653097 : List Nat := [1, 2, 1, 1, 1, 3, 3, 3, 1, 3, 4]
def baseStart_1653097 : Nat := 118140960795 + 1653097 * 2 ^ 59
def prefixEnd_1653097 : Nat := 4983230072969 + 3 ^ 40 * 1653097 * 2
def baseEnd_1653097 : Nat := 848833329505623984085051

theorem tailTrace_1653097 : CollatzResearch.WordTrace tailWord_1653097 prefixEnd_1653097 848833329505623984085051 := by
  unfold tailWord_1653097
  simp only [CollatzResearch.WordTrace]
  refine ⟨60293400892119370335549545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40195600594746246890366363 60293400892119370335549545)
  ·
    refine ⟨45220050669089527751662159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60293400892119370335549545 45220050669089527751662159)
    ·
      refine ⟨67830076003634291627493239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45220050669089527751662159 67830076003634291627493239)
      ·
        refine ⟨101745114005451437441239859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67830076003634291627493239 101745114005451437441239859)
        ·
          refine ⟨152617671008177156161859789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101745114005451437441239859 152617671008177156161859789)
          ·
            refine ⟨57231626628066433560697421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152617671008177156161859789 57231626628066433560697421)
            ·
              refine ⟨21461859985524912585261533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57231626628066433560697421 21461859985524912585261533)
              ·
                refine ⟨8048197494571842219473075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21461859985524912585261533 8048197494571842219473075)
                ·
                  refine ⟨12072296241857763329209613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8048197494571842219473075 12072296241857763329209613)
                  ·
                    refine ⟨4527111090696661248453605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12072296241857763329209613 4527111090696661248453605)
                    ·
                      refine ⟨848833329505623984085051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4527111090696661248453605 848833329505623984085051)
                      ·
                        rfl

theorem cell23_1653097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_1653097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653097 prefixEnd_1653097 := by exact prefixLift 1653097
  have htrace : WordTrace (prefixWord ++ tailWord_1653097) baseStart_1653097 baseEnd_1653097 := by
    simpa [prefixWord, tailWord_1653097, baseEnd_1653097] using wordTrace_append hprefix tailTrace_1653097
  have hstable : (prefixWord ++ tailWord_1653097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653097).length < 2 ^ (prefixWord ++ tailWord_1653097).sum := by decide
  have hdescent : baseEnd_1653097 < baseStart_1653097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653098 : List Nat := [3, 1, 3, 3, 1, 3, 1, 3, 5]
def baseStart_1653098 : Nat := 118140960795 + 1653098 * 2 ^ 59
def prefixEnd_1653098 : Nat := 4983230072969 + 3 ^ 40 * 1653098 * 2
def baseEnd_1653098 : Nat := 94314871442919831130283

theorem tailTrace_1653098 : CollatzResearch.WordTrace tailWord_1653098 prefixEnd_1653098 94314871442919831130283 := by
  unfold tailWord_1653098
  simp only [CollatzResearch.WordTrace]
  refine ⟨15073359341278936876583987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40195624910077165004223965 15073359341278936876583987)
  ·
    refine ⟨22610039011918405314875981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15073359341278936876583987 22610039011918405314875981)
    ·
      refine ⟨8478764629469401993078493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22610039011918405314875981 8478764629469401993078493)
      ·
        refine ⟨3179536736051025747404435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8478764629469401993078493 3179536736051025747404435)
        ·
          refine ⟨4769305104076538621106653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3179536736051025747404435 4769305104076538621106653)
          ·
            refine ⟨1788489414028701982914995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4769305104076538621106653 1788489414028701982914995)
            ·
              refine ⟨2682734121043052974372493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788489414028701982914995 2682734121043052974372493)
              ·
                refine ⟨1006025295391144865389685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2682734121043052974372493 1006025295391144865389685)
                ·
                  refine ⟨94314871442919831130283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1006025295391144865389685 94314871442919831130283)
                  ·
                    rfl

theorem cell23_1653098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 5].length) (baseStart_1653098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653098 prefixEnd_1653098 := by exact prefixLift 1653098
  have htrace : WordTrace (prefixWord ++ tailWord_1653098) baseStart_1653098 baseEnd_1653098 := by
    simpa [prefixWord, tailWord_1653098, baseEnd_1653098] using wordTrace_append hprefix tailTrace_1653098
  have hstable : (prefixWord ++ tailWord_1653098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653098).length < 2 ^ (prefixWord ++ tailWord_1653098).sum := by decide
  have hdescent : baseEnd_1653098 < baseStart_1653098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653151 : List Nat := [1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 3]
def baseStart_1653151 : Nat := 118140960795 + 1653151 * 2 ^ 59
def prefixEnd_1653151 : Nat := 4983230072969 + 3 ^ 40 * 1653151 * 2
def baseEnd_1653151 : Nat := 848861057460966772809803

theorem tailTrace_1653151 : CollatzResearch.WordTrace tailWord_1653151 prefixEnd_1653151 848861057460966772809803 := by
  unfold tailWord_1653151
  simp only [CollatzResearch.WordTrace]
  refine ⟨60295370433923737558015307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40196913622615825038676871 60295370433923737558015307)
  ·
    refine ⟨90443055650885606337022961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60295370433923737558015307 90443055650885606337022961)
    ·
      refine ⟨67832291738164204752767221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90443055650885606337022961 67832291738164204752767221)
      ·
        refine ⟨6359277350452894195571927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67832291738164204752767221 6359277350452894195571927)
        ·
          refine ⟨9538916025679341293357891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6359277350452894195571927 9538916025679341293357891)
          ·
            refine ⟨14308374038519011940036837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9538916025679341293357891 14308374038519011940036837)
            ·
              refine ⟨2682820132222314738756907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14308374038519011940036837 2682820132222314738756907)
              ·
                refine ⟨4024230198333472108135361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2682820132222314738756907 4024230198333472108135361)
                ·
                  refine ⟨3018172648750104081101521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4024230198333472108135361 3018172648750104081101521)
                  ·
                    refine ⟨2263629486562578060826141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3018172648750104081101521 2263629486562578060826141)
                    ·
                      refine ⟨848861057460966772809803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2263629486562578060826141 848861057460966772809803)
                      ·
                        rfl

theorem cell23_1653151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_1653151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653151 prefixEnd_1653151 := by exact prefixLift 1653151
  have htrace : WordTrace (prefixWord ++ tailWord_1653151) baseStart_1653151 baseEnd_1653151 := by
    simpa [prefixWord, tailWord_1653151, baseEnd_1653151] using wordTrace_append hprefix tailTrace_1653151
  have hstable : (prefixWord ++ tailWord_1653151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653151).length < 2 ^ (prefixWord ++ tailWord_1653151).sum := by decide
  have hdescent : baseEnd_1653151 < baseStart_1653151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653175 : List Nat := [1, 1, 3, 1, 3, 5, 2, 2, 1, 4]
def baseStart_1653175 : Nat := 118140960795 + 1653175 * 2 ^ 59
def prefixEnd_1653175 : Nat := 4983230072969 + 3 ^ 40 * 1653175 * 2
def baseEnd_1653175 : Nat := 282957793665558226303231

theorem tailTrace_1653175 : CollatzResearch.WordTrace tailWord_1653175 prefixEnd_1653175 282957793665558226303231 := by
  unfold tailWord_1653175
  simp only [CollatzResearch.WordTrace]
  refine ⟨60296245785836789656888979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40197497190557859771259319 60296245785836789656888979)
  ·
    refine ⟨90444368678755184485333469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60296245785836789656888979 90444368678755184485333469)
    ·
      refine ⟨33916638254533194182000051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90444368678755184485333469 33916638254533194182000051)
      ·
        refine ⟨50874957381799791273000077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33916638254533194182000051 50874957381799791273000077)
        ·
          refine ⟨19078109018174921727375029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50874957381799791273000077 19078109018174921727375029)
          ·
            refine ⟨1788572720453898911941409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19078109018174921727375029 1788572720453898911941409)
            ·
              refine ⟨1341429540340424183956057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788572720453898911941409 1341429540340424183956057)
              ·
                refine ⟨1006072155255318137967043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1341429540340424183956057 1006072155255318137967043)
                ·
                  refine ⟨1509108232882977206950565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1006072155255318137967043 1509108232882977206950565)
                  ·
                    refine ⟨282957793665558226303231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1509108232882977206950565 282957793665558226303231)
                    ·
                      rfl

theorem cell23_1653175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 2, 1, 4].length) (baseStart_1653175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653175 prefixEnd_1653175 := by exact prefixLift 1653175
  have htrace : WordTrace (prefixWord ++ tailWord_1653175) baseStart_1653175 baseEnd_1653175 := by
    simpa [prefixWord, tailWord_1653175, baseEnd_1653175] using wordTrace_append hprefix tailTrace_1653175
  have hstable : (prefixWord ++ tailWord_1653175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653175).length < 2 ^ (prefixWord ++ tailWord_1653175).sum := by decide
  have hdescent : baseEnd_1653175 < baseStart_1653175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653202 : List Nat := [3, 2, 2, 4, 2, 1, 1, 1, 2, 2, 3]
def baseStart_1653202 : Nat := 118140960795 + 1653202 * 2 ^ 59
def prefixEnd_1653202 : Nat := 4983230072969 + 3 ^ 40 * 1653202 * 2
def baseEnd_1653202 : Nat := 848887244974346073272069

theorem tailTrace_1653202 : CollatzResearch.WordTrace tailWord_1653202 prefixEnd_1653202 848887244974346073272069 := by
  unfold tailWord_1653202
  simp only [CollatzResearch.WordTrace]
  refine ⟨15074307639184743317030465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40198153704492648845414573 15074307639184743317030465)
  ·
    refine ⟨11305730729388557487772849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15074307639184743317030465 11305730729388557487772849)
    ·
      refine ⟨8479298047041418115829637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11305730729388557487772849 8479298047041418115829637)
      ·
        refine ⟨1589868383820265896718057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8479298047041418115829637 1589868383820265896718057)
        ·
          refine ⟨1192401287865199422538543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1589868383820265896718057 1192401287865199422538543)
          ·
            refine ⟨1788601931797799133807815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192401287865199422538543 1788601931797799133807815)
            ·
              refine ⟨2682902897696698700711723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788601931797799133807815 2682902897696698700711723)
              ·
                refine ⟨4024354346545048051067585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2682902897696698700711723 4024354346545048051067585)
                ·
                  refine ⟨3018265759908786038300689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4024354346545048051067585 3018265759908786038300689)
                  ·
                    refine ⟨2263699319931589528725517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3018265759908786038300689 2263699319931589528725517)
                    ·
                      refine ⟨848887244974346073272069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2263699319931589528725517 848887244974346073272069)
                      ·
                        rfl

theorem cell23_1653202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_1653202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653202 prefixEnd_1653202 := by exact prefixLift 1653202
  have htrace : WordTrace (prefixWord ++ tailWord_1653202) baseStart_1653202 baseEnd_1653202 := by
    simpa [prefixWord, tailWord_1653202, baseEnd_1653202] using wordTrace_append hprefix tailTrace_1653202
  have hstable : (prefixWord ++ tailWord_1653202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653202).length < 2 ^ (prefixWord ++ tailWord_1653202).sum := by decide
  have hdescent : baseEnd_1653202 < baseStart_1653202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653215 : List Nat := [1, 1, 2, 3, 3, 3, 2, 3, 1, 1, 3]
def baseStart_1653215 : Nat := 118140960795 + 1653215 * 2 ^ 59
def prefixEnd_1653215 : Nat := 4983230072969 + 3 ^ 40 * 1653215 * 2
def baseEnd_1653215 : Nat := 848893920222854522409509

theorem tailTrace_1653215 : CollatzResearch.WordTrace tailWord_1653215 prefixEnd_1653215 848893920222854522409509 := by
  unfold tailWord_1653215
  simp only [CollatzResearch.WordTrace]
  refine ⟨60297704705691876488345099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40198469803794584325563399 60297704705691876488345099)
  ·
    refine ⟨90446557058537814732517649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60297704705691876488345099 90446557058537814732517649)
    ·
      refine ⟨67834917793903361049388237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90446557058537814732517649 67834917793903361049388237)
      ·
        refine ⟨25438094172713760393520589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67834917793903361049388237 25438094172713760393520589)
        ·
          refine ⟨9539285314767660147570221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25438094172713760393520589 9539285314767660147570221)
          ·
            refine ⟨3577231993037872555338833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9539285314767660147570221 3577231993037872555338833)
            ·
              refine ⟨2682923994778404416504125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3577231993037872555338833 2682923994778404416504125)
              ·
                refine ⟨1006096498041901656189047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2682923994778404416504125 1006096498041901656189047)
                ·
                  refine ⟨1509144747062852484283571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1006096498041901656189047 1509144747062852484283571)
                  ·
                    refine ⟨2263717120594278726425357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1509144747062852484283571 2263717120594278726425357)
                    ·
                      refine ⟨848893920222854522409509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2263717120594278726425357 848893920222854522409509)
                      ·
                        rfl

theorem cell23_1653215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_1653215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653215 prefixEnd_1653215 := by exact prefixLift 1653215
  have htrace : WordTrace (prefixWord ++ tailWord_1653215) baseStart_1653215 baseEnd_1653215 := by
    simpa [prefixWord, tailWord_1653215, baseEnd_1653215] using wordTrace_append hprefix tailTrace_1653215
  have hstable : (prefixWord ++ tailWord_1653215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653215).length < 2 ^ (prefixWord ++ tailWord_1653215).sum := by decide
  have hdescent : baseEnd_1653215 < baseStart_1653215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653227 : List Nat := [1, 1, 1, 1, 2, 3, 14]
def baseStart_1653227 : Nat := 118140960795 + 1653227 * 2 ^ 59
def prefixEnd_1653227 : Nat := 4983230072969 + 3 ^ 40 * 1653227 * 2
def baseEnd_1653227 : Nat := 10480247925811215746413

theorem tailTrace_1653227 : CollatzResearch.WordTrace tailWord_1653227 prefixEnd_1653227 10480247925811215746413 := by
  unfold tailWord_1653227
  simp only [CollatzResearch.WordTrace]
  refine ⟨60298142381648402537781935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40198761587765601691854623 60298142381648402537781935)
  ·
    refine ⟨90447213572472603806672903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60298142381648402537781935 90447213572472603806672903)
    ·
      refine ⟨135670820358708905710009355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90447213572472603806672903 135670820358708905710009355)
      ·
        refine ⟨203506230538063358565014033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135670820358708905710009355 203506230538063358565014033)
        ·
          refine ⟨152629672903547518923760525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203506230538063358565014033 152629672903547518923760525)
          ·
            refine ⟨57236127338830319596410197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152629672903547518923760525 57236127338830319596410197)
            ·
              refine ⟨10480247925811215746413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 57236127338830319596410197 10480247925811215746413)
              ·
                rfl

theorem cell23_1653227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 14].length) (baseStart_1653227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653227 prefixEnd_1653227 := by exact prefixLift 1653227
  have htrace : WordTrace (prefixWord ++ tailWord_1653227) baseStart_1653227 baseEnd_1653227 := by
    simpa [prefixWord, tailWord_1653227, baseEnd_1653227] using wordTrace_append hprefix tailTrace_1653227
  have hstable : (prefixWord ++ tailWord_1653227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653227).length < 2 ^ (prefixWord ++ tailWord_1653227).sum := by decide
  have hdescent : baseEnd_1653227 < baseStart_1653227 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653258 : List Nat := [3, 1, 2, 2, 2, 1, 4, 2, 1, 2, 3]
def baseStart_1653258 : Nat := 118140960795 + 1653258 * 2 ^ 59
def prefixEnd_1653258 : Nat := 4983230072969 + 3 ^ 40 * 1653258 * 2
def baseEnd_1653258 : Nat := 848915999890997854171811

theorem tailTrace_1653258 : CollatzResearch.WordTrace tailWord_1653258 prefixEnd_1653258 848915999890997854171811 := by
  unfold tailWord_1653258
  simp only [CollatzResearch.WordTrace]
  refine ⟨15074818261134023708040107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40199515363024063221440285 15074818261134023708040107)
  ·
    refine ⟨22612227391701035562060161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15074818261134023708040107 22612227391701035562060161)
    ·
      refine ⟨16959170543775776671545121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22612227391701035562060161 16959170543775776671545121)
      ·
        refine ⟨12719377907831832503658841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16959170543775776671545121 12719377907831832503658841)
        ·
          refine ⟨9539533430873874377744131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12719377907831832503658841 9539533430873874377744131)
          ·
            refine ⟨14309300146310811566616197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9539533430873874377744131 14309300146310811566616197)
            ·
              refine ⟨2682993777433277168740537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14309300146310811566616197 2682993777433277168740537)
              ·
                refine ⟨2012245333074957876555403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2682993777433277168740537 2012245333074957876555403)
                ·
                  refine ⟨3018367999612436814833105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012245333074957876555403 3018367999612436814833105)
                  ·
                    refine ⟨2263775999709327611124829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3018367999612436814833105 2263775999709327611124829)
                    ·
                      refine ⟨848915999890997854171811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2263775999709327611124829 848915999890997854171811)
                      ·
                        rfl

theorem cell23_1653258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 4, 2, 1, 2, 3].length) (baseStart_1653258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653258 prefixEnd_1653258 := by exact prefixLift 1653258
  have htrace : WordTrace (prefixWord ++ tailWord_1653258) baseStart_1653258 baseEnd_1653258 := by
    simpa [prefixWord, tailWord_1653258, baseEnd_1653258] using wordTrace_append hprefix tailTrace_1653258
  have hstable : (prefixWord ++ tailWord_1653258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653258).length < 2 ^ (prefixWord ++ tailWord_1653258).sum := by decide
  have hdescent : baseEnd_1653258 < baseStart_1653258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653272 : List Nat := [2, 1, 2, 3, 3, 1, 3, 3, 1, 2, 2]
def baseStart_1653272 : Nat := 118140960795 + 1653272 * 2 ^ 59
def prefixEnd_1653272 : Nat := 4983230072969 + 3 ^ 40 * 1653272 * 2
def baseEnd_1653272 : Nat := 848923188620160799396747

theorem tailTrace_1653272 : CollatzResearch.WordTrace tailWord_1653272 prefixEnd_1653272 848923188620160799396747 := by
  unfold tailWord_1653272
  simp only [CollatzResearch.WordTrace]
  refine ⟨30149891833242687611585035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40199855777656916815446713 30149891833242687611585035)
  ·
    refine ⟨45224837749864031417377553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30149891833242687611585035 45224837749864031417377553)
    ·
      refine ⟨33918628312398023563033165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45224837749864031417377553 33918628312398023563033165)
      ·
        refine ⟨12719485617149258836137437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33918628312398023563033165 12719485617149258836137437)
        ·
          refine ⟨4769807106430972063551539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12719485617149258836137437 4769807106430972063551539)
          ·
            refine ⟨7154710659646458095327309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4769807106430972063551539 7154710659646458095327309)
            ·
              refine ⟨2683016497367421785747741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7154710659646458095327309 2683016497367421785747741)
              ·
                refine ⟨1006131186512783169655403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2683016497367421785747741 1006131186512783169655403)
                ·
                  refine ⟨1509196779769174754483105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1006131186512783169655403 1509196779769174754483105)
                  ·
                    refine ⟨1131897584826881065862329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1509196779769174754483105 1131897584826881065862329)
                    ·
                      refine ⟨848923188620160799396747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1131897584826881065862329 848923188620160799396747)
                      ·
                        rfl

theorem cell23_1653272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 3, 3, 1, 2, 2].length) (baseStart_1653272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653272 prefixEnd_1653272 := by exact prefixLift 1653272
  have htrace : WordTrace (prefixWord ++ tailWord_1653272) baseStart_1653272 baseEnd_1653272 := by
    simpa [prefixWord, tailWord_1653272, baseEnd_1653272] using wordTrace_append hprefix tailTrace_1653272
  have hstable : (prefixWord ++ tailWord_1653272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653272).length < 2 ^ (prefixWord ++ tailWord_1653272).sum := by decide
  have hdescent : baseEnd_1653272 < baseStart_1653272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653304 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 1, 8]
def baseStart_1653304 : Nat := 118140960795 + 1653304 * 2 ^ 59
def prefixEnd_1653304 : Nat := 4983230072969 + 3 ^ 40 * 1653304 * 2
def baseEnd_1653304 : Nat := 282979873333701558065533

theorem tailTrace_1653304 : CollatzResearch.WordTrace tailWord_1653304 prefixEnd_1653304 282979873333701558065533 := by
  unfold tailWord_1653304
  simp only [CollatzResearch.WordTrace]
  refine ⟨30150475401184722344167483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40200633868246296458889977 30150475401184722344167483)
  ·
    refine ⟨45225713101777083516251225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30150475401184722344167483 45225713101777083516251225)
    ·
      refine ⟨33919284826332812637188419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45225713101777083516251225 33919284826332812637188419)
      ·
        refine ⟨50878927239499218955782629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33919284826332812637188419 50878927239499218955782629)
        ·
          refine ⟨9539798857406103554209243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50878927239499218955782629 9539798857406103554209243)
          ·
            refine ⟨14309698286109155331313865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9539798857406103554209243 14309698286109155331313865)
            ·
              refine ⟨10732273714581866498485399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14309698286109155331313865 10732273714581866498485399)
              ·
                refine ⟨16098410571872799747728099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10732273714581866498485399 16098410571872799747728099)
                ·
                  refine ⟨24147615857809199621592149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16098410571872799747728099 24147615857809199621592149)
                  ·
                    refine ⟨282979873333701558065533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24147615857809199621592149 282979873333701558065533)
                    ·
                      rfl

theorem cell23_1653304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_1653304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653304 prefixEnd_1653304 := by exact prefixLift 1653304
  have htrace : WordTrace (prefixWord ++ tailWord_1653304) baseStart_1653304 baseEnd_1653304 := by
    simpa [prefixWord, tailWord_1653304, baseEnd_1653304] using wordTrace_append hprefix tailTrace_1653304
  have hstable : (prefixWord ++ tailWord_1653304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653304).length < 2 ^ (prefixWord ++ tailWord_1653304).sum := by decide
  have hdescent : baseEnd_1653304 < baseStart_1653304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653328 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 4, 2, 2]
def baseStart_1653328 : Nat := 118140960795 + 1653328 * 2 ^ 59
def prefixEnd_1653328 : Nat := 4983230072969 + 3 ^ 40 * 1653328 * 2
def baseEnd_1653328 : Nat := 848951943536812580296489

theorem tailTrace_1653328 : CollatzResearch.WordTrace tailWord_1653328 prefixEnd_1653328 848951943536812580296489 := by
  unfold tailWord_1653328
  simp only [CollatzResearch.WordTrace]
  refine ⟨30150913077141248393604319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40201217436188331191472425 30150913077141248393604319)
  ·
    refine ⟨45226369615711872590406479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30150913077141248393604319 45226369615711872590406479)
    ·
      refine ⟨67839554423567808885609719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45226369615711872590406479 67839554423567808885609719)
      ·
        refine ⟨101759331635351713328414579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67839554423567808885609719 101759331635351713328414579)
        ·
          refine ⟨152638997453027569992621869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101759331635351713328414579 152638997453027569992621869)
          ·
            refine ⟨57239624044885338747233201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152638997453027569992621869 57239624044885338747233201)
            ·
              refine ⟨42929718033664004060424901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57239624044885338747233201 42929718033664004060424901)
              ·
                refine ⟨8049322131312000761329669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42929718033664004060424901 8049322131312000761329669)
                ·
                  refine ⟨1509247899621000142749313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8049322131312000761329669 1509247899621000142749313)
                  ·
                    refine ⟨1131935924715750107061985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1509247899621000142749313 1131935924715750107061985)
                    ·
                      refine ⟨848951943536812580296489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1131935924715750107061985 848951943536812580296489)
                      ·
                        rfl

theorem cell23_1653328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 4, 2, 2].length) (baseStart_1653328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653328 prefixEnd_1653328 := by exact prefixLift 1653328
  have htrace : WordTrace (prefixWord ++ tailWord_1653328) baseStart_1653328 baseEnd_1653328 := by
    simpa [prefixWord, tailWord_1653328, baseEnd_1653328] using wordTrace_append hprefix tailTrace_1653328
  have hstable : (prefixWord ++ tailWord_1653328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653328).length < 2 ^ (prefixWord ++ tailWord_1653328).sum := by decide
  have hdescent : baseEnd_1653328 < baseStart_1653328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653332 : List Nat := [2, 4, 1, 1, 1, 4, 3, 1, 1, 3, 2]
def baseStart_1653332 : Nat := 118140960795 + 1653332 * 2 ^ 59
def prefixEnd_1653332 : Nat := 4983230072969 + 3 ^ 40 * 1653332 * 2
def baseEnd_1653332 : Nat := 848953997459430564646471

theorem tailTrace_1653332 : CollatzResearch.WordTrace tailWord_1653332 prefixEnd_1653332 848953997459430564646471 := by
  unfold tailWord_1653332
  simp only [CollatzResearch.WordTrace]
  refine ⟨30150986023134002735177125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40201314697512003646902833 30150986023134002735177125)
  ·
    refine ⟨5653309879337625512845711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30150986023134002735177125 5653309879337625512845711)
    ·
      refine ⟨8479964819006438269268567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5653309879337625512845711 8479964819006438269268567)
      ·
        refine ⟨12719947228509657403902851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8479964819006438269268567 12719947228509657403902851)
        ·
          refine ⟨19079920842764486105854277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12719947228509657403902851 19079920842764486105854277)
          ·
            refine ⟨3577485158018341144847677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19079920842764486105854277 3577485158018341144847677)
            ·
              refine ⟨1341556934256877929317879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3577485158018341144847677 1341556934256877929317879)
              ·
                refine ⟨2012335401385316893976819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341556934256877929317879 2012335401385316893976819)
                ·
                  refine ⟨3018503102077975340965229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012335401385316893976819 3018503102077975340965229)
                  ·
                    refine ⟨1131938663279240752861961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3018503102077975340965229 1131938663279240752861961)
                    ·
                      refine ⟨848953997459430564646471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1131938663279240752861961 848953997459430564646471)
                      ·
                        rfl

theorem cell23_1653332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_1653332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653332 prefixEnd_1653332 := by exact prefixLift 1653332
  have htrace : WordTrace (prefixWord ++ tailWord_1653332) baseStart_1653332 baseEnd_1653332 := by
    simpa [prefixWord, tailWord_1653332, baseEnd_1653332] using wordTrace_append hprefix tailTrace_1653332
  have hstable : (prefixWord ++ tailWord_1653332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653332).length < 2 ^ (prefixWord ++ tailWord_1653332).sum := by decide
  have hdescent : baseEnd_1653332 < baseStart_1653332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653344 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 7]
def baseStart_1653344 : Nat := 118140960795 + 1653344 * 2 ^ 59
def prefixEnd_1653344 : Nat := 4983230072969 + 3 ^ 40 * 1653344 * 2
def baseEnd_1653344 : Nat := 848960159227284517696415

theorem tailTrace_1653344 : CollatzResearch.WordTrace tailWord_1653344 prefixEnd_1653344 848960159227284517696415 := by
  unfold tailWord_1653344
  simp only [CollatzResearch.WordTrace]
  refine ⟨30151204861112265759895543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40201606481483021013194057 30151204861112265759895543)
  ·
    refine ⟨45226807291668398639843315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30151204861112265759895543 45226807291668398639843315)
    ·
      refine ⟨67840210937502597959764973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45226807291668398639843315 67840210937502597959764973)
      ·
        refine ⟨25440079101563474234911865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67840210937502597959764973 25440079101563474234911865)
        ·
          refine ⟨19080059326172605676183899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25440079101563474234911865 19080059326172605676183899)
          ·
            refine ⟨28620088989258908514275849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19080059326172605676183899 28620088989258908514275849)
            ·
              refine ⟨21465066741944181385706887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28620088989258908514275849 21465066741944181385706887)
              ·
                refine ⟨32197600112916272078560331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21465066741944181385706887 32197600112916272078560331)
                ·
                  refine ⟨48296400169374408117840497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32197600112916272078560331 48296400169374408117840497)
                  ·
                    refine ⟨36222300127030806088380373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48296400169374408117840497 36222300127030806088380373)
                    ·
                      refine ⟨848960159227284517696415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36222300127030806088380373 848960159227284517696415)
                      ·
                        rfl

theorem cell23_1653344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_1653344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653344 prefixEnd_1653344 := by exact prefixLift 1653344
  have htrace : WordTrace (prefixWord ++ tailWord_1653344) baseStart_1653344 baseEnd_1653344 := by
    simpa [prefixWord, tailWord_1653344, baseEnd_1653344] using wordTrace_append hprefix tailTrace_1653344
  have hstable : (prefixWord ++ tailWord_1653344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653344).length < 2 ^ (prefixWord ++ tailWord_1653344).sum := by decide
  have hdescent : baseEnd_1653344 < baseStart_1653344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653345 : List Nat := [1, 2, 3, 1, 1, 4, 1, 4, 2, 2, 2]
def baseStart_1653345 : Nat := 118140960795 + 1653345 * 2 ^ 59
def prefixEnd_1653345 : Nat := 4983230072969 + 3 ^ 40 * 1653345 * 2
def baseEnd_1653345 : Nat := 848960672707939013783911

theorem tailTrace_1653345 : CollatzResearch.WordTrace tailWord_1653345 prefixEnd_1653345 848960672707939013783911 := by
  unfold tailWord_1653345
  simp only [CollatzResearch.WordTrace]
  refine ⟨60302446195220908690577489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40201630796813939127051659 60302446195220908690577489)
  ·
    refine ⟨45226834646415681517933117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60302446195220908690577489 45226834646415681517933117)
    ·
      refine ⟨16960062992405880569224919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45226834646415681517933117 16960062992405880569224919)
      ·
        refine ⟨25440094488608820853837379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16960062992405880569224919 25440094488608820853837379)
        ·
          refine ⟨38160141732913231280756069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25440094488608820853837379 38160141732913231280756069)
          ·
            refine ⟨7155026574921230865141763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38160141732913231280756069 7155026574921230865141763)
            ·
              refine ⟨10732539862381846297712645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7155026574921230865141763 10732539862381846297712645)
              ·
                refine ⟨2012351224196596180821121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10732539862381846297712645 2012351224196596180821121)
                ·
                  refine ⟨1509263418147447135615841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2012351224196596180821121 1509263418147447135615841)
                  ·
                    refine ⟨1131947563610585351711881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1509263418147447135615841 1131947563610585351711881)
                    ·
                      refine ⟨848960672707939013783911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1131947563610585351711881 848960672707939013783911)
                      ·
                        rfl

theorem cell23_1653345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_1653345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653345 prefixEnd_1653345 := by exact prefixLift 1653345
  have htrace : WordTrace (prefixWord ++ tailWord_1653345) baseStart_1653345 baseEnd_1653345 := by
    simpa [prefixWord, tailWord_1653345, baseEnd_1653345] using wordTrace_append hprefix tailTrace_1653345
  have hstable : (prefixWord ++ tailWord_1653345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653345).length < 2 ^ (prefixWord ++ tailWord_1653345).sum := by decide
  have hdescent : baseEnd_1653345 < baseStart_1653345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653358 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_1653358 : Nat := 118140960795 + 1653358 * 2 ^ 59
def prefixEnd_1653358 : Nat := 4983230072969 + 3 ^ 40 * 1653358 * 2
def baseEnd_1653358 : Nat := 848967347956447462921351

theorem tailTrace_1653358 : CollatzResearch.WordTrace tailWord_1653358 prefixEnd_1653358 848967347956447462921351 := by
  unfold tailWord_1653358
  simp only [CollatzResearch.WordTrace]
  refine ⟨7537865043021726488850091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40201946896115874607200485 7537865043021726488850091)
  ·
    refine ⟨11306797564532589733275137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7537865043021726488850091 11306797564532589733275137)
    ·
      refine ⟨8480098173399442299956353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11306797564532589733275137 8480098173399442299956353)
      ·
        refine ⟨6360073630049581724967265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8480098173399442299956353 6360073630049581724967265)
        ·
          refine ⟨4770055222537186293725449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6360073630049581724967265 4770055222537186293725449)
          ·
            refine ⟨3577541416902889720294087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4770055222537186293725449 3577541416902889720294087)
            ·
              refine ⟨5366312125354334580441131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3577541416902889720294087 5366312125354334580441131)
              ·
                refine ⟨8049468188031501870661697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5366312125354334580441131 8049468188031501870661697)
                ·
                  refine ⟨6037101141023626402996273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8049468188031501870661697 6037101141023626402996273)
                  ·
                    refine ⟨4527825855767719802247205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6037101141023626402996273 4527825855767719802247205)
                    ·
                      refine ⟨848967347956447462921351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4527825855767719802247205 848967347956447462921351)
                      ·
                        rfl

theorem cell23_1653358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_1653358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653358 prefixEnd_1653358 := by exact prefixLift 1653358
  have htrace : WordTrace (prefixWord ++ tailWord_1653358) baseStart_1653358 baseEnd_1653358 := by
    simpa [prefixWord, tailWord_1653358, baseEnd_1653358] using wordTrace_append hprefix tailTrace_1653358
  have hstable : (prefixWord ++ tailWord_1653358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653358).length < 2 ^ (prefixWord ++ tailWord_1653358).sum := by decide
  have hdescent : baseEnd_1653358 < baseStart_1653358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653381 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 1, 7]
def baseStart_1653381 : Nat := 118140960795 + 1653381 * 2 ^ 59
def prefixEnd_1653381 : Nat := 4983230072969 + 3 ^ 40 * 1653381 * 2
def baseEnd_1653381 : Nat := 282993052670500290977915

theorem tailTrace_1653381 : CollatzResearch.WordTrace tailWord_1653381 prefixEnd_1653381 282993052670500290977915 := by
  unfold tailWord_1653381
  simp only [CollatzResearch.WordTrace]
  refine ⟨60303759223090486838887997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40202506148726991225925331 60303759223090486838887997)
  ·
    refine ⟨22613909708658932564582999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60303759223090486838887997 22613909708658932564582999)
    ·
      refine ⟨33920864562988398846874499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22613909708658932564582999 33920864562988398846874499)
      ·
        refine ⟨50881296844482598270311749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33920864562988398846874499 50881296844482598270311749)
        ·
          refine ⟨9540243158340487175683453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50881296844482598270311749 9540243158340487175683453)
          ·
            refine ⟨3577591184377682690881295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9540243158340487175683453 3577591184377682690881295)
            ·
              refine ⟨5366386776566524036321943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3577591184377682690881295 5366386776566524036321943)
              ·
                refine ⟨8049580164849786054482915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5366386776566524036321943 8049580164849786054482915)
                ·
                  refine ⟨12074370247274679081724373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8049580164849786054482915 12074370247274679081724373)
                  ·
                    refine ⟨282993052670500290977915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12074370247274679081724373 282993052670500290977915)
                    ·
                      rfl

theorem cell23_1653381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_1653381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653381 prefixEnd_1653381 := by exact prefixLift 1653381
  have htrace : WordTrace (prefixWord ++ tailWord_1653381) baseStart_1653381 baseEnd_1653381 := by
    simpa [prefixWord, tailWord_1653381, baseEnd_1653381] using wordTrace_append hprefix tailTrace_1653381
  have hstable : (prefixWord ++ tailWord_1653381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653381).length < 2 ^ (prefixWord ++ tailWord_1653381).sum := by decide
  have hdescent : baseEnd_1653381 < baseStart_1653381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653401 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 4, 1, 4]
def baseStart_1653401 : Nat := 118140960795 + 1653401 * 2 ^ 59
def prefixEnd_1653401 : Nat := 4983230072969 + 3 ^ 40 * 1653401 * 2
def baseEnd_1653401 : Nat := 848989427624590794683653

theorem tailTrace_1653401 : CollatzResearch.WordTrace tailWord_1653401 prefixEnd_1653401 848989427624590794683653 := by
  unfold tailWord_1653401
  simp only [CollatzResearch.WordTrace]
  refine ⟨60304488683018030254616057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40202992455345353503077371 60304488683018030254616057)
  ·
    refine ⟨45228366512263522690962043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60304488683018030254616057 45228366512263522690962043)
    ·
      refine ⟨67842549768395284036443065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45228366512263522690962043 67842549768395284036443065)
      ·
        refine ⟨50881912326296463027332299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67842549768395284036443065 50881912326296463027332299)
        ·
          refine ⟨76322868489444694540998449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50881912326296463027332299 76322868489444694540998449)
          ·
            refine ⟨57242151367083520905748837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76322868489444694540998449 57242151367083520905748837)
            ·
              refine ⟨10732903381328160169827907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57242151367083520905748837 10732903381328160169827907)
              ·
                refine ⟨16099355071992240254741861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10732903381328160169827907 16099355071992240254741861)
                ·
                  refine ⟨3018629075998545047764099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16099355071992240254741861 3018629075998545047764099)
                  ·
                    refine ⟨4527943613997817571646149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3018629075998545047764099 4527943613997817571646149)
                    ·
                      refine ⟨848989427624590794683653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4527943613997817571646149 848989427624590794683653)
                      ·
                        rfl

theorem cell23_1653401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_1653401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653401 prefixEnd_1653401 := by exact prefixLift 1653401
  have htrace : WordTrace (prefixWord ++ tailWord_1653401) baseStart_1653401 baseEnd_1653401 := by
    simpa [prefixWord, tailWord_1653401, baseEnd_1653401] using wordTrace_append hprefix tailTrace_1653401
  have hstable : (prefixWord ++ tailWord_1653401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653401).length < 2 ^ (prefixWord ++ tailWord_1653401).sum := by decide
  have hdescent : baseEnd_1653401 < baseStart_1653401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653438 : List Nat := [4, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_1653438 : Nat := 118140960795 + 1653438 * 2 ^ 59
def prefixEnd_1653438 : Nat := 4983230072969 + 3 ^ 40 * 1653438 * 2
def baseEnd_1653438 : Nat := 849008426408807149920983

theorem tailTrace_1653438 : CollatzResearch.WordTrace tailWord_1653438 prefixEnd_1653438 849008426408807149920983 := by
  unfold tailWord_1653438
  simp only [CollatzResearch.WordTrace]
  refine ⟨7538229772985498196714121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40203892122589323715808645 7538229772985498196714121)
  ·
    refine ⟨5653672329739123647535591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7538229772985498196714121 5653672329739123647535591)
    ·
      refine ⟨8480508494608685471303387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5653672329739123647535591 8480508494608685471303387)
      ·
        refine ⟨12720762741913028206955081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8480508494608685471303387 12720762741913028206955081)
        ·
          refine ⟨9540572056434771155216311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12720762741913028206955081 9540572056434771155216311)
          ·
            refine ⟨14310858084652156732824467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9540572056434771155216311 14310858084652156732824467)
            ·
              refine ⟨21466287126978235099236701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14310858084652156732824467 21466287126978235099236701)
              ·
                refine ⟨8049857672616838162213763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21466287126978235099236701 8049857672616838162213763)
                ·
                  refine ⟨12074786508925257243320645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8049857672616838162213763 12074786508925257243320645)
                  ·
                    refine ⟨2264022470423485733122621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12074786508925257243320645 2264022470423485733122621)
                    ·
                      refine ⟨849008426408807149920983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2264022470423485733122621 849008426408807149920983)
                      ·
                        rfl

theorem cell23_1653438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_1653438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653438 prefixEnd_1653438 := by exact prefixLift 1653438
  have htrace : WordTrace (prefixWord ++ tailWord_1653438) baseStart_1653438 baseEnd_1653438 := by
    simpa [prefixWord, tailWord_1653438, baseEnd_1653438] using wordTrace_append hprefix tailTrace_1653438
  have hstable : (prefixWord ++ tailWord_1653438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653438).length < 2 ^ (prefixWord ++ tailWord_1653438).sum := by decide
  have hdescent : baseEnd_1653438 < baseStart_1653438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653475 : List Nat := [1, 1, 1, 7, 1, 1, 4, 1, 6]
def baseStart_1653475 : Nat := 118140960795 + 1653475 * 2 ^ 59
def prefixEnd_1653475 : Nat := 4983230072969 + 3 ^ 40 * 1653475 * 2
def baseEnd_1653475 : Nat := 94336380577002611684257

theorem tailTrace_1653475 : CollatzResearch.WordTrace tailWord_1653475 prefixEnd_1653475 94336380577002611684257 := by
  unfold tailWord_1653475
  simp only [CollatzResearch.WordTrace]
  refine ⟨60307187684749940892809879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40204791789833293928539919 60307187684749940892809879)
  ·
    refine ⟨90460781527124911339214819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60307187684749940892809879 90460781527124911339214819)
    ·
      refine ⟨135691172290687367008822229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90460781527124911339214819 135691172290687367008822229)
      ·
        refine ⟨3180261850562985164269271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 135691172290687367008822229 3180261850562985164269271)
        ·
          refine ⟨4770392775844477746403907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3180261850562985164269271 4770392775844477746403907)
          ·
            refine ⟨7155589163766716619605861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4770392775844477746403907 7155589163766716619605861)
            ·
              refine ⟨1341672968206259366176099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7155589163766716619605861 1341672968206259366176099)
              ·
                refine ⟨2012509452309389049264149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341672968206259366176099 2012509452309389049264149)
                ·
                  refine ⟨94336380577002611684257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2012509452309389049264149 94336380577002611684257)
                  ·
                    rfl

theorem cell23_1653475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 6].length) (baseStart_1653475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653475 prefixEnd_1653475 := by exact prefixLift 1653475
  have htrace : WordTrace (prefixWord ++ tailWord_1653475) baseStart_1653475 baseEnd_1653475 := by
    simpa [prefixWord, tailWord_1653475, baseEnd_1653475] using wordTrace_append hprefix tailTrace_1653475
  have hstable : (prefixWord ++ tailWord_1653475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653475).length < 2 ^ (prefixWord ++ tailWord_1653475).sum := by decide
  have hdescent : baseEnd_1653475 < baseStart_1653475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653485 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_1653485 : Nat := 118140960795 + 1653485 * 2 ^ 59
def prefixEnd_1653485 : Nat := 4983230072969 + 3 ^ 40 * 1653485 * 2
def baseEnd_1653485 : Nat := 849032559999568466033267

theorem tailTrace_1653485 : CollatzResearch.WordTrace tailWord_1653485 prefixEnd_1653485 849032559999568466033267 := by
  unfold tailWord_1653485
  simp only [CollatzResearch.WordTrace]
  refine ⟨60307552414713712600673909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40205034943142475067115939 60307552414713712600673909)
  ·
    refine ⟨5653833038879410556313179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60307552414713712600673909 5653833038879410556313179)
    ·
      refine ⟨8480749558319115834469769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5653833038879410556313179 8480749558319115834469769)
      ·
        refine ⟨6360562168739336875852327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8480749558319115834469769 6360562168739336875852327)
        ·
          refine ⟨9540843253109005313778491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6360562168739336875852327 9540843253109005313778491)
          ·
            refine ⟨14311264879663507970667737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9540843253109005313778491 14311264879663507970667737)
            ·
              refine ⟨10733448659747630978000803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14311264879663507970667737 10733448659747630978000803)
              ·
                refine ⟨16100172989621446467001205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10733448659747630978000803 16100172989621446467001205)
                ·
                  refine ⟨1509391217777010606281363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16100172989621446467001205 1509391217777010606281363)
                  ·
                    refine ⟨2264086826665515909422045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1509391217777010606281363 2264086826665515909422045)
                    ·
                      refine ⟨849032559999568466033267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2264086826665515909422045 849032559999568466033267)
                      ·
                        rfl

theorem cell23_1653485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_1653485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653485 prefixEnd_1653485 := by exact prefixLift 1653485
  have htrace : WordTrace (prefixWord ++ tailWord_1653485) baseStart_1653485 baseEnd_1653485 := by
    simpa [prefixWord, tailWord_1653485, baseEnd_1653485] using wordTrace_append hprefix tailTrace_1653485
  have hstable : (prefixWord ++ tailWord_1653485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653485).length < 2 ^ (prefixWord ++ tailWord_1653485).sum := by decide
  have hdescent : baseEnd_1653485 < baseStart_1653485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653521 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 6]
def baseStart_1653521 : Nat := 118140960795 + 1653521 * 2 ^ 59
def prefixEnd_1653521 : Nat := 4983230072969 + 3 ^ 40 * 1653521 * 2
def baseEnd_1653521 : Nat := 849051045303130325183101

theorem tailTrace_1653521 : CollatzResearch.WordTrace tailWord_1653521 prefixEnd_1653521 849051045303130325183101 := by
  unfold tailWord_1653521
  simp only [CollatzResearch.WordTrace]
  refine ⟨60308865442583290748984417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40205910295055527165989611 60308865442583290748984417)
  ·
    refine ⟨45231649081937468061738313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60308865442583290748984417 45231649081937468061738313)
    ·
      refine ⟨33923736811453101046303735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45231649081937468061738313 33923736811453101046303735)
      ·
        refine ⟨50885605217179651569455603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33923736811453101046303735 50885605217179651569455603)
        ·
          refine ⟨76328407825769477354183405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50885605217179651569455603 76328407825769477354183405)
          ·
            refine ⟨28623152934663554007818777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76328407825769477354183405 28623152934663554007818777)
            ·
              refine ⟨21467364700997665505864083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28623152934663554007818777 21467364700997665505864083)
              ·
                refine ⟨32201047051496498258796125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21467364700997665505864083 32201047051496498258796125)
                ·
                  refine ⟨12075392644311186847048547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32201047051496498258796125 12075392644311186847048547)
                  ·
                    refine ⟨18113088966466780270572821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12075392644311186847048547 18113088966466780270572821)
                    ·
                      refine ⟨849051045303130325183101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18113088966466780270572821 849051045303130325183101)
                      ·
                        rfl

theorem cell23_1653521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_1653521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653521 prefixEnd_1653521 := by exact prefixLift 1653521
  have htrace : WordTrace (prefixWord ++ tailWord_1653521) baseStart_1653521 baseEnd_1653521 := by
    simpa [prefixWord, tailWord_1653521, baseEnd_1653521] using wordTrace_append hprefix tailTrace_1653521
  have hstable : (prefixWord ++ tailWord_1653521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653521).length < 2 ^ (prefixWord ++ tailWord_1653521).sum := by decide
  have hdescent : baseEnd_1653521 < baseStart_1653521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653535 : List Nat := [1, 1, 2, 4, 2, 2, 2, 3, 2, 4]
def baseStart_1653535 : Nat := 118140960795 + 1653535 * 2 ^ 59
def prefixEnd_1653535 : Nat := 4983230072969 + 3 ^ 40 * 1653535 * 2
def baseEnd_1653535 : Nat := 283019411344097756802679

theorem tailTrace_1653535 : CollatzResearch.WordTrace tailWord_1653535 prefixEnd_1653535 283019411344097756802679 := by
  unfold tailWord_1653535
  simp only [CollatzResearch.WordTrace]
  refine ⟨60309376064532571139994059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40206250709688380759996039 60309376064532571139994059)
  ·
    refine ⟨90464064096798856709991089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60309376064532571139994059 90464064096798856709991089)
    ·
      refine ⟨67848048072599142532493317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90464064096798856709991089 67848048072599142532493317)
      ·
        refine ⟨12721509013612339224842497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67848048072599142532493317 12721509013612339224842497)
        ·
          refine ⟨9541131760209254418631873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12721509013612339224842497 9541131760209254418631873)
          ·
            refine ⟨7155848820156940813973905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9541131760209254418631873 7155848820156940813973905)
            ·
              refine ⟨5366886615117705610480429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7155848820156940813973905 5366886615117705610480429)
              ·
                refine ⟨2012582480669139603930161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5366886615117705610480429 2012582480669139603930161)
                ·
                  refine ⟨1509436860501854702947621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2012582480669139603930161 1509436860501854702947621)
                  ·
                    refine ⟨283019411344097756802679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1509436860501854702947621 283019411344097756802679)
                    ·
                      rfl

theorem cell23_1653535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 3, 2, 4].length) (baseStart_1653535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653535 prefixEnd_1653535 := by exact prefixLift 1653535
  have htrace : WordTrace (prefixWord ++ tailWord_1653535) baseStart_1653535 baseEnd_1653535 := by
    simpa [prefixWord, tailWord_1653535, baseEnd_1653535] using wordTrace_append hprefix tailTrace_1653535
  have hstable : (prefixWord ++ tailWord_1653535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653535).length < 2 ^ (prefixWord ++ tailWord_1653535).sum := by decide
  have hdescent : baseEnd_1653535 < baseStart_1653535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653546 : List Nat := [3, 1, 4, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_1653546 : Nat := 118140960795 + 1653546 * 2 ^ 59
def prefixEnd_1653546 : Nat := 4983230072969 + 3 ^ 40 * 1653546 * 2
def baseEnd_1653546 : Nat := 849063882319492727370487

theorem tailTrace_1653546 : CollatzResearch.WordTrace tailWord_1653546 prefixEnd_1653546 849063882319492727370487 := by
  unfold tailWord_1653546
  simp only [CollatzResearch.WordTrace]
  refine ⟨15077444316873180004661123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40206518178328480012429661 15077444316873180004661123)
  ·
    refine ⟨22616166475309770006991685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15077444316873180004661123 22616166475309770006991685)
    ·
      refine ⟨4240531214120581876310941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22616166475309770006991685 4240531214120581876310941)
      ·
        refine ⟨1590199205295218203616603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4240531214120581876310941 1590199205295218203616603)
        ·
          refine ⟨2385298807942827305424905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1590199205295218203616603 2385298807942827305424905)
          ·
            refine ⟨1788974105957120479068679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2385298807942827305424905 1788974105957120479068679)
            ·
              refine ⟨2683461158935680718603019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788974105957120479068679 2683461158935680718603019)
              ·
                refine ⟨4025191738403521077904529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2683461158935680718603019 4025191738403521077904529)
                ·
                  refine ⟨3018893803802640808428397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4025191738403521077904529 3018893803802640808428397)
                  ·
                    refine ⟨1132085176425990303160649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3018893803802640808428397 1132085176425990303160649)
                    ·
                      refine ⟨849063882319492727370487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1132085176425990303160649 849063882319492727370487)
                      ·
                        rfl

theorem cell23_1653546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_1653546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653546 prefixEnd_1653546 := by exact prefixLift 1653546
  have htrace : WordTrace (prefixWord ++ tailWord_1653546) baseStart_1653546 baseEnd_1653546 := by
    simpa [prefixWord, tailWord_1653546, baseEnd_1653546] using wordTrace_append hprefix tailTrace_1653546
  have hstable : (prefixWord ++ tailWord_1653546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653546).length < 2 ^ (prefixWord ++ tailWord_1653546).sum := by decide
  have hdescent : baseEnd_1653546 < baseStart_1653546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653548 : List Nat := [2, 2, 1, 1, 1, 4, 5, 7]
def baseStart_1653548 : Nat := 118140960795 + 1653548 * 2 ^ 59
def prefixEnd_1653548 : Nat := 4983230072969 + 3 ^ 40 * 1653548 * 2
def baseEnd_1653548 : Nat := 31446848491881545168351

theorem tailTrace_1653548 : CollatzResearch.WordTrace tailWord_1653548 prefixEnd_1653548 31446848491881545168351 := by
  unfold tailWord_1653548
  simp only [CollatzResearch.WordTrace]
  refine ⟨30154925106742737180108649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40206566808990316240144865 30154925106742737180108649)
  ·
    refine ⟨22616193830057052885081487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30154925106742737180108649 22616193830057052885081487)
    ·
      refine ⟨33924290745085579327622231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22616193830057052885081487 33924290745085579327622231)
      ·
        refine ⟨50886436117628368991433347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33924290745085579327622231 50886436117628368991433347)
        ·
          refine ⟨76329654176442553487150021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50886436117628368991433347 76329654176442553487150021)
          ·
            refine ⟨14311810158082978778840629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76329654176442553487150021 14311810158082978778840629)
            ·
              refine ⟨1341732202320279260516309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14311810158082978778840629 1341732202320279260516309)
              ·
                refine ⟨31446848491881545168351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1341732202320279260516309 31446848491881545168351)
                ·
                  rfl

theorem cell23_1653548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 7].length) (baseStart_1653548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653548 prefixEnd_1653548 := by exact prefixLift 1653548
  have htrace : WordTrace (prefixWord ++ tailWord_1653548) baseStart_1653548 baseEnd_1653548 := by
    simpa [prefixWord, tailWord_1653548, baseEnd_1653548] using wordTrace_append hprefix tailTrace_1653548
  have hstable : (prefixWord ++ tailWord_1653548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653548).length < 2 ^ (prefixWord ++ tailWord_1653548).sum := by decide
  have hdescent : baseEnd_1653548 < baseStart_1653548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653556 : List Nat := [2, 5, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_1653556 : Nat := 118140960795 + 1653556 * 2 ^ 59
def prefixEnd_1653556 : Nat := 4983230072969 + 3 ^ 40 * 1653556 * 2
def baseEnd_1653556 : Nat := 283023005708679229415147

theorem tailTrace_1653556 : CollatzResearch.WordTrace tailWord_1653556 prefixEnd_1653556 283023005708679229415147 := by
  unfold tailWord_1653556
  simp only [CollatzResearch.WordTrace]
  refine ⟨30155070998728245863254261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40206761331637661151005681 30155070998728245863254261)
  ·
    refine ⟨2827037906130773049680087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30155070998728245863254261 2827037906130773049680087)
    ·
      refine ⟨4240556859196159574520131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2827037906130773049680087 4240556859196159574520131)
      ·
        refine ⟨6360835288794239361780197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4240556859196159574520131 6360835288794239361780197)
        ·
          refine ⟨1192656616648919880333787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6360835288794239361780197 1192656616648919880333787)
          ·
            refine ⟨1788984924973379820500681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192656616648919880333787 1788984924973379820500681)
            ·
              refine ⟨1341738693730034865375511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1788984924973379820500681 1341738693730034865375511)
              ·
                refine ⟨2012608040595052298063267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341738693730034865375511 2012608040595052298063267)
                ·
                  refine ⟨3018912060892578447094901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012608040595052298063267 3018912060892578447094901)
                  ·
                    refine ⟨283023005708679229415147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3018912060892578447094901 283023005708679229415147)
                    ·
                      rfl

theorem cell23_1653556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_1653556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653556 prefixEnd_1653556 := by exact prefixLift 1653556
  have htrace : WordTrace (prefixWord ++ tailWord_1653556) baseStart_1653556 baseEnd_1653556 := by
    simpa [prefixWord, tailWord_1653556, baseEnd_1653556] using wordTrace_append hprefix tailTrace_1653556
  have hstable : (prefixWord ++ tailWord_1653556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653556).length < 2 ^ (prefixWord ++ tailWord_1653556).sum := by decide
  have hdescent : baseEnd_1653556 < baseStart_1653556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653559 : List Nat := [1, 1, 3, 1, 2, 1, 6, 3, 1, 2, 2]
def baseStart_1653559 : Nat := 118140960795 + 1653559 * 2 ^ 59
def prefixEnd_1653559 : Nat := 4983230072969 + 3 ^ 40 * 1653559 * 2
def baseEnd_1653559 : Nat := 849070557568001176507927

theorem tailTrace_1653559 : CollatzResearch.WordTrace tailWord_1653559 prefixEnd_1653559 849070557568001176507927 := by
  unfold tailWord_1653559
  simp only [CollatzResearch.WordTrace]
  refine ⟨60310251416445623238867731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40206834277630415492578487 60310251416445623238867731)
  ·
    refine ⟨90465377124668434858301597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60310251416445623238867731 90465377124668434858301597)
    ·
      refine ⟨33924516421750663071863099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90465377124668434858301597 33924516421750663071863099)
      ·
        refine ⟨50886774632625994607794649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33924516421750663071863099 50886774632625994607794649)
        ·
          refine ⟨38165080974469495955845987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50886774632625994607794649 38165080974469495955845987)
          ·
            refine ⟨57247621461704243933768981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38165080974469495955845987 57247621461704243933768981)
            ·
              refine ⟨2683482256017386434395421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57247621461704243933768981 2683482256017386434395421)
              ·
                refine ⟨1006305846006519912898283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2683482256017386434395421 1006305846006519912898283)
                ·
                  refine ⟨1509458769009779869347425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1006305846006519912898283 1509458769009779869347425)
                  ·
                    refine ⟨1132094076757334902010569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1509458769009779869347425 1132094076757334902010569)
                    ·
                      refine ⟨849070557568001176507927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1132094076757334902010569 849070557568001176507927)
                      ·
                        rfl

theorem cell23_1653559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 3, 1, 2, 2].length) (baseStart_1653559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653559 prefixEnd_1653559 := by exact prefixLift 1653559
  have htrace : WordTrace (prefixWord ++ tailWord_1653559) baseStart_1653559 baseEnd_1653559 := by
    simpa [prefixWord, tailWord_1653559, baseEnd_1653559] using wordTrace_append hprefix tailTrace_1653559
  have hstable : (prefixWord ++ tailWord_1653559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653559).length < 2 ^ (prefixWord ++ tailWord_1653559).sum := by decide
  have hdescent : baseEnd_1653559 < baseStart_1653559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653562 : List Nat := [3, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3]
def baseStart_1653562 : Nat := 118140960795 + 1653562 * 2 ^ 59
def prefixEnd_1653562 : Nat := 4983230072969 + 3 ^ 40 * 1653562 * 2
def baseEnd_1653562 : Nat := 849072098009964664770413

theorem tailTrace_1653562 : CollatzResearch.WordTrace tailWord_1653562 prefixEnd_1653562 849072098009964664770413 := by
  unfold tailWord_1653562
  simp only [CollatzResearch.WordTrace]
  refine ⟨15077590208858688687806735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40206907223623169834151293 15077590208858688687806735)
  ·
    refine ⟨22616385313288033031710103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15077590208858688687806735 22616385313288033031710103)
    ·
      refine ⟨33924577969932049547565155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22616385313288033031710103 33924577969932049547565155)
      ·
        refine ⟨50886866954898074321347733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33924577969932049547565155 50886866954898074321347733)
        ·
          refine ⟨2385321888510847233813175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 50886866954898074321347733 2385321888510847233813175)
          ·
            refine ⟨3577982832766270850719763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2385321888510847233813175 3577982832766270850719763)
            ·
              refine ⟨5366974249149406276079645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3577982832766270850719763 5366974249149406276079645)
              ·
                refine ⟨2012615343431027353529867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5366974249149406276079645 2012615343431027353529867)
                ·
                  refine ⟨3018923015146541030294801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2012615343431027353529867 3018923015146541030294801)
                  ·
                    refine ⟨2264192261359905772721101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3018923015146541030294801 2264192261359905772721101)
                    ·
                      refine ⟨849072098009964664770413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2264192261359905772721101 849072098009964664770413)
                      ·
                        rfl

theorem cell23_1653562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 1, 3, 1, 2, 3].length) (baseStart_1653562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653562 prefixEnd_1653562 := by exact prefixLift 1653562
  have htrace : WordTrace (prefixWord ++ tailWord_1653562) baseStart_1653562 baseEnd_1653562 := by
    simpa [prefixWord, tailWord_1653562, baseEnd_1653562] using wordTrace_append hprefix tailTrace_1653562
  have hstable : (prefixWord ++ tailWord_1653562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653562).length < 2 ^ (prefixWord ++ tailWord_1653562).sum := by decide
  have hdescent : baseEnd_1653562 < baseStart_1653562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653615 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 1, 4, 2]
def baseStart_1653615 : Nat := 118140960795 + 1653615 * 2 ^ 59
def prefixEnd_1653615 : Nat := 4983230072969 + 3 ^ 40 * 1653615 * 2
def baseEnd_1653615 : Nat := 849099312484652957407669

theorem tailTrace_1653615 : CollatzResearch.WordTrace tailWord_1653615 prefixEnd_1653615 849099312484652957407669 := by
  unfold tailWord_1653615
  simp only [CollatzResearch.WordTrace]
  refine ⟨60312293904242744802906299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40208195936161829868604199 60312293904242744802906299)
  ·
    refine ⟨90468440856364117204359449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60312293904242744802906299 90468440856364117204359449)
    ·
      refine ⟨67851330642273087903269587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90468440856364117204359449 67851330642273087903269587)
      ·
        refine ⟨101776995963409631854904381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67851330642273087903269587 101776995963409631854904381)
        ·
          refine ⟨38166373486278611945589143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101776995963409631854904381 38166373486278611945589143)
          ·
            refine ⟨57249560229417917918383715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38166373486278611945589143 57249560229417917918383715)
            ·
              refine ⟨85874340344126876877575573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57249560229417917918383715 85874340344126876877575573)
              ·
                refine ⟨4025359703630947353636355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85874340344126876877575573 4025359703630947353636355)
                ·
                  refine ⟨6038039555446421030454533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025359703630947353636355 6038039555446421030454533)
                  ·
                    refine ⟨1132132416646203943210225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6038039555446421030454533 1132132416646203943210225)
                    ·
                      refine ⟨849099312484652957407669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1132132416646203943210225 849099312484652957407669)
                      ·
                        rfl

theorem cell23_1653615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 4, 2].length) (baseStart_1653615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653615 prefixEnd_1653615 := by exact prefixLift 1653615
  have htrace : WordTrace (prefixWord ++ tailWord_1653615) baseStart_1653615 baseEnd_1653615 := by
    simpa [prefixWord, tailWord_1653615, baseEnd_1653615] using wordTrace_append hprefix tailTrace_1653615
  have hstable : (prefixWord ++ tailWord_1653615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653615).length < 2 ^ (prefixWord ++ tailWord_1653615).sum := by decide
  have hdescent : baseEnd_1653615 < baseStart_1653615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653618 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1653618 : Nat := 118140960795 + 1653618 * 2 ^ 59
def prefixEnd_1653618 : Nat := 4983230072969 + 3 ^ 40 * 1653618 * 2
def baseEnd_1653618 : Nat := 849100852926616445670155

theorem tailTrace_1653618 : CollatzResearch.WordTrace tailWord_1653618 prefixEnd_1653618 849100852926616445670155 := by
  unfold tailWord_1653618
  simp only [CollatzResearch.WordTrace]
  refine ⟨15078100830807969078816377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40208268882154584210177005 15078100830807969078816377)
  ·
    refine ⟨11308575623105976809112283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15078100830807969078816377 11308575623105976809112283)
    ·
      refine ⟨16962863434658965213668425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11308575623105976809112283 16962863434658965213668425)
      ·
        refine ⟨12722147575994223910251319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16962863434658965213668425 12722147575994223910251319)
        ·
          refine ⟨19083221363991335865376979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12722147575994223910251319 19083221363991335865376979)
          ·
            refine ⟨28624832045987003798065469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19083221363991335865376979 28624832045987003798065469)
            ·
              refine ⟨10734312017245126424274551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28624832045987003798065469 10734312017245126424274551)
              ·
                refine ⟨16101468025867689636411827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10734312017245126424274551 16101468025867689636411827)
                ·
                  refine ⟨24152202038801534454617741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16101468025867689636411827 24152202038801534454617741)
                  ·
                    refine ⟨9057075764550575420481653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24152202038801534454617741 9057075764550575420481653)
                    ·
                      refine ⟨849100852926616445670155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9057075764550575420481653 849100852926616445670155)
                      ·
                        rfl

theorem cell23_1653618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1653618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653618 prefixEnd_1653618 := by exact prefixLift 1653618
  have htrace : WordTrace (prefixWord ++ tailWord_1653618) baseStart_1653618 baseEnd_1653618 := by
    simpa [prefixWord, tailWord_1653618, baseEnd_1653618] using wordTrace_append hprefix tailTrace_1653618
  have hstable : (prefixWord ++ tailWord_1653618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653618).length < 2 ^ (prefixWord ++ tailWord_1653618).sum := by decide
  have hdescent : baseEnd_1653618 < baseStart_1653618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653628 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_1653628 : Nat := 118140960795 + 1653628 * 2 ^ 59
def prefixEnd_1653628 : Nat := 4983230072969 + 3 ^ 40 * 1653628 * 2
def baseEnd_1653628 : Nat := 849105987733161406545109

theorem tailTrace_1653628 : CollatzResearch.WordTrace tailWord_1653628 prefixEnd_1653628 849105987733161406545109 := by
  unfold tailWord_1653628
  simp only [CollatzResearch.WordTrace]
  refine ⟨30156384026597824011564769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40208512035463765348753025 30156384026597824011564769)
  ·
    refine ⟨22617288019948368008673577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30156384026597824011564769 22617288019948368008673577)
    ·
      refine ⟨16962966014961276006505183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22617288019948368008673577 16962966014961276006505183)
      ·
        refine ⟨25444449022441914009757775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16962966014961276006505183 25444449022441914009757775)
        ·
          refine ⟨38166673533662871014636663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25444449022441914009757775 38166673533662871014636663)
          ·
            refine ⟨57250010300494306521954995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38166673533662871014636663 57250010300494306521954995)
            ·
              refine ⟨85875015450741459782932493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57250010300494306521954995 85875015450741459782932493)
              ·
                refine ⟨32203130794028047418599685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85875015450741459782932493 32203130794028047418599685)
                ·
                  refine ⟨6038087023880258890987441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32203130794028047418599685 6038087023880258890987441)
                  ·
                    refine ⟨4528565267910194168240581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6038087023880258890987441 4528565267910194168240581)
                    ·
                      refine ⟨849105987733161406545109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4528565267910194168240581 849105987733161406545109)
                      ·
                        rfl

theorem cell23_1653628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_1653628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653628 prefixEnd_1653628 := by exact prefixLift 1653628
  have htrace : WordTrace (prefixWord ++ tailWord_1653628) baseStart_1653628 baseEnd_1653628 := by
    simpa [prefixWord, tailWord_1653628, baseEnd_1653628] using wordTrace_append hprefix tailTrace_1653628
  have hstable : (prefixWord ++ tailWord_1653628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653628).length < 2 ^ (prefixWord ++ tailWord_1653628).sum := by decide
  have hdescent : baseEnd_1653628 < baseStart_1653628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653685 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 2, 5]
def baseStart_1653685 : Nat := 118140960795 + 1653685 * 2 ^ 59
def prefixEnd_1653685 : Nat := 4983230072969 + 3 ^ 40 * 1653685 * 2
def baseEnd_1653685 : Nat := 283045085376822561177449

theorem tailTrace_1653685 : CollatzResearch.WordTrace tailWord_1653685 prefixEnd_1653685 283045085376822561177449 := by
  unfold tailWord_1653685
  simp only [CollatzResearch.WordTrace]
  refine ⟨60314847013989146757954509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40209898009326097838636339 60314847013989146757954509)
  ·
    refine ⟨22618067630245930034232941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60314847013989146757954509 22618067630245930034232941)
    ·
      refine ⟨8481775361342223762837353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22618067630245930034232941 8481775361342223762837353)
      ·
        refine ⟨6361331521006667822128015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8481775361342223762837353 6361331521006667822128015)
        ·
          refine ⟨9541997281510001733192023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6361331521006667822128015 9541997281510001733192023)
          ·
            refine ⟨14312995922265002599788035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9541997281510001733192023 14312995922265002599788035)
            ·
              refine ⟨21469493883397503899682053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14312995922265002599788035 21469493883397503899682053)
              ·
                refine ⟨4025530103137031981190385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21469493883397503899682053 4025530103137031981190385)
                ·
                  refine ⟨3019147577352773985892789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4025530103137031981190385 3019147577352773985892789)
                  ·
                    refine ⟨283045085376822561177449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3019147577352773985892789 283045085376822561177449)
                    ·
                      rfl

theorem cell23_1653685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_1653685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653685 prefixEnd_1653685 := by exact prefixLift 1653685
  have htrace : WordTrace (prefixWord ++ tailWord_1653685) baseStart_1653685 baseEnd_1653685 := by
    simpa [prefixWord, tailWord_1653685, baseEnd_1653685] using wordTrace_append hprefix tailTrace_1653685
  have hstable : (prefixWord ++ tailWord_1653685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653685).length < 2 ^ (prefixWord ++ tailWord_1653685).sum := by decide
  have hdescent : baseEnd_1653685 < baseStart_1653685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653689 : List Nat := [1, 2, 1, 4, 2, 4, 2, 2, 5]
def baseStart_1653689 : Nat := 118140960795 + 1653689 * 2 ^ 59
def prefixEnd_1653689 : Nat := 4983230072969 + 3 ^ 40 * 1653689 * 2
def baseEnd_1653689 : Nat := 94348590005898407542481

theorem tailTrace_1653689 : CollatzResearch.WordTrace tailWord_1653689 prefixEnd_1653689 94348590005898407542481 := by
  unfold tailWord_1653689
  simp only [CollatzResearch.WordTrace]
  refine ⟨60314992905974655441100121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40209995270649770294066747 60314992905974655441100121)
  ·
    refine ⟨45236244679480991580825091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60314992905974655441100121 45236244679480991580825091)
    ·
      refine ⟨67854367019221487371237637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45236244679480991580825091 67854367019221487371237637)
      ·
        refine ⟨12722693816104028882107057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67854367019221487371237637 12722693816104028882107057)
        ·
          refine ⟨9542020362078021661580293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12722693816104028882107057 9542020362078021661580293)
          ·
            refine ⟨1789128817889629061546305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9542020362078021661580293 1789128817889629061546305)
            ·
              refine ⟨1341846613417221796159729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1789128817889629061546305 1341846613417221796159729)
              ·
                refine ⟨1006384960062916347119797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1341846613417221796159729 1006384960062916347119797)
                ·
                  refine ⟨94348590005898407542481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1006384960062916347119797 94348590005898407542481)
                  ·
                    rfl

theorem cell23_1653689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 5].length) (baseStart_1653689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653689 prefixEnd_1653689 := by exact prefixLift 1653689
  have htrace : WordTrace (prefixWord ++ tailWord_1653689) baseStart_1653689 baseEnd_1653689 := by
    simpa [prefixWord, tailWord_1653689, baseEnd_1653689] using wordTrace_append hprefix tailTrace_1653689
  have hstable : (prefixWord ++ tailWord_1653689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653689).length < 2 ^ (prefixWord ++ tailWord_1653689).sum := by decide
  have hdescent : baseEnd_1653689 < baseStart_1653689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653722 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4]
def baseStart_1653722 : Nat := 118140960795 + 1653722 * 2 ^ 59
def prefixEnd_1653722 : Nat := 4983230072969 + 3 ^ 40 * 1653722 * 2
def baseEnd_1653722 : Nat := 849154254914684038769677

theorem tailTrace_1653722 : CollatzResearch.WordTrace tailWord_1653722 prefixEnd_1653722 849154254914684038769677 := by
  unfold tailWord_1653722
  simp only [CollatzResearch.WordTrace]
  refine ⟨15079049128713775519262855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40210797676570068051367613 15079049128713775519262855)
  ·
    refine ⟨22618573693070663278894283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15079049128713775519262855 22618573693070663278894283)
    ·
      refine ⟨33927860539605994918341425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22618573693070663278894283 33927860539605994918341425)
      ·
        refine ⟨25445895404704496188756069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33927860539605994918341425 25445895404704496188756069)
        ·
          refine ⟨4771105388382093035391763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25445895404704496188756069 4771105388382093035391763)
          ·
            refine ⟨7156658082573139553087645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4771105388382093035391763 7156658082573139553087645)
            ·
              refine ⟨2683746780964927332407867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7156658082573139553087645 2683746780964927332407867)
              ·
                refine ⟨4025620171447390998611801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2683746780964927332407867 4025620171447390998611801)
                ·
                  refine ⟨3019215128585543248958851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4025620171447390998611801 3019215128585543248958851)
                  ·
                    refine ⟨4528822692878314873438277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3019215128585543248958851 4528822692878314873438277)
                    ·
                      refine ⟨849154254914684038769677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4528822692878314873438277 849154254914684038769677)
                      ·
                        rfl

theorem cell23_1653722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 2, 1, 4].length) (baseStart_1653722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653722 prefixEnd_1653722 := by exact prefixLift 1653722
  have htrace : WordTrace (prefixWord ++ tailWord_1653722) baseStart_1653722 baseEnd_1653722 := by
    simpa [prefixWord, tailWord_1653722, baseEnd_1653722] using wordTrace_append hprefix tailTrace_1653722
  have hstable : (prefixWord ++ tailWord_1653722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653722).length < 2 ^ (prefixWord ++ tailWord_1653722).sum := by decide
  have hdescent : baseEnd_1653722 < baseStart_1653722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653735 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1653735 : Nat := 118140960795 + 1653735 * 2 ^ 59
def prefixEnd_1653735 : Nat := 4983230072969 + 3 ^ 40 * 1653735 * 2
def baseEnd_1653735 : Nat := 849160930163192487907117

theorem tailTrace_1653735 : CollatzResearch.WordTrace tailWord_1653735 prefixEnd_1653735 849160930163192487907117 := by
  unfold tailWord_1653735
  simp only [CollatzResearch.WordTrace]
  refine ⟨60316670663808005297274659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40211113775872003531516439 60316670663808005297274659)
  ·
    refine ⟨90475005995712007945911989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60316670663808005297274659 90475005995712007945911989)
    ·
      refine ⟨8482031812098000744929249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90475005995712007945911989 8482031812098000744929249)
      ·
        refine ⟨6361523859073500558696937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8482031812098000744929249 6361523859073500558696937)
        ·
          refine ⟨4771142894305125419022703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6361523859073500558696937 4771142894305125419022703)
          ·
            refine ⟨7156714341457688128534055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4771142894305125419022703 7156714341457688128534055)
            ·
              refine ⟨10735071512186532192801083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7156714341457688128534055 10735071512186532192801083)
              ·
                refine ⟨16102607268279798289201625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10735071512186532192801083 16102607268279798289201625)
                ·
                  refine ⟨12076955451209848716901219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16102607268279798289201625 12076955451209848716901219)
                  ·
                    refine ⟨18115433176814773075351829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12076955451209848716901219 18115433176814773075351829)
                    ·
                      refine ⟨849160930163192487907117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18115433176814773075351829 849160930163192487907117)
                      ·
                        rfl

theorem cell23_1653735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1653735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653735 prefixEnd_1653735 := by exact prefixLift 1653735
  have htrace : WordTrace (prefixWord ++ tailWord_1653735) baseStart_1653735 baseEnd_1653735 := by
    simpa [prefixWord, tailWord_1653735, baseEnd_1653735] using wordTrace_append hprefix tailTrace_1653735
  have hstable : (prefixWord ++ tailWord_1653735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653735).length < 2 ^ (prefixWord ++ tailWord_1653735).sum := by decide
  have hdescent : baseEnd_1653735 < baseStart_1653735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653745 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 8]
def baseStart_1653745 : Nat := 118140960795 + 1653745 * 2 ^ 59
def prefixEnd_1653745 : Nat := 4983230072969 + 3 ^ 40 * 1653745 * 2
def baseEnd_1653745 : Nat := 94351784996637494309119

theorem tailTrace_1653745 : CollatzResearch.WordTrace tailWord_1653745 prefixEnd_1653745 94351784996637494309119 := by
  unfold tailWord_1653745
  simp only [CollatzResearch.WordTrace]
  refine ⟨60317035393771777005138689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40211356929181184670092459 60317035393771777005138689)
  ·
    refine ⟨45237776545328832753854017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60317035393771777005138689 45237776545328832753854017)
    ·
      refine ⟨33928332408996624565390513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45237776545328832753854017 33928332408996624565390513)
      ·
        refine ⟨25446249306747468424042885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33928332408996624565390513 25446249306747468424042885)
        ·
          refine ⟨4771171745015150329508041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25446249306747468424042885 4771171745015150329508041)
          ·
            refine ⟨3578378808761362747131031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4771171745015150329508041 3578378808761362747131031)
            ·
              refine ⟨5367568213142044120696547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3578378808761362747131031 5367568213142044120696547)
              ·
                refine ⟨8051352319713066181044821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5367568213142044120696547 8051352319713066181044821)
                ·
                  refine ⟨94351784996637494309119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8051352319713066181044821 94351784996637494309119)
                  ·
                    rfl

theorem cell23_1653745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 8].length) (baseStart_1653745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653745 prefixEnd_1653745 := by exact prefixLift 1653745
  have htrace : WordTrace (prefixWord ++ tailWord_1653745) baseStart_1653745 baseEnd_1653745 := by
    simpa [prefixWord, tailWord_1653745, baseEnd_1653745] using wordTrace_append hprefix tailTrace_1653745
  have hstable : (prefixWord ++ tailWord_1653745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653745).length < 2 ^ (prefixWord ++ tailWord_1653745).sum := by decide
  have hdescent : baseEnd_1653745 < baseStart_1653745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653815 : List Nat := [1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 3]
def baseStart_1653815 : Nat := 118140960795 + 1653815 * 2 ^ 59
def prefixEnd_1653815 : Nat := 4983230072969 + 3 ^ 40 * 1653815 * 2
def baseEnd_1653815 : Nat := 849202008615552174906749

theorem tailTrace_1653815 : CollatzResearch.WordTrace tailWord_1653815 prefixEnd_1653815 849202008615552174906749 := by
  unfold tailWord_1653815
  simp only [CollatzResearch.WordTrace]
  refine ⟨60319588503518178960186899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40213059002345452640124599 60319588503518178960186899)
  ·
    refine ⟨90479382755277268440280349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60319588503518178960186899 90479382755277268440280349)
    ·
      refine ⟨33929768533228975665105131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90479382755277268440280349 33929768533228975665105131)
      ·
        refine ⟨50894652799843463497657697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33929768533228975665105131 50894652799843463497657697)
        ·
          refine ⟨38170989599882597623243273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50894652799843463497657697 38170989599882597623243273)
          ·
            refine ⟨28628242199911948217432455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38170989599882597623243273 28628242199911948217432455)
            ·
              refine ⟨42942363299867922326148683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28628242199911948217432455 42942363299867922326148683)
              ·
                refine ⟨64413544949801883489223025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42942363299867922326148683 64413544949801883489223025)
                ·
                  refine ⟨48310158712351412616917269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64413544949801883489223025 48310158712351412616917269)
                  ·
                    refine ⟨2264538689641472466417997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48310158712351412616917269 2264538689641472466417997)
                    ·
                      refine ⟨849202008615552174906749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2264538689641472466417997 849202008615552174906749)
                      ·
                        rfl

theorem cell23_1653815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_1653815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653815 prefixEnd_1653815 := by exact prefixLift 1653815
  have htrace : WordTrace (prefixWord ++ tailWord_1653815) baseStart_1653815 baseEnd_1653815 := by
    simpa [prefixWord, tailWord_1653815, baseEnd_1653815] using wordTrace_append hprefix tailTrace_1653815
  have hstable : (prefixWord ++ tailWord_1653815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653815).length < 2 ^ (prefixWord ++ tailWord_1653815).sum := by decide
  have hdescent : baseEnd_1653815 < baseStart_1653815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653829 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 3, 2, 2]
def baseStart_1653829 : Nat := 118140960795 + 1653829 * 2 ^ 59
def prefixEnd_1653829 : Nat := 4983230072969 + 3 ^ 40 * 1653829 * 2
def baseEnd_1653829 : Nat := 849209197344715120131685

theorem tailTrace_1653829 : CollatzResearch.WordTrace tailWord_1653829 prefixEnd_1653829 849209197344715120131685 := by
  unfold tailWord_1653829
  simp only [CollatzResearch.WordTrace]
  refine ⟨60320099125467459351196541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40213399416978306234131027 60320099125467459351196541)
  ·
    refine ⟨22620037172050297256698703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60320099125467459351196541 22620037172050297256698703)
    ·
      refine ⟨33930055758075445885048055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22620037172050297256698703 33930055758075445885048055)
      ·
        refine ⟨50895083637113168827572083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33930055758075445885048055 50895083637113168827572083)
        ·
          refine ⟨76342625455669753241358125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50895083637113168827572083 76342625455669753241358125)
          ·
            refine ⟨28628484545876157465509297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76342625455669753241358125 28628484545876157465509297)
            ·
              refine ⟨21471363409407118099131973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28628484545876157465509297 21471363409407118099131973)
              ·
                refine ⟨4025880639263834643587245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21471363409407118099131973 4025880639263834643587245)
                ·
                  refine ⟨1509705239723937991345217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4025880639263834643587245 1509705239723937991345217)
                  ·
                    refine ⟨1132278929792953493508913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1509705239723937991345217 1132278929792953493508913)
                    ·
                      refine ⟨849209197344715120131685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1132278929792953493508913 849209197344715120131685)
                      ·
                        rfl

theorem cell23_1653829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 3, 2, 2].length) (baseStart_1653829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653829 prefixEnd_1653829 := by exact prefixLift 1653829
  have htrace : WordTrace (prefixWord ++ tailWord_1653829) baseStart_1653829 baseEnd_1653829 := by
    simpa [prefixWord, tailWord_1653829, baseEnd_1653829] using wordTrace_append hprefix tailTrace_1653829
  have hstable : (prefixWord ++ tailWord_1653829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653829).length < 2 ^ (prefixWord ++ tailWord_1653829).sum := by decide
  have hdescent : baseEnd_1653829 < baseStart_1653829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653832 : List Nat := [2, 1, 3, 1, 1, 1, 5, 1, 3, 2, 3]
def baseStart_1653832 : Nat := 118140960795 + 1653832 * 2 ^ 59
def prefixEnd_1653832 : Nat := 4983230072969 + 3 ^ 40 * 1653832 * 2
def baseEnd_1653832 : Nat := 849210737786678608394171

theorem tailTrace_1653832 : CollatzResearch.WordTrace tailWord_1653832 prefixEnd_1653832 849210737786678608394171 := by
  unfold tailWord_1653832
  simp only [CollatzResearch.WordTrace]
  refine ⟨30160104272228295431777875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40213472362971060575703833 30160104272228295431777875)
  ·
    refine ⟨45240156408342443147666813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30160104272228295431777875 45240156408342443147666813)
    ·
      refine ⟨16965058653128416180375055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45240156408342443147666813 16965058653128416180375055)
      ·
        refine ⟨25447587979692624270562583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16965058653128416180375055 25447587979692624270562583)
        ·
          refine ⟨38171381969538936405843875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25447587979692624270562583 38171381969538936405843875)
          ·
            refine ⟨57257072954308404608765813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38171381969538936405843875 57257072954308404608765813)
            ·
              refine ⟨5367850589466412932071795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57257072954308404608765813 5367850589466412932071795)
              ·
                refine ⟨8051775884199619398107693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5367850589466412932071795 8051775884199619398107693)
                ·
                  refine ⟨3019415956574857274290385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8051775884199619398107693 3019415956574857274290385)
                  ·
                    refine ⟨2264561967431142955717789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3019415956574857274290385 2264561967431142955717789)
                    ·
                      refine ⟨849210737786678608394171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2264561967431142955717789 849210737786678608394171)
                      ·
                        rfl

theorem cell23_1653832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 1, 3, 2, 3].length) (baseStart_1653832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653832 prefixEnd_1653832 := by exact prefixLift 1653832
  have htrace : WordTrace (prefixWord ++ tailWord_1653832) baseStart_1653832 baseEnd_1653832 := by
    simpa [prefixWord, tailWord_1653832, baseEnd_1653832] using wordTrace_append hprefix tailTrace_1653832
  have hstable : (prefixWord ++ tailWord_1653832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653832).length < 2 ^ (prefixWord ++ tailWord_1653832).sum := by decide
  have hdescent : baseEnd_1653832 < baseStart_1653832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653842 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 3, 2, 4]
def baseStart_1653842 : Nat := 118140960795 + 1653842 * 2 ^ 59
def prefixEnd_1653842 : Nat := 4983230072969 + 3 ^ 40 * 1653842 * 2
def baseEnd_1653842 : Nat := 849215872593223569269125

theorem tailTrace_1653842 : CollatzResearch.WordTrace tailWord_1653842 prefixEnd_1653842 849215872593223569269125 := by
  unfold tailWord_1653842
  simp only [CollatzResearch.WordTrace]
  refine ⟨15080143318605090642854945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40213715516280241714279853 15080143318605090642854945)
  ·
    refine ⟨11310107488953817982141209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15080143318605090642854945 11310107488953817982141209)
    ·
      refine ⟨8482580616715363486605907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11310107488953817982141209 8482580616715363486605907)
      ·
        refine ⟨12723870925073045229908861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8482580616715363486605907 12723870925073045229908861)
        ·
          refine ⟨4771451596902391961215823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12723870925073045229908861 4771451596902391961215823)
          ·
            refine ⟨7157177395353587941823735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4771451596902391961215823 7157177395353587941823735)
            ·
              refine ⟨10735766093030381912735603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7157177395353587941823735 10735766093030381912735603)
              ·
                refine ⟨16103649139545572869103405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10735766093030381912735603 16103649139545572869103405)
                ·
                  refine ⟨6038868427329589825913777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16103649139545572869103405 6038868427329589825913777)
                  ·
                    refine ⟨4529151320497192369435333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6038868427329589825913777 4529151320497192369435333)
                    ·
                      refine ⟨849215872593223569269125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4529151320497192369435333 849215872593223569269125)
                      ·
                        rfl

theorem cell23_1653842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_1653842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653842 prefixEnd_1653842 := by exact prefixLift 1653842
  have htrace : WordTrace (prefixWord ++ tailWord_1653842) baseStart_1653842 baseEnd_1653842 := by
    simpa [prefixWord, tailWord_1653842, baseEnd_1653842] using wordTrace_append hprefix tailTrace_1653842
  have hstable : (prefixWord ++ tailWord_1653842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653842).length < 2 ^ (prefixWord ++ tailWord_1653842).sum := by decide
  have hdescent : baseEnd_1653842 < baseStart_1653842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653863 : List Nat := [1, 1, 5, 1, 1, 4, 1, 4, 1, 2, 2]
def baseStart_1653863 : Nat := 118140960795 + 1653863 * 2 ^ 59
def prefixEnd_1653863 : Nat := 4983230072969 + 3 ^ 40 * 1653863 * 2
def baseEnd_1653863 : Nat := 849226655686967987106529

theorem tailTrace_1653863 : CollatzResearch.WordTrace tailWord_1653863 prefixEnd_1653863 849226655686967987106529 := by
  unfold tailWord_1653863
  simp only [CollatzResearch.WordTrace]
  refine ⟨60321339207344283157934243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40214226138229522105289495 60321339207344283157934243)
  ·
    refine ⟨90482008811016424736901365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60321339207344283157934243 90482008811016424736901365)
    ·
      refine ⟨8482688326032789819084503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90482008811016424736901365 8482688326032789819084503)
      ·
        refine ⟨12724032489049184728626755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8482688326032789819084503 12724032489049184728626755)
        ·
          refine ⟨19086048733573777092940133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12724032489049184728626755 19086048733573777092940133)
          ·
            refine ⟨3578634137545083204926275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19086048733573777092940133 3578634137545083204926275)
            ·
              refine ⟨5367951206317624807389413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3578634137545083204926275 5367951206317624807389413)
              ·
                refine ⟨1006490851184554651385515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5367951206317624807389413 1006490851184554651385515)
                ·
                  refine ⟨1509736276776831977078273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1006490851184554651385515 1509736276776831977078273)
                  ·
                    refine ⟨1132302207582623982808705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1509736276776831977078273 1132302207582623982808705)
                    ·
                      refine ⟨849226655686967987106529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1132302207582623982808705 849226655686967987106529)
                      ·
                        rfl

theorem cell23_1653863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_1653863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653863 prefixEnd_1653863 := by exact prefixLift 1653863
  have htrace : WordTrace (prefixWord ++ tailWord_1653863) baseStart_1653863 baseEnd_1653863 := by
    simpa [prefixWord, tailWord_1653863, baseEnd_1653863] using wordTrace_append hprefix tailTrace_1653863
  have hstable : (prefixWord ++ tailWord_1653863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653863).length < 2 ^ (prefixWord ++ tailWord_1653863).sum := by decide
  have hdescent : baseEnd_1653863 < baseStart_1653863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653865 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 2, 7]
def baseStart_1653865 : Nat := 118140960795 + 1653865 * 2 ^ 59
def prefixEnd_1653865 : Nat := 4983230072969 + 3 ^ 40 * 1653865 * 2
def baseEnd_1653865 : Nat := 283075894216092326427173

theorem tailTrace_1653865 : CollatzResearch.WordTrace tailWord_1653865 prefixEnd_1653865 283075894216092326427173 := by
  unfold tailWord_1653865
  simp only [CollatzResearch.WordTrace]
  refine ⟨60321412153337037499507049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40214274768891358333004699 60321412153337037499507049)
  ·
    refine ⟨45241059115002778124630287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60321412153337037499507049 45241059115002778124630287)
    ·
      refine ⟨67861588672504167186945431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45241059115002778124630287 67861588672504167186945431)
      ·
        refine ⟨101792383008756250780418147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67861588672504167186945431 101792383008756250780418147)
        ·
          refine ⟨152688574513134376170627221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101792383008756250780418147 152688574513134376170627221)
          ·
            refine ⟨7157276930303173882998151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152688574513134376170627221 7157276930303173882998151)
            ·
              refine ⟨10735915395454760824497227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7157276930303173882998151 10735915395454760824497227)
              ·
                refine ⟨16103873093182141236745841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10735915395454760824497227 16103873093182141236745841)
                ·
                  refine ⟨12077904819886605927559381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16103873093182141236745841 12077904819886605927559381)
                  ·
                    refine ⟨283075894216092326427173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12077904819886605927559381 283075894216092326427173)
                    ·
                      rfl

theorem cell23_1653865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 7].length) (baseStart_1653865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653865 prefixEnd_1653865 := by exact prefixLift 1653865
  have htrace : WordTrace (prefixWord ++ tailWord_1653865) baseStart_1653865 baseEnd_1653865 := by
    simpa [prefixWord, tailWord_1653865, baseEnd_1653865] using wordTrace_append hprefix tailTrace_1653865
  have hstable : (prefixWord ++ tailWord_1653865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653865).length < 2 ^ (prefixWord ++ tailWord_1653865).sum := by decide
  have hdescent : baseEnd_1653865 < baseStart_1653865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653879 : List Nat := [1, 1, 3, 1, 1, 4, 1, 5, 2, 1, 3]
def baseStart_1653879 : Nat := 118140960795 + 1653879 * 2 ^ 59
def prefixEnd_1653879 : Nat := 4983230072969 + 3 ^ 40 * 1653879 * 2
def baseEnd_1653879 : Nat := 849234871377439924506455

theorem tailTrace_1653879 : CollatzResearch.WordTrace tailWord_1653879 prefixEnd_1653879 849234871377439924506455 := by
  unfold tailWord_1653879
  simp only [CollatzResearch.WordTrace]
  refine ⟨60321922775286317890516691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40214615183524211927011127 60321922775286317890516691)
  ·
    refine ⟨90482884162929476835775037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60321922775286317890516691 90482884162929476835775037)
    ·
      refine ⟨33931081561098553813415639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90482884162929476835775037 33931081561098553813415639)
      ·
        refine ⟨50896622341647830720123459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33931081561098553813415639 50896622341647830720123459)
        ·
          refine ⟨76344933512471746080185189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50896622341647830720123459 76344933512471746080185189)
          ·
            refine ⟨14314675033588452390034723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76344933512471746080185189 14314675033588452390034723)
            ·
              refine ⟨21472012550382678585052085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14314675033588452390034723 21472012550382678585052085)
              ·
                refine ⟨2013001176598376117348633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21472012550382678585052085 2013001176598376117348633)
                ·
                  refine ⟨1509750882448782088011475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2013001176598376117348633 1509750882448782088011475)
                  ·
                    refine ⟨2264626323673173132017213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1509750882448782088011475 2264626323673173132017213)
                    ·
                      refine ⟨849234871377439924506455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2264626323673173132017213 849234871377439924506455)
                      ·
                        rfl

theorem cell23_1653879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 2, 1, 3].length) (baseStart_1653879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653879 prefixEnd_1653879 := by exact prefixLift 1653879
  have htrace : WordTrace (prefixWord ++ tailWord_1653879) baseStart_1653879 baseEnd_1653879 := by
    simpa [prefixWord, tailWord_1653879, baseEnd_1653879] using wordTrace_append hprefix tailTrace_1653879
  have hstable : (prefixWord ++ tailWord_1653879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653879).length < 2 ^ (prefixWord ++ tailWord_1653879).sum := by decide
  have hdescent : baseEnd_1653879 < baseStart_1653879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653895 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 3, 8]
def baseStart_1653895 : Nat := 118140960795 + 1653895 * 2 ^ 59
def prefixEnd_1653895 : Nat := 4983230072969 + 3 ^ 40 * 1653895 * 2
def baseEnd_1653895 : Nat := 283081029022637287302127

theorem tailTrace_1653895 : CollatzResearch.WordTrace tailWord_1653895 prefixEnd_1653895 283081029022637287302127 := by
  unfold tailWord_1653895
  simp only [CollatzResearch.WordTrace]
  refine ⟨60322506343228352623099139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40215004228818901748732759 60322506343228352623099139)
  ·
    refine ⟨90483759514842528934648709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60322506343228352623099139 90483759514842528934648709)
    ·
      refine ⟨16965704909032974175246633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90483759514842528934648709 16965704909032974175246633)
      ·
        refine ⟨12724278681774730631434975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16965704909032974175246633 12724278681774730631434975)
        ·
          refine ⟨19086418022662095947152463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12724278681774730631434975 19086418022662095947152463)
          ·
            refine ⟨28629627033993143920728695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19086418022662095947152463 28629627033993143920728695)
            ·
              refine ⟨42944440550989715881093043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28629627033993143920728695 42944440550989715881093043)
              ·
                refine ⟨64416660826484573821639565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42944440550989715881093043 64416660826484573821639565)
                ·
                  refine ⟨24156247809931715183114837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64416660826484573821639565 24156247809931715183114837)
                  ·
                    refine ⟨283081029022637287302127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24156247809931715183114837 283081029022637287302127)
                    ·
                      rfl

theorem cell23_1653895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_1653895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653895 prefixEnd_1653895 := by exact prefixLift 1653895
  have htrace : WordTrace (prefixWord ++ tailWord_1653895) baseStart_1653895 baseEnd_1653895 := by
    simpa [prefixWord, tailWord_1653895, baseEnd_1653895] using wordTrace_append hprefix tailTrace_1653895
  have hstable : (prefixWord ++ tailWord_1653895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653895).length < 2 ^ (prefixWord ++ tailWord_1653895).sum := by decide
  have hdescent : baseEnd_1653895 < baseStart_1653895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653912 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 2, 6]
def baseStart_1653912 : Nat := 118140960795 + 1653912 * 2 ^ 59
def prefixEnd_1653912 : Nat := 4983230072969 + 3 ^ 40 * 1653912 * 2
def baseEnd_1653912 : Nat := 283083938746346098464601

theorem tailTrace_1653912 : CollatzResearch.WordTrace tailWord_1653912 prefixEnd_1653912 283083938746346098464601 := by
  unfold tailWord_1653912
  simp only [CollatzResearch.WordTrace]
  refine ⟨30161563192083382263233995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40215417589444509684311993 30161563192083382263233995)
  ·
    refine ⟨45242344788125073394850993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30161563192083382263233995 45242344788125073394850993)
    ·
      refine ⟨33931758591093805046138245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45242344788125073394850993 33931758591093805046138245)
      ·
        refine ⟨6362204735830088446150921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33931758591093805046138245 6362204735830088446150921)
        ·
          refine ⟨4771653551872566334613191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6362204735830088446150921 4771653551872566334613191)
          ·
            refine ⟨7157480327808849501919787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4771653551872566334613191 7157480327808849501919787)
            ·
              refine ⟨10736220491713274252879681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7157480327808849501919787 10736220491713274252879681)
              ·
                refine ⟨8052165368784955689659761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10736220491713274252879681 8052165368784955689659761)
                ·
                  refine ⟨6039124026588716767244821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8052165368784955689659761 6039124026588716767244821)
                  ·
                    refine ⟨283083938746346098464601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6039124026588716767244821 283083938746346098464601)
                    ·
                      rfl

theorem cell23_1653912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 2, 6].length) (baseStart_1653912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653912 prefixEnd_1653912 := by exact prefixLift 1653912
  have htrace : WordTrace (prefixWord ++ tailWord_1653912) baseStart_1653912 baseEnd_1653912 := by
    simpa [prefixWord, tailWord_1653912, baseEnd_1653912] using wordTrace_append hprefix tailTrace_1653912
  have hstable : (prefixWord ++ tailWord_1653912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653912).length < 2 ^ (prefixWord ++ tailWord_1653912).sum := by decide
  have hdescent : baseEnd_1653912 < baseStart_1653912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653930 : List Nat := [3, 1, 5, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_1653930 : Nat := 118140960795 + 1653930 * 2 ^ 59
def prefixEnd_1653930 : Nat := 4983230072969 + 3 ^ 40 * 1653930 * 2
def baseEnd_1653930 : Nat := 849261058890819224968721

theorem tailTrace_1653930 : CollatzResearch.WordTrace tailWord_1653930 prefixEnd_1653930 849261058890819224968721 := by
  unfold tailWord_1653930
  simp only [CollatzResearch.WordTrace]
  refine ⟨15080945724525388400155811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40215855265401035733748829 15080945724525388400155811)
  ·
    refine ⟨22621418586788082600233717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15080945724525388400155811 22621418586788082600233717)
    ·
      refine ⟨2120757992511382743771911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22621418586788082600233717 2120757992511382743771911)
      ·
        refine ⟨3181136988767074115657867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2120757992511382743771911 3181136988767074115657867)
        ·
          refine ⟨4771705483150611173486801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3181136988767074115657867 4771705483150611173486801)
          ·
            refine ⟨3578779112362958380115101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4771705483150611173486801 3578779112362958380115101)
            ·
              refine ⟨1342042167136109392543163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3578779112362958380115101 1342042167136109392543163)
              ·
                refine ⟨2013063250704164088814745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1342042167136109392543163 2013063250704164088814745)
                ·
                  refine ⟨1509797438028123066611059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2013063250704164088814745 1509797438028123066611059)
                  ·
                    refine ⟨2264696157042184599916589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1509797438028123066611059 2264696157042184599916589)
                    ·
                      refine ⟨849261058890819224968721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2264696157042184599916589 849261058890819224968721)
                      ·
                        rfl

theorem cell23_1653930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_1653930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653930 prefixEnd_1653930 := by exact prefixLift 1653930
  have htrace : WordTrace (prefixWord ++ tailWord_1653930) baseStart_1653930 baseEnd_1653930 := by
    simpa [prefixWord, tailWord_1653930, baseEnd_1653930] using wordTrace_append hprefix tailTrace_1653930
  have hstable : (prefixWord ++ tailWord_1653930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653930).length < 2 ^ (prefixWord ++ tailWord_1653930).sum := by decide
  have hdescent : baseEnd_1653930 < baseStart_1653930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653953 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_1653953 : Nat := 118140960795 + 1653953 * 2 ^ 59
def prefixEnd_1653953 : Nat := 4983230072969 + 3 ^ 40 * 1653953 * 2
def baseEnd_1653953 : Nat := 849272868945872634981115

theorem tailTrace_1653953 : CollatzResearch.WordTrace tailWord_1653953 prefixEnd_1653953 849272868945872634981115 := by
  unfold tailWord_1653953
  simp only [CollatzResearch.WordTrace]
  refine ⟨60324621777018228528710513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40216414518012152352473675 60324621777018228528710513)
  ·
    refine ⟨45243466332763671396532885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60324621777018228528710513 45243466332763671396532885)
    ·
      refine ⟨2120787484348297096712479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45243466332763671396532885 2120787484348297096712479)
      ·
        refine ⟨3181181226522445645068719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2120787484348297096712479 3181181226522445645068719)
        ·
          refine ⟨4771771839783668467603079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3181181226522445645068719 4771771839783668467603079)
          ·
            refine ⟨7157657759675502701404619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4771771839783668467603079 7157657759675502701404619)
            ·
              refine ⟨10736486639513254052106929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7157657759675502701404619 10736486639513254052106929)
              ·
                refine ⟨8052364979634940539080197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10736486639513254052106929 8052364979634940539080197)
                ·
                  refine ⟨1509818433681551351077537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8052364979634940539080197 1509818433681551351077537)
                  ·
                    refine ⟨1132363825261163513308153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1509818433681551351077537 1132363825261163513308153)
                    ·
                      refine ⟨849272868945872634981115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1132363825261163513308153 849272868945872634981115)
                      ·
                        rfl

theorem cell23_1653953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_1653953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653953 prefixEnd_1653953 := by exact prefixLift 1653953
  have htrace : WordTrace (prefixWord ++ tailWord_1653953) baseStart_1653953 baseEnd_1653953 := by
    simpa [prefixWord, tailWord_1653953, baseEnd_1653953] using wordTrace_append hprefix tailTrace_1653953
  have hstable : (prefixWord ++ tailWord_1653953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653953).length < 2 ^ (prefixWord ++ tailWord_1653953).sum := by decide
  have hdescent : baseEnd_1653953 < baseStart_1653953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1653976 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 7]
def baseStart_1653976 : Nat := 118140960795 + 1653976 * 2 ^ 59
def prefixEnd_1653976 : Nat := 4983230072969 + 3 ^ 40 * 1653976 * 2
def baseEnd_1653976 : Nat := 94364964333436227221501

theorem tailTrace_1653976 : CollatzResearch.WordTrace tailWord_1653976 prefixEnd_1653976 94364964333436227221501 := by
  unfold tailWord_1653976
  simp only [CollatzResearch.WordTrace]
  refine ⟨30162730327967451728398891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40216973770623268971198521 30162730327967451728398891)
  ·
    refine ⟨45244095491951177592598337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30162730327967451728398891 45244095491951177592598337)
    ·
      refine ⟨33933071618963383194448753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45244095491951177592598337 33933071618963383194448753)
      ·
        refine ⟨25449803714222537395836565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33933071618963383194448753 25449803714222537395836565)
        ·
          refine ⟨1192959549104181440429839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25449803714222537395836565 1192959549104181440429839)
          ·
            refine ⟨1789439323656272160644759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192959549104181440429839 1789439323656272160644759)
            ·
              refine ⟨2684158985484408240967139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789439323656272160644759 2684158985484408240967139)
              ·
                refine ⟨4026238478226612361450709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2684158985484408240967139 4026238478226612361450709)
                ·
                  refine ⟨94364964333436227221501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4026238478226612361450709 94364964333436227221501)
                  ·
                    rfl

theorem cell23_1653976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 7].length) (baseStart_1653976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1653976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1653976 prefixEnd_1653976 := by exact prefixLift 1653976
  have htrace : WordTrace (prefixWord ++ tailWord_1653976) baseStart_1653976 baseEnd_1653976 := by
    simpa [prefixWord, tailWord_1653976, baseEnd_1653976] using wordTrace_append hprefix tailTrace_1653976
  have hstable : (prefixWord ++ tailWord_1653976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1653976).length < 2 ^ (prefixWord ++ tailWord_1653976).sum := by decide
  have hdescent : baseEnd_1653976 < baseStart_1653976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1653976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654009 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 2, 1, 4]
def baseStart_1654009 : Nat := 118140960795 + 1654009 * 2 ^ 59
def prefixEnd_1654009 : Nat := 4983230072969 + 3 ^ 40 * 1654009 * 2
def baseEnd_1654009 : Nat := 849301623862524415880857

theorem tailTrace_1654009 : CollatzResearch.WordTrace tailWord_1654009 prefixEnd_1654009 849301623862524415880857 := by
  unfold tailWord_1654009
  simp only [CollatzResearch.WordTrace]
  refine ⟨60326664264815350092749081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40217776176543566728499387 60326664264815350092749081)
  ·
    refine ⟨45244998198611512569561811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60326664264815350092749081 45244998198611512569561811)
    ·
      refine ⟨67867497297917268854342717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45244998198611512569561811 67867497297917268854342717)
      ·
        refine ⟨25450311486718975820378519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67867497297917268854342717 25450311486718975820378519)
        ·
          refine ⟨38175467230078463730567779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25450311486718975820378519 38175467230078463730567779)
          ·
            refine ⟨57263200845117695595851669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38175467230078463730567779 57263200845117695595851669)
            ·
              refine ⟨2684212539614891981055547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 57263200845117695595851669 2684212539614891981055547)
              ·
                refine ⟨4026318809422337971583321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2684212539614891981055547 4026318809422337971583321)
                ·
                  refine ⟨3019739107066753478687491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4026318809422337971583321 3019739107066753478687491)
                  ·
                    refine ⟨4529608660600130218031237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3019739107066753478687491 4529608660600130218031237)
                    ·
                      refine ⟨849301623862524415880857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4529608660600130218031237 849301623862524415880857)
                      ·
                        rfl

theorem cell23_1654009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_1654009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654009 prefixEnd_1654009 := by exact prefixLift 1654009
  have htrace : WordTrace (prefixWord ++ tailWord_1654009) baseStart_1654009 baseEnd_1654009 := by
    simpa [prefixWord, tailWord_1654009, baseEnd_1654009] using wordTrace_append hprefix tailTrace_1654009
  have hstable : (prefixWord ++ tailWord_1654009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654009).length < 2 ^ (prefixWord ++ tailWord_1654009).sum := by decide
  have hdescent : baseEnd_1654009 < baseStart_1654009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654072 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 2, 4, 5]
def baseStart_1654072 : Nat := 118140960795 + 1654072 * 2 ^ 59
def prefixEnd_1654072 : Nat := 4983230072969 + 3 ^ 40 * 1654072 * 2
def baseEnd_1654072 : Nat := 849333973143757669393067

theorem tailTrace_1654072 : CollatzResearch.WordTrace tailWord_1654072 prefixEnd_1654072 849333973143757669393067 := by
  unfold tailWord_1654072
  simp only [CollatzResearch.WordTrace]
  refine ⟨30164481031793555926146235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40219308042391407901528313 30164481031793555926146235)
  ·
    refine ⟨45246721547690333889219353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30164481031793555926146235 45246721547690333889219353)
    ·
      refine ⟨33935041160767750416914515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45246721547690333889219353 33935041160767750416914515)
      ·
        refine ⟨50902561741151625625371773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33935041160767750416914515 50902561741151625625371773)
        ·
          refine ⟨19088460652931859609514415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50902561741151625625371773 19088460652931859609514415)
          ·
            refine ⟨28632690979397789414271623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19088460652931859609514415 28632690979397789414271623)
            ·
              refine ⟨42949036469096684121407435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28632690979397789414271623 42949036469096684121407435)
              ·
                refine ⟨64423554703645026182111153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42949036469096684121407435 64423554703645026182111153)
                ·
                  refine ⟨48317666027733769636583365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64423554703645026182111153 48317666027733769636583365)
                  ·
                    refine ⟨9059562380200081806859381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48317666027733769636583365 9059562380200081806859381)
                    ·
                      refine ⟨849333973143757669393067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9059562380200081806859381 849333973143757669393067)
                      ·
                        rfl

theorem cell23_1654072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 2, 4, 5].length) (baseStart_1654072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654072 prefixEnd_1654072 := by exact prefixLift 1654072
  have htrace : WordTrace (prefixWord ++ tailWord_1654072) baseStart_1654072 baseEnd_1654072 := by
    simpa [prefixWord, tailWord_1654072, baseEnd_1654072] using wordTrace_append hprefix tailTrace_1654072
  have hstable : (prefixWord ++ tailWord_1654072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654072).length < 2 ^ (prefixWord ++ tailWord_1654072).sum := by decide
  have hdescent : baseEnd_1654072 < baseStart_1654072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654116 : List Nat := [2, 3, 1, 1, 3, 2, 1, 4, 1, 1, 4]
def baseStart_1654116 : Nat := 118140960795 + 1654116 * 2 ^ 59
def prefixEnd_1654116 : Nat := 4983230072969 + 3 ^ 40 * 1654116 * 2
def baseEnd_1654116 : Nat := 849356566292555497242865

theorem tailTrace_1654116 : CollatzResearch.WordTrace tailWord_1654116 prefixEnd_1654116 849356566292555497242865 := by
  unfold tailWord_1654116
  simp only [CollatzResearch.WordTrace]
  refine ⟨30165283437713853683447101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40220377916951804911262801 30165283437713853683447101)
  ·
    refine ⟨11311981289142695131292663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30165283437713853683447101 11311981289142695131292663)
    ·
      refine ⟨16967971933714042696938995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11311981289142695131292663 16967971933714042696938995)
      ·
        refine ⟨25451957900571064045408493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16967971933714042696938995 25451957900571064045408493)
        ·
          refine ⟨9544484212714149017028185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25451957900571064045408493 9544484212714149017028185)
          ·
            refine ⟨7158363159535611762771139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9544484212714149017028185 7158363159535611762771139)
            ·
              refine ⟨10737544739303417644156709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7158363159535611762771139 10737544739303417644156709)
              ·
                refine ⟨2013289638619390808279383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10737544739303417644156709 2013289638619390808279383)
                ·
                  refine ⟨3019934457929086212419075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013289638619390808279383 3019934457929086212419075)
                  ·
                    refine ⟨4529901686893629318628613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3019934457929086212419075 4529901686893629318628613)
                    ·
                      refine ⟨849356566292555497242865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4529901686893629318628613 849356566292555497242865)
                      ·
                        rfl

theorem cell23_1654116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_1654116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654116 prefixEnd_1654116 := by exact prefixLift 1654116
  have htrace : WordTrace (prefixWord ++ tailWord_1654116) baseStart_1654116 baseEnd_1654116 := by
    simpa [prefixWord, tailWord_1654116, baseEnd_1654116] using wordTrace_append hprefix tailTrace_1654116
  have hstable : (prefixWord ++ tailWord_1654116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654116).length < 2 ^ (prefixWord ++ tailWord_1654116).sum := by decide
  have hdescent : baseEnd_1654116 < baseStart_1654116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654129 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 1, 2, 4]
def baseStart_1654129 : Nat := 118140960795 + 1654129 * 2 ^ 59
def prefixEnd_1654129 : Nat := 4983230072969 + 3 ^ 40 * 1654129 * 2
def baseEnd_1654129 : Nat := 849363241541063946380305

theorem tailTrace_1654129 : CollatzResearch.WordTrace tailWord_1654129 prefixEnd_1654129 849363241541063946380305 := by
  unfold tailWord_1654129
  simp only [CollatzResearch.WordTrace]
  refine ⟨60331041024380610587117441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40220694016253740391411627 60331041024380610587117441)
  ·
    refine ⟨45248280768285457940338081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60331041024380610587117441 45248280768285457940338081)
    ·
      refine ⟨33936210576214093455253561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45248280768285457940338081 33936210576214093455253561)
      ·
        refine ⟨25452157932160570091440171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33936210576214093455253561 25452157932160570091440171)
        ·
          refine ⟨38178236898240855137160257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25452157932160570091440171 38178236898240855137160257)
          ·
            refine ⟨28633677673680641352870193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38178236898240855137160257 28633677673680641352870193)
            ·
              refine ⟨21475258255260481014652645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28633677673680641352870193 21475258255260481014652645)
              ·
                refine ⟨4026610922861340190247371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21475258255260481014652645 4026610922861340190247371)
                ·
                  refine ⟨6039916384292010285371057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4026610922861340190247371 6039916384292010285371057)
                  ·
                    refine ⟨4529937288219007714028293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6039916384292010285371057 4529937288219007714028293)
                    ·
                      refine ⟨849363241541063946380305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4529937288219007714028293 849363241541063946380305)
                      ·
                        rfl

theorem cell23_1654129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_1654129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654129 prefixEnd_1654129 := by exact prefixLift 1654129
  have htrace : WordTrace (prefixWord ++ tailWord_1654129) baseStart_1654129 baseEnd_1654129 := by
    simpa [prefixWord, tailWord_1654129, baseEnd_1654129] using wordTrace_append hprefix tailTrace_1654129
  have hstable : (prefixWord ++ tailWord_1654129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654129).length < 2 ^ (prefixWord ++ tailWord_1654129).sum := by decide
  have hdescent : baseEnd_1654129 < baseStart_1654129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654199 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 2, 6]
def baseStart_1654199 : Nat := 118140960795 + 1654199 * 2 ^ 59
def prefixEnd_1654199 : Nat := 4983230072969 + 3 ^ 40 * 1654199 * 2
def baseEnd_1654199 : Nat := 283133061728959557501661

theorem tailTrace_1654199 : CollatzResearch.WordTrace tailWord_1654199 prefixEnd_1654199 283133061728959557501661 := by
  unfold tailWord_1654199
  simp only [CollatzResearch.WordTrace]
  refine ⟨60333594134127012542165651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40222396089418008361443767 60333594134127012542165651)
  ·
    refine ⟨90500391201190518813248477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60333594134127012542165651 90500391201190518813248477)
    ·
      refine ⟨33937646700446444554968179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90500391201190518813248477 33937646700446444554968179)
      ·
        refine ⟨50906470050669666832452269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33937646700446444554968179 50906470050669666832452269)
        ·
          refine ⟨19089926269001125062169601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50906470050669666832452269 19089926269001125062169601)
          ·
            refine ⟨14317444701750843796627201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19089926269001125062169601 14317444701750843796627201)
            ·
              refine ⟨10738083526313132847470401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14317444701750843796627201 10738083526313132847470401)
              ·
                refine ⟨8053562644734849635602801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10738083526313132847470401 8053562644734849635602801)
                ·
                  refine ⟨6040171983551137226702101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8053562644734849635602801 6040171983551137226702101)
                  ·
                    refine ⟨283133061728959557501661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6040171983551137226702101 283133061728959557501661)
                    ·
                      rfl

theorem cell23_1654199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 6].length) (baseStart_1654199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654199 prefixEnd_1654199 := by exact prefixLift 1654199
  have htrace : WordTrace (prefixWord ++ tailWord_1654199) baseStart_1654199 baseEnd_1654199 := by
    simpa [prefixWord, tailWord_1654199, baseEnd_1654199] using wordTrace_append hprefix tailTrace_1654199
  have hstable : (prefixWord ++ tailWord_1654199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654199).length < 2 ^ (prefixWord ++ tailWord_1654199).sum := by decide
  have hdescent : baseEnd_1654199 < baseStart_1654199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654201 : List Nat := [1, 2, 1, 4, 5, 1, 2, 2, 1, 2, 2]
def baseStart_1654201 : Nat := 118140960795 + 1654201 * 2 ^ 59
def prefixEnd_1654201 : Nat := 4983230072969 + 3 ^ 40 * 1654201 * 2
def baseEnd_1654201 : Nat := 849400212148187664679975

theorem tailTrace_1654201 : CollatzResearch.WordTrace tailWord_1654201 prefixEnd_1654201 849400212148187664679975 := by
  unfold tailWord_1654201
  simp only [CollatzResearch.WordTrace]
  refine ⟨60333667080119766883738457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40222444720079844589158971 60333667080119766883738457)
  ·
    refine ⟨45250250310089825162803843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60333667080119766883738457 45250250310089825162803843)
    ·
      refine ⟨67875375465134737744205765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45250250310089825162803843 67875375465134737744205765)
      ·
        refine ⟨12726632899712763327038581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67875375465134737744205765 12726632899712763327038581)
        ·
          refine ⟨1193121834348071561909867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12726632899712763327038581 1193121834348071561909867)
          ·
            refine ⟨1789682751522107342864801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193121834348071561909867 1789682751522107342864801)
            ·
              refine ⟨1342262063641580507148601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1789682751522107342864801 1342262063641580507148601)
              ·
                refine ⟨1006696547731185380361451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1342262063641580507148601 1006696547731185380361451)
                ·
                  refine ⟨1510044821596778070542177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1006696547731185380361451 1510044821596778070542177)
                  ·
                    refine ⟨1132533616197583552906633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1510044821596778070542177 1132533616197583552906633)
                    ·
                      refine ⟨849400212148187664679975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1132533616197583552906633 849400212148187664679975)
                      ·
                        rfl

theorem cell23_1654201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 2, 2, 1, 2, 2].length) (baseStart_1654201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654201 prefixEnd_1654201 := by exact prefixLift 1654201
  have htrace : WordTrace (prefixWord ++ tailWord_1654201) baseStart_1654201 baseEnd_1654201 := by
    simpa [prefixWord, tailWord_1654201, baseEnd_1654201] using wordTrace_append hprefix tailTrace_1654201
  have hstable : (prefixWord ++ tailWord_1654201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654201).length < 2 ^ (prefixWord ++ tailWord_1654201).sum := by decide
  have hdescent : baseEnd_1654201 < baseStart_1654201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654219 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 4]
def baseStart_1654219 : Nat := 118140960795 + 1654219 * 2 ^ 59
def prefixEnd_1654219 : Nat := 4983230072969 + 3 ^ 40 * 1654219 * 2
def baseEnd_1654219 : Nat := 849409454799968594254891

theorem tailTrace_1654219 : CollatzResearch.WordTrace tailWord_1654219 prefixEnd_1654219 849409454799968594254891 := by
  unfold tailWord_1654219
  simp only [CollatzResearch.WordTrace]
  refine ⟨60334323594054555957893711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40222882396036370638595807 60334323594054555957893711)
  ·
    refine ⟨90501485391081833936840567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60334323594054555957893711 90501485391081833936840567)
    ·
      refine ⟨135752228086622750905260851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90501485391081833936840567 135752228086622750905260851)
      ·
        refine ⟨203628342129934126357891277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135752228086622750905260851 203628342129934126357891277)
        ·
          refine ⟨76360628298725297384209229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203628342129934126357891277 76360628298725297384209229)
          ·
            refine ⟨28635235612021986519078461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76360628298725297384209229 28635235612021986519078461)
            ·
              refine ⟨10738213354508244944654423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28635235612021986519078461 10738213354508244944654423)
              ·
                refine ⟨16107320031762367416981635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10738213354508244944654423 16107320031762367416981635)
                ·
                  refine ⟨24160980047643551125472453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16107320031762367416981635 24160980047643551125472453)
                  ·
                    refine ⟨4530183758933165836026085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24160980047643551125472453 4530183758933165836026085)
                    ·
                      refine ⟨849409454799968594254891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4530183758933165836026085 849409454799968594254891)
                      ·
                        rfl

theorem cell23_1654219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 4].length) (baseStart_1654219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654219 prefixEnd_1654219 := by exact prefixLift 1654219
  have htrace : WordTrace (prefixWord ++ tailWord_1654219) baseStart_1654219 baseEnd_1654219 := by
    simpa [prefixWord, tailWord_1654219, baseEnd_1654219] using wordTrace_append hprefix tailTrace_1654219
  have hstable : (prefixWord ++ tailWord_1654219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654219).length < 2 ^ (prefixWord ++ tailWord_1654219).sum := by decide
  have hdescent : baseEnd_1654219 < baseStart_1654219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654256 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 3]
def baseStart_1654256 : Nat := 118140960795 + 1654256 * 2 ^ 59
def prefixEnd_1654256 : Nat := 4983230072969 + 3 ^ 40 * 1654256 * 2
def baseEnd_1654256 : Nat := 849428453584184949492221

theorem tailTrace_1654256 : CollatzResearch.WordTrace tailWord_1654256 prefixEnd_1654256 849428453584184949492221 := by
  unfold tailWord_1654256
  simp only [CollatzResearch.WordTrace]
  refine ⟨30167836547460255638495311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40223782063280340851327081 30167836547460255638495311)
  ·
    refine ⟨45251754821190383457742967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30167836547460255638495311 45251754821190383457742967)
    ·
      refine ⟨67877632231785575186614451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45251754821190383457742967 67877632231785575186614451)
      ·
        refine ⟨101816448347678362779921677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67877632231785575186614451 101816448347678362779921677)
        ·
          refine ⟨38181168130379386042470629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101816448347678362779921677 38181168130379386042470629)
          ·
            refine ⟨7158969024446134882963243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38181168130379386042470629 7158969024446134882963243)
            ·
              refine ⟨10738453536669202324444865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7158969024446134882963243 10738453536669202324444865)
              ·
                refine ⟨8053840152501901743333649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10738453536669202324444865 8053840152501901743333649)
                ·
                  refine ⟨6040380114376426307500237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8053840152501901743333649 6040380114376426307500237)
                  ·
                    refine ⟨2265142542891159865312589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6040380114376426307500237 2265142542891159865312589)
                    ·
                      refine ⟨849428453584184949492221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2265142542891159865312589 849428453584184949492221)
                      ·
                        rfl

theorem cell23_1654256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 2, 3, 3].length) (baseStart_1654256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654256 prefixEnd_1654256 := by exact prefixLift 1654256
  have htrace : WordTrace (prefixWord ++ tailWord_1654256) baseStart_1654256 baseEnd_1654256 := by
    simpa [prefixWord, tailWord_1654256, baseEnd_1654256] using wordTrace_append hprefix tailTrace_1654256
  have hstable : (prefixWord ++ tailWord_1654256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654256).length < 2 ^ (prefixWord ++ tailWord_1654256).sum := by decide
  have hdescent : baseEnd_1654256 < baseStart_1654256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654257 : List Nat := [1, 2, 2, 2, 3, 4, 1, 2, 2, 2, 2]
def baseStart_1654257 : Nat := 118140960795 + 1654257 * 2 ^ 59
def prefixEnd_1654257 : Nat := 4983230072969 + 3 ^ 40 * 1654257 * 2
def baseEnd_1654257 : Nat := 849428967064839445579717

theorem tailTrace_1654257 : CollatzResearch.WordTrace tailWord_1654257 prefixEnd_1654257 849428967064839445579717 := by
  unfold tailWord_1654257
  simp only [CollatzResearch.WordTrace]
  refine ⟨60335709567916888447777025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40223806378611258965184683 60335709567916888447777025)
  ·
    refine ⟨45251782175937666335832769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60335709567916888447777025 45251782175937666335832769)
    ·
      refine ⟨33938836631953249751874577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45251782175937666335832769 33938836631953249751874577)
      ·
        refine ⟨25454127473964937313905933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33938836631953249751874577 25454127473964937313905933)
        ·
          refine ⟨9545297802736851492714725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25454127473964937313905933 9545297802736851492714725)
          ·
            refine ⟨1789743338013159654884011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9545297802736851492714725 1789743338013159654884011)
            ·
              refine ⟨2684615007019739482326017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789743338013159654884011 2684615007019739482326017)
              ·
                refine ⟨2013461255264804611744513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2684615007019739482326017 2013461255264804611744513)
                ·
                  refine ⟨1510095941448603458808385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2013461255264804611744513 1510095941448603458808385)
                  ·
                    refine ⟨1132571956086452594106289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1510095941448603458808385 1132571956086452594106289)
                    ·
                      refine ⟨849428967064839445579717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1132571956086452594106289 849428967064839445579717)
                      ·
                        rfl

theorem cell23_1654257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_1654257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654257 prefixEnd_1654257 := by exact prefixLift 1654257
  have htrace : WordTrace (prefixWord ++ tailWord_1654257) baseStart_1654257 baseEnd_1654257 := by
    simpa [prefixWord, tailWord_1654257, baseEnd_1654257] using wordTrace_append hprefix tailTrace_1654257
  have hstable : (prefixWord ++ tailWord_1654257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654257).length < 2 ^ (prefixWord ++ tailWord_1654257).sum := by decide
  have hdescent : baseEnd_1654257 < baseStart_1654257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654289 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 2, 8]
def baseStart_1654289 : Nat := 118140960795 + 1654289 * 2 ^ 59
def prefixEnd_1654289 : Nat := 4983230072969 + 3 ^ 40 * 1654289 * 2
def baseEnd_1654289 : Nat := 283148466148594440126523

theorem tailTrace_1654289 : CollatzResearch.WordTrace tailWord_1654289 prefixEnd_1654289 283148466148594440126523 := by
  unfold tailWord_1654289
  simp only [CollatzResearch.WordTrace]
  refine ⟨60336876703800957912941921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40224584469200638608627947 60336876703800957912941921)
  ·
    refine ⟨45252657527850718434706441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60336876703800957912941921 45252657527850718434706441)
    ·
      refine ⟨33939493145888038826029831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45252657527850718434706441 33939493145888038826029831)
      ·
        refine ⟨50909239718832058239044747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33939493145888038826029831 50909239718832058239044747)
        ·
          refine ⟨76363859578248087358567121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50909239718832058239044747 76363859578248087358567121)
          ·
            refine ⟨57272894683686065518925341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76363859578248087358567121 57272894683686065518925341)
            ·
              refine ⟨21477335506382274569597003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57272894683686065518925341 21477335506382274569597003)
              ·
                refine ⟨32216003259573411854395505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21477335506382274569597003 32216003259573411854395505)
                ·
                  refine ⟨24162002444680058890796629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32216003259573411854395505 24162002444680058890796629)
                  ·
                    refine ⟨283148466148594440126523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24162002444680058890796629 283148466148594440126523)
                    ·
                      rfl

theorem cell23_1654289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_1654289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654289 prefixEnd_1654289 := by exact prefixLift 1654289
  have htrace : WordTrace (prefixWord ++ tailWord_1654289) baseStart_1654289 baseEnd_1654289 := by
    simpa [prefixWord, tailWord_1654289, baseEnd_1654289] using wordTrace_append hprefix tailTrace_1654289
  have hstable : (prefixWord ++ tailWord_1654289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654289).length < 2 ^ (prefixWord ++ tailWord_1654289).sum := by decide
  have hdescent : baseEnd_1654289 < baseStart_1654289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654323 : List Nat := [1, 1, 1, 2, 4, 3, 3, 1, 3, 4]
def baseStart_1654323 : Nat := 118140960795 + 1654323 * 2 ^ 59
def prefixEnd_1654323 : Nat := 4983230072969 + 3 ^ 40 * 1654323 * 2
def baseEnd_1654323 : Nat := 283154285596012062451471

theorem tailTrace_1654323 : CollatzResearch.WordTrace tailWord_1654323 prefixEnd_1654323 283154285596012062451471 := by
  unfold tailWord_1654323
  simp only [CollatzResearch.WordTrace]
  refine ⟨60338116785677781719679623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40225411190451854479786415 60338116785677781719679623)
  ·
    refine ⟨90507175178516672579519435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60338116785677781719679623 90507175178516672579519435)
    ·
      refine ⟨135760762767775008869279153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90507175178516672579519435 135760762767775008869279153)
      ·
        refine ⟨101820572075831256651959365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135760762767775008869279153 101820572075831256651959365)
        ·
          refine ⟨19091357264218360622242381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101820572075831256651959365 19091357264218360622242381)
          ·
            refine ⟨7159258974081885233340893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19091357264218360622242381 7159258974081885233340893)
            ·
              refine ⟨2684722115280706962502835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7159258974081885233340893 2684722115280706962502835)
              ·
                refine ⟨4027083172921060443754253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2684722115280706962502835 4027083172921060443754253)
                ·
                  refine ⟨1510156189845397666407845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4027083172921060443754253 1510156189845397666407845)
                  ·
                    refine ⟨283154285596012062451471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1510156189845397666407845 283154285596012062451471)
                    ·
                      rfl

theorem cell23_1654323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 3, 1, 3, 4].length) (baseStart_1654323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654323 prefixEnd_1654323 := by exact prefixLift 1654323
  have htrace : WordTrace (prefixWord ++ tailWord_1654323) baseStart_1654323 baseEnd_1654323 := by
    simpa [prefixWord, tailWord_1654323, baseEnd_1654323] using wordTrace_append hprefix tailTrace_1654323
  have hstable : (prefixWord ++ tailWord_1654323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654323).length < 2 ^ (prefixWord ++ tailWord_1654323).sum := by decide
  have hdescent : baseEnd_1654323 < baseStart_1654323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654403 : List Nat := [1, 1, 1, 3, 3, 1, 1, 6, 1, 1, 4]
def baseStart_1654403 : Nat := 118140960795 + 1654403 * 2 ^ 59
def prefixEnd_1654403 : Nat := 4983230072969 + 3 ^ 40 * 1654403 * 2
def baseEnd_1654403 : Nat := 849503935240395874354045

theorem tailTrace_1654403 : CollatzResearch.WordTrace tailWord_1654403 prefixEnd_1654403 849503935240395874354045 := by
  unfold tailWord_1654403
  simp only [CollatzResearch.WordTrace]
  refine ⟨60341034625387955382591863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40227356416925303588394575 60341034625387955382591863)
  ·
    refine ⟨90511551938081933073887795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60341034625387955382591863 90511551938081933073887795)
    ·
      refine ⟨135767327907122899610831693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90511551938081933073887795 135767327907122899610831693)
      ·
        refine ⟨50912747965171087354061885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135767327907122899610831693 50912747965171087354061885)
        ·
          refine ⟨19092280486939157757773207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50912747965171087354061885 19092280486939157757773207)
          ·
            refine ⟨28638420730408736636659811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19092280486939157757773207 28638420730408736636659811)
            ·
              refine ⟨42957631095613104954989717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28638420730408736636659811 42957631095613104954989717)
              ·
                refine ⟨2013638957606864294765143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 42957631095613104954989717 2013638957606864294765143)
                ·
                  refine ⟨3020458436410296442147715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013638957606864294765143 3020458436410296442147715)
                  ·
                    refine ⟨4530687654615444663221573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3020458436410296442147715 4530687654615444663221573)
                    ·
                      refine ⟨849503935240395874354045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4530687654615444663221573 849503935240395874354045)
                      ·
                        rfl

theorem cell23_1654403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 6, 1, 1, 4].length) (baseStart_1654403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654403 prefixEnd_1654403 := by exact prefixLift 1654403
  have htrace : WordTrace (prefixWord ++ tailWord_1654403) baseStart_1654403 baseEnd_1654403 := by
    simpa [prefixWord, tailWord_1654403, baseEnd_1654403] using wordTrace_append hprefix tailTrace_1654403
  have hstable : (prefixWord ++ tailWord_1654403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654403).length < 2 ^ (prefixWord ++ tailWord_1654403).sum := by decide
  have hdescent : baseEnd_1654403 < baseStart_1654403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654407 : List Nat := [1, 1, 4, 2, 1, 5, 1, 1, 2, 3, 2]
def baseStart_1654407 : Nat := 118140960795 + 1654407 * 2 ^ 59
def prefixEnd_1654407 : Nat := 4983230072969 + 3 ^ 40 * 1654407 * 2
def baseEnd_1654407 : Nat := 849505989163013858704027

theorem tailTrace_1654407 : CollatzResearch.WordTrace tailWord_1654407 prefixEnd_1654407 849505989163013858704027 := by
  unfold tailWord_1654407
  simp only [CollatzResearch.WordTrace]
  refine ⟨60341180517373464065737475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40227453678248976043824983 60341180517373464065737475)
  ·
    refine ⟨90511770776060196098606213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60341180517373464065737475 90511770776060196098606213)
    ·
      refine ⟨16970957020511286768488665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90511770776060196098606213 16970957020511286768488665)
      ·
        refine ⟨12728217765383465076366499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16970957020511286768488665 12728217765383465076366499)
        ·
          refine ⟨19092326648075197614549749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12728217765383465076366499 19092326648075197614549749)
          ·
            refine ⟨1789905623257049776364039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19092326648075197614549749 1789905623257049776364039)
            ·
              refine ⟨2684858434885574664546059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789905623257049776364039 2684858434885574664546059)
              ·
                refine ⟨4027287652328361996819089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2684858434885574664546059 4027287652328361996819089)
                ·
                  refine ⟨3020465739246271497614317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4027287652328361996819089 3020465739246271497614317)
                  ·
                    refine ⟨1132674652217351811605369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3020465739246271497614317 1132674652217351811605369)
                    ·
                      refine ⟨849505989163013858704027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1132674652217351811605369 849505989163013858704027)
                      ·
                        rfl

theorem cell23_1654407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_1654407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654407 prefixEnd_1654407 := by exact prefixLift 1654407
  have htrace : WordTrace (prefixWord ++ tailWord_1654407) baseStart_1654407 baseEnd_1654407 := by
    simpa [prefixWord, tailWord_1654407, baseEnd_1654407] using wordTrace_append hprefix tailTrace_1654407
  have hstable : (prefixWord ++ tailWord_1654407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654407).length < 2 ^ (prefixWord ++ tailWord_1654407).sum := by decide
  have hdescent : baseEnd_1654407 < baseStart_1654407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654414 : List Nat := [4, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3]
def baseStart_1654414 : Nat := 118140960795 + 1654414 * 2 ^ 59
def prefixEnd_1654414 : Nat := 4983230072969 + 3 ^ 40 * 1654414 * 2
def baseEnd_1654414 : Nat := 849509583527595331316495

theorem tailTrace_1654414 : CollatzResearch.WordTrace tailWord_1654414 prefixEnd_1654414 849509583527595331316495 := by
  unfold tailWord_1654414
  simp only [CollatzResearch.WordTrace]
  refine ⟨7542679478543513032655287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40227623885565402840828197 7542679478543513032655287)
  ·
    refine ⟨11314019217815269548982931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7542679478543513032655287 11314019217815269548982931)
    ·
      refine ⟨16971028826722904323474397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11314019217815269548982931 16971028826722904323474397)
      ·
        refine ⟨6364135810021089121302899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16971028826722904323474397 6364135810021089121302899)
        ·
          refine ⟨9546203715031633681954349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6364135810021089121302899 9546203715031633681954349)
          ·
            refine ⟨3579826393136862630732881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9546203715031633681954349 3579826393136862630732881)
            ·
              refine ⟨2684869794852646973049661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3579826393136862630732881 2684869794852646973049661)
              ·
                refine ⟨1006826173069742614893623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2684869794852646973049661 1006826173069742614893623)
                ·
                  refine ⟨1510239259604613922340435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1006826173069742614893623 1510239259604613922340435)
                  ·
                    refine ⟨2265358889406920883510653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1510239259604613922340435 2265358889406920883510653)
                    ·
                      refine ⟨849509583527595331316495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2265358889406920883510653 849509583527595331316495)
                      ·
                        rfl

theorem cell23_1654414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_1654414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654414 prefixEnd_1654414 := by exact prefixLift 1654414
  have htrace : WordTrace (prefixWord ++ tailWord_1654414) baseStart_1654414 baseEnd_1654414 := by
    simpa [prefixWord, tailWord_1654414, baseEnd_1654414] using wordTrace_append hprefix tailTrace_1654414
  have hstable : (prefixWord ++ tailWord_1654414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654414).length < 2 ^ (prefixWord ++ tailWord_1654414).sum := by decide
  have hdescent : baseEnd_1654414 < baseStart_1654414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654454 : List Nat := [5, 1, 3, 1, 1, 2, 2, 2, 1, 1, 4]
def baseStart_1654454 : Nat := 118140960795 + 1654454 * 2 ^ 59
def prefixEnd_1654454 : Nat := 4983230072969 + 3 ^ 40 * 1654454 * 2
def baseEnd_1654454 : Nat := 849530122753775174816311

theorem tailTrace_1654454 : CollatzResearch.WordTrace tailWord_1654454 prefixEnd_1654454 849530122753775174816311 := by
  unfold tailWord_1654454
  simp only [CollatzResearch.WordTrace]
  refine ⟨3771430921762699443293651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40228596498802127395132277 3771430921762699443293651)
  ·
    refine ⟨5657146382644049164940477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3771430921762699443293651 5657146382644049164940477)
    ·
      refine ⟨2121429893491518436852679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5657146382644049164940477 2121429893491518436852679)
      ·
        refine ⟨3182144840237277655279019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121429893491518436852679 3182144840237277655279019)
        ·
          refine ⟨4773217260355916482918529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3182144840237277655279019 4773217260355916482918529)
          ·
            refine ⟨3579912945266937362188897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4773217260355916482918529 3579912945266937362188897)
            ·
              refine ⟨2684934708950203021641673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3579912945266937362188897 2684934708950203021641673)
              ·
                refine ⟨2013701031712652266231255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2684934708950203021641673 2013701031712652266231255)
                ·
                  refine ⟨3020551547568978399346883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013701031712652266231255 3020551547568978399346883)
                  ·
                    refine ⟨4530827321353467599020325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3020551547568978399346883 4530827321353467599020325)
                    ·
                      refine ⟨849530122753775174816311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4530827321353467599020325 849530122753775174816311)
                      ·
                        rfl

theorem cell23_1654454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_1654454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654454 prefixEnd_1654454 := by exact prefixLift 1654454
  have htrace : WordTrace (prefixWord ++ tailWord_1654454) baseStart_1654454 baseEnd_1654454 := by
    simpa [prefixWord, tailWord_1654454, baseEnd_1654454] using wordTrace_append hprefix tailTrace_1654454
  have hstable : (prefixWord ++ tailWord_1654454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654454).length < 2 ^ (prefixWord ++ tailWord_1654454).sum := by decide
  have hdescent : baseEnd_1654454 < baseStart_1654454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654456 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 2, 7]
def baseStart_1654456 : Nat := 118140960795 + 1654456 * 2 ^ 59
def prefixEnd_1654456 : Nat := 4983230072969 + 3 ^ 40 * 1654456 * 2
def baseEnd_1654456 : Nat := 283177049905028055663767

theorem tailTrace_1654456 : CollatzResearch.WordTrace tailWord_1654456 prefixEnd_1654456 283177049905028055663767 := by
  unfold tailWord_1654456
  simp only [CollatzResearch.WordTrace]
  refine ⟨30171483847097972717135611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40228645129463963622847481 30171483847097972717135611)
  ·
    refine ⟨45257225770646959075703417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30171483847097972717135611 45257225770646959075703417)
    ·
      refine ⟨33942919327985219306777563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45257225770646959075703417 33942919327985219306777563)
      ·
        refine ⟨50914378991977828960166345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33942919327985219306777563 50914378991977828960166345)
        ·
          refine ⟨38185784243983371720124759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50914378991977828960166345 38185784243983371720124759)
          ·
            refine ⟨57278676365975057580187139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38185784243983371720124759 57278676365975057580187139)
            ·
              refine ⟨85918014548962586370280709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57278676365975057580187139 85918014548962586370280709)
              ·
                refine ⟨16109627727930484944427633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85918014548962586370280709 16109627727930484944427633)
                ·
                  refine ⟨12082220795947863708320725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16109627727930484944427633 12082220795947863708320725)
                  ·
                    refine ⟨283177049905028055663767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12082220795947863708320725 283177049905028055663767)
                    ·
                      rfl

theorem cell23_1654456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2, 7].length) (baseStart_1654456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654456 prefixEnd_1654456 := by exact prefixLift 1654456
  have htrace : WordTrace (prefixWord ++ tailWord_1654456) baseStart_1654456 baseEnd_1654456 := by
    simpa [prefixWord, tailWord_1654456, baseEnd_1654456] using wordTrace_append hprefix tailTrace_1654456
  have hstable : (prefixWord ++ tailWord_1654456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654456).length < 2 ^ (prefixWord ++ tailWord_1654456).sum := by decide
  have hdescent : baseEnd_1654456 < baseStart_1654456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654460 : List Nat := [2, 2, 2, 3, 1, 4, 2, 7]
def baseStart_1654460 : Nat := 118140960795 + 1654460 * 2 ^ 59
def prefixEnd_1654460 : Nat := 4983230072969 + 3 ^ 40 * 1654460 * 2
def baseEnd_1654460 : Nat := 31464192727322301901529

theorem tailTrace_1654460 : CollatzResearch.WordTrace tailWord_1654460 prefixEnd_1654460 31464192727322301901529 := by
  unfold tailWord_1654460
  simp only [CollatzResearch.WordTrace]
  refine ⟨30171556793090727058708417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40228742390787636078277889 30171556793090727058708417)
  ·
    refine ⟨22628667594818045294031313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30171556793090727058708417 22628667594818045294031313)
    ·
      refine ⟨16971500696113533970523485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22628667594818045294031313 16971500696113533970523485)
      ·
        refine ⟨6364312761042575238946307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16971500696113533970523485 6364312761042575238946307)
        ·
          refine ⟨9546469141563862858419461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6364312761042575238946307 9546469141563862858419461)
          ·
            refine ⟨1789962964043224285953649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9546469141563862858419461 1789962964043224285953649)
            ·
              refine ⟨1342472223032418214465237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1789962964043224285953649 1342472223032418214465237)
              ·
                refine ⟨31464192727322301901529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1342472223032418214465237 31464192727322301901529)
                ·
                  rfl

theorem cell23_1654460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 7].length) (baseStart_1654460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654460 prefixEnd_1654460 := by exact prefixLift 1654460
  have htrace : WordTrace (prefixWord ++ tailWord_1654460) baseStart_1654460 baseEnd_1654460 := by
    simpa [prefixWord, tailWord_1654460, baseEnd_1654460] using wordTrace_append hprefix tailTrace_1654460
  have hstable : (prefixWord ++ tailWord_1654460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654460).length < 2 ^ (prefixWord ++ tailWord_1654460).sum := by decide
  have hdescent : baseEnd_1654460 < baseStart_1654460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654504 : List Nat := [2, 1, 4, 1, 3, 1, 4, 1, 2, 1, 3]
def baseStart_1654504 : Nat := 118140960795 + 1654504 * 2 ^ 59
def prefixEnd_1654504 : Nat := 4983230072969 + 3 ^ 40 * 1654504 * 2
def baseEnd_1654504 : Nat := 849555796786499979191081

theorem tailTrace_1654504 : CollatzResearch.WordTrace tailWord_1654504 prefixEnd_1654504 849555796786499979191081 := by
  unfold tailWord_1654504
  simp only [CollatzResearch.WordTrace]
  refine ⟨30172359199011024816009283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40229812265348033088012377 30172359199011024816009283)
  ·
    refine ⟨45258538798516537224013925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30172359199011024816009283 45258538798516537224013925)
    ·
      refine ⟨8485976024721850729502611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45258538798516537224013925 8485976024721850729502611)
      ·
        refine ⟨12728964037082776094253917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8485976024721850729502611 12728964037082776094253917)
        ·
          refine ⟨4773361513906041035345219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12728964037082776094253917 4773361513906041035345219)
          ·
            refine ⟨7160042270859061553017829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4773361513906041035345219 7160042270859061553017829)
            ·
              refine ⟨1342507925786074041190843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7160042270859061553017829 1342507925786074041190843)
              ·
                refine ⟨2013761888679111061786265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1342507925786074041190843 2013761888679111061786265)
                ·
                  refine ⟨1510321416509333296339699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2013761888679111061786265 1510321416509333296339699)
                  ·
                    refine ⟨2265482124763999944509549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1510321416509333296339699 2265482124763999944509549)
                    ·
                      refine ⟨849555796786499979191081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2265482124763999944509549 849555796786499979191081)
                      ·
                        rfl

theorem cell23_1654504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 2, 1, 3].length) (baseStart_1654504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654504 prefixEnd_1654504 := by exact prefixLift 1654504
  have htrace : WordTrace (prefixWord ++ tailWord_1654504) baseStart_1654504 baseEnd_1654504 := by
    simpa [prefixWord, tailWord_1654504, baseEnd_1654504] using wordTrace_append hprefix tailTrace_1654504
  have hstable : (prefixWord ++ tailWord_1654504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654504).length < 2 ^ (prefixWord ++ tailWord_1654504).sum := by decide
  have hdescent : baseEnd_1654504 < baseStart_1654504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654513 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 2, 1, 5]
def baseStart_1654513 : Nat := 118140960795 + 1654513 * 2 ^ 59
def prefixEnd_1654513 : Nat := 4983230072969 + 3 ^ 40 * 1654513 * 2
def baseEnd_1654513 : Nat := 849560418112390443978539

theorem tailTrace_1654513 : CollatzResearch.WordTrace tailWord_1654513 prefixEnd_1654513 849560418112390443978539 := by
  unfold tailWord_1654513
  simp only [CollatzResearch.WordTrace]
  refine ⟨60345046654989444169096193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40230031103326296112730795 60345046654989444169096193)
  ·
    refine ⟨45258784991242083126822145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60345046654989444169096193 45258784991242083126822145)
    ·
      refine ⟨33944088743431562345116609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45258784991242083126822145 33944088743431562345116609)
      ·
        refine ⟨25458066557573671758837457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33944088743431562345116609 25458066557573671758837457)
        ·
          refine ⟨19093549918180253819128093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25458066557573671758837457 19093549918180253819128093)
          ·
            refine ⟨7160081219317595182173035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19093549918180253819128093 7160081219317595182173035)
            ·
              refine ⟨10740121828976392773259553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7160081219317595182173035 10740121828976392773259553)
              ·
                refine ⟨8055091371732294579944665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10740121828976392773259553 8055091371732294579944665)
                ·
                  refine ⟨6041318528799220934958499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8055091371732294579944665 6041318528799220934958499)
                  ·
                    refine ⟨9061977793198831402437749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6041318528799220934958499 9061977793198831402437749)
                    ·
                      refine ⟨849560418112390443978539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9061977793198831402437749 849560418112390443978539)
                      ·
                        rfl

theorem cell23_1654513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_1654513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654513 prefixEnd_1654513 := by exact prefixLift 1654513
  have htrace : WordTrace (prefixWord ++ tailWord_1654513) baseStart_1654513 baseEnd_1654513 := by
    simpa [prefixWord, tailWord_1654513, baseEnd_1654513] using wordTrace_append hprefix tailTrace_1654513
  have hstable : (prefixWord ++ tailWord_1654513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654513).length < 2 ^ (prefixWord ++ tailWord_1654513).sum := by decide
  have hdescent : baseEnd_1654513 < baseStart_1654513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654530 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1654530 : Nat := 118140960795 + 1654530 * 2 ^ 59
def prefixEnd_1654530 : Nat := 4983230072969 + 3 ^ 40 * 1654530 * 2
def baseEnd_1654530 : Nat := 849569147283516877465961

theorem tailTrace_1654530 : CollatzResearch.WordTrace tailWord_1654530 prefixEnd_1654530 849569147283516877465961 := by
  unfold tailWord_1654530
  simp only [CollatzResearch.WordTrace]
  refine ⟨15086416673981964018116261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40230444463951904048310029 15086416673981964018116261)
  ·
    refine ⟨2828703126371618253396799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15086416673981964018116261 2828703126371618253396799)
    ·
      refine ⟨4243054689557427380095199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2828703126371618253396799 4243054689557427380095199)
      ·
        refine ⟨6364582034336141070142799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4243054689557427380095199 6364582034336141070142799)
        ·
          refine ⟨9546873051504211605214199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6364582034336141070142799 9546873051504211605214199)
          ·
            refine ⟨14320309577256317407821299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9546873051504211605214199 14320309577256317407821299)
            ·
              refine ⟨21480464365884476111731949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14320309577256317407821299 21480464365884476111731949)
              ·
                refine ⟨8055174137206678541899481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21480464365884476111731949 8055174137206678541899481)
                ·
                  refine ⟨6041380602905008906424611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8055174137206678541899481 6041380602905008906424611)
                  ·
                    refine ⟨9062070904357513359636917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6041380602905008906424611 9062070904357513359636917)
                    ·
                      refine ⟨849569147283516877465961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9062070904357513359636917 849569147283516877465961)
                      ·
                        rfl

theorem cell23_1654530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1654530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654530 prefixEnd_1654530 := by exact prefixLift 1654530
  have htrace : WordTrace (prefixWord ++ tailWord_1654530) baseStart_1654530 baseEnd_1654530 := by
    simpa [prefixWord, tailWord_1654530, baseEnd_1654530] using wordTrace_append hprefix tailTrace_1654530
  have hstable : (prefixWord ++ tailWord_1654530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654530).length < 2 ^ (prefixWord ++ tailWord_1654530).sum := by decide
  have hdescent : baseEnd_1654530 < baseStart_1654530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654560 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1654560 : Nat := 118140960795 + 1654560 * 2 ^ 59
def prefixEnd_1654560 : Nat := 4983230072969 + 3 ^ 40 * 1654560 * 2
def baseEnd_1654560 : Nat := 849584551703151760090823

theorem tailTrace_1654560 : CollatzResearch.WordTrace tailWord_1654560 prefixEnd_1654560 849584551703151760090823 := by
  unfold tailWord_1654560
  simp only [CollatzResearch.WordTrace]
  refine ⟨30173380442909585598028567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40231173923879447464038089 30173380442909585598028567)
  ·
    refine ⟨45260070664364378397042851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30173380442909585598028567 45260070664364378397042851)
    ·
      refine ⟨67890105996546567595564277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45260070664364378397042851 67890105996546567595564277)
      ·
        refine ⟨6364697437176240712084151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67890105996546567595564277 6364697437176240712084151)
        ·
          refine ⟨9547046155764361068126227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6364697437176240712084151 9547046155764361068126227)
          ·
            refine ⟨14320569233646541602189341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9547046155764361068126227 14320569233646541602189341)
            ·
              refine ⟨5370213462617453100821003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14320569233646541602189341 5370213462617453100821003)
              ·
                refine ⟨8055320193926179651231505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5370213462617453100821003 8055320193926179651231505)
                ·
                  refine ⟨6041490145444634738423629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8055320193926179651231505 6041490145444634738423629)
                  ·
                    refine ⟨2265558804541738026908861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6041490145444634738423629 2265558804541738026908861)
                    ·
                      refine ⟨849584551703151760090823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2265558804541738026908861 849584551703151760090823)
                      ·
                        rfl

theorem cell23_1654560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1654560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654560 prefixEnd_1654560 := by exact prefixLift 1654560
  have htrace : WordTrace (prefixWord ++ tailWord_1654560) baseStart_1654560 baseEnd_1654560 := by
    simpa [prefixWord, tailWord_1654560, baseEnd_1654560] using wordTrace_append hprefix tailTrace_1654560
  have hstable : (prefixWord ++ tailWord_1654560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654560).length < 2 ^ (prefixWord ++ tailWord_1654560).sum := by decide
  have hdescent : baseEnd_1654560 < baseStart_1654560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654563 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 4, 5]
def baseStart_1654563 : Nat := 118140960795 + 1654563 * 2 ^ 59
def prefixEnd_1654563 : Nat := 4983230072969 + 3 ^ 40 * 1654563 * 2
def baseEnd_1654563 : Nat := 283195364048371749451103

theorem tailTrace_1654563 : CollatzResearch.WordTrace tailWord_1654563 prefixEnd_1654563 283195364048371749451103 := by
  unfold tailWord_1654563
  simp only [CollatzResearch.WordTrace]
  refine ⟨60346870304808302708416343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40231246869872201805610895 60346870304808302708416343)
  ·
    refine ⟨90520305457212454062624515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60346870304808302708416343 90520305457212454062624515)
    ·
      refine ⟨135780458185818681093936773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90520305457212454062624515 135780458185818681093936773)
      ·
        refine ⟨25458835909841002705113145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135780458185818681093936773 25458835909841002705113145)
        ·
          refine ⟨19094126932380752028834859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25458835909841002705113145 19094126932380752028834859)
          ·
            refine ⟨28641190398571128043252289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19094126932380752028834859 28641190398571128043252289)
            ·
              refine ⟨21480892798928346032439217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28641190398571128043252289 21480892798928346032439217)
              ·
                refine ⟨16110669599196259524329413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21480892798928346032439217 16110669599196259524329413)
                ·
                  refine ⟨3020750549849298660811765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16110669599196259524329413 3020750549849298660811765)
                  ·
                    refine ⟨283195364048371749451103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3020750549849298660811765 283195364048371749451103)
                    ·
                      rfl

theorem cell23_1654563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 4, 5].length) (baseStart_1654563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654563 prefixEnd_1654563 := by exact prefixLift 1654563
  have htrace : WordTrace (prefixWord ++ tailWord_1654563) baseStart_1654563 baseEnd_1654563 := by
    simpa [prefixWord, tailWord_1654563, baseEnd_1654563] using wordTrace_append hprefix tailTrace_1654563
  have hstable : (prefixWord ++ tailWord_1654563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654563).length < 2 ^ (prefixWord ++ tailWord_1654563).sum := by decide
  have hdescent : baseEnd_1654563 < baseStart_1654563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654654 : List Nat := [4, 2, 3, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1654654 : Nat := 118140960795 + 1654654 * 2 ^ 59
def prefixEnd_1654654 : Nat := 4983230072969 + 3 ^ 40 * 1654654 * 2
def baseEnd_1654654 : Nat := 849632818884674392315391

theorem tailTrace_1654654 : CollatzResearch.WordTrace tailWord_1654654 prefixEnd_1654654 849632818884674392315391 := by
  unfold tailWord_1654654
  simp only [CollatzResearch.WordTrace]
  refine ⟨7543773668434828156247377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40233459564985750166652677 7543773668434828156247377)
  ·
    refine ⟨5657830251326121117185533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7543773668434828156247377 5657830251326121117185533)
    ·
      refine ⟨2121686344247295418944575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5657830251326121117185533 2121686344247295418944575)
      ·
        refine ⟨3182529516370943128416863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121686344247295418944575 3182529516370943128416863)
        ·
          refine ⟨4773794274556414692625295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3182529516370943128416863 4773794274556414692625295)
          ·
            refine ⟨7160691411834622038937943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4773794274556414692625295 7160691411834622038937943)
            ·
              refine ⟨10741037117751933058406915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7160691411834622038937943 10741037117751933058406915)
              ·
                refine ⟨16111555676627899587610373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10741037117751933058406915 16111555676627899587610373)
                ·
                  refine ⟨3020916689367731172676945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16111555676627899587610373 3020916689367731172676945)
                  ·
                    refine ⟨2265687517025798379507709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3020916689367731172676945 2265687517025798379507709)
                    ·
                      refine ⟨849632818884674392315391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2265687517025798379507709 849632818884674392315391)
                      ·
                        rfl

theorem cell23_1654654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1654654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654654 prefixEnd_1654654 := by exact prefixLift 1654654
  have htrace : WordTrace (prefixWord ++ tailWord_1654654) baseStart_1654654 baseEnd_1654654 := by
    simpa [prefixWord, tailWord_1654654, baseEnd_1654654] using wordTrace_append hprefix tailTrace_1654654
  have hstable : (prefixWord ++ tailWord_1654654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654654).length < 2 ^ (prefixWord ++ tailWord_1654654).sum := by decide
  have hdescent : baseEnd_1654654 < baseStart_1654654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654674 : List Nat := [3, 2, 3, 2, 1, 1, 4, 1, 6]
def baseStart_1654674 : Nat := 118140960795 + 1654674 * 2 ^ 59
def prefixEnd_1654674 : Nat := 4983230072969 + 3 ^ 40 * 1654674 * 2
def baseEnd_1654674 : Nat := 94404787610862701562811

theorem tailTrace_1654674 : CollatzResearch.WordTrace tailWord_1654674 prefixEnd_1654674 94404787610862701562811 := by
  unfold tailWord_1654674
  simp only [CollatzResearch.WordTrace]
  refine ⟨15087729701851542166426769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40233945871604112443804717 15087729701851542166426769)
  ·
    refine ⟨11315797276388656624820077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15087729701851542166426769 11315797276388656624820077)
    ·
      refine ⟨4243423978645746234307529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11315797276388656624820077 4243423978645746234307529)
      ·
        refine ⟨3182567983984309675730647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4243423978645746234307529 3182567983984309675730647)
        ·
          refine ⟨4773851975976464513595971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3182567983984309675730647 4773851975976464513595971)
          ·
            refine ⟨7160777963964696770393957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4773851975976464513595971 7160777963964696770393957)
            ·
              refine ⟨1342645868243380644448867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7160777963964696770393957 1342645868243380644448867)
              ·
                refine ⟨2013968802365070966673301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1342645868243380644448867 2013968802365070966673301)
                ·
                  refine ⟨94404787610862701562811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2013968802365070966673301 94404787610862701562811)
                  ·
                    rfl

theorem cell23_1654674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 6].length) (baseStart_1654674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654674 prefixEnd_1654674 := by exact prefixLift 1654674
  have htrace : WordTrace (prefixWord ++ tailWord_1654674) baseStart_1654674 baseEnd_1654674 := by
    simpa [prefixWord, tailWord_1654674, baseEnd_1654674] using wordTrace_append hprefix tailTrace_1654674
  have hstable : (prefixWord ++ tailWord_1654674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654674).length < 2 ^ (prefixWord ++ tailWord_1654674).sum := by decide
  have hdescent : baseEnd_1654674 < baseStart_1654674 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654677 : List Nat := [1, 3, 2, 1, 1, 3, 1, 2, 4, 3, 2]
def baseStart_1654677 : Nat := 118140960795 + 1654677 * 2 ^ 59
def prefixEnd_1654677 : Nat := 4983230072969 + 3 ^ 40 * 1654677 * 2
def baseEnd_1654677 : Nat := 849644628939727802327785

theorem tailTrace_1654677 : CollatzResearch.WordTrace tailWord_1654677 prefixEnd_1654677 849644628939727802327785 := by
  unfold tailWord_1654677
  simp only [CollatzResearch.WordTrace]
  refine ⟨60351028226395300178066285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40234018817596866785377523 60351028226395300178066285)
  ·
    refine ⟨22631635584898237566774857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60351028226395300178066285 22631635584898237566774857)
    ·
      refine ⟨16973726688673678175081143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22631635584898237566774857 16973726688673678175081143)
      ·
        refine ⟨25460590033010517262621715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16973726688673678175081143 25460590033010517262621715)
        ·
          refine ⟨38190885049515775893932573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25460590033010517262621715 38190885049515775893932573)
          ·
            refine ⟨14321581893568415960224715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38190885049515775893932573 14321581893568415960224715)
            ·
              refine ⟨21482372840352623940337073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14321581893568415960224715 21482372840352623940337073)
              ·
                refine ⟨16111779630264467955252805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21482372840352623940337073 16111779630264467955252805)
                ·
                  refine ⟨3020958680674587741609901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16111779630264467955252805 3020958680674587741609901)
                  ·
                    refine ⟨1132859505252970403103713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3020958680674587741609901 1132859505252970403103713)
                    ·
                      refine ⟨849644628939727802327785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1132859505252970403103713 849644628939727802327785)
                      ·
                        rfl

theorem cell23_1654677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_1654677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654677 prefixEnd_1654677 := by exact prefixLift 1654677
  have htrace : WordTrace (prefixWord ++ tailWord_1654677) baseStart_1654677 baseEnd_1654677 := by
    simpa [prefixWord, tailWord_1654677, baseEnd_1654677] using wordTrace_append hprefix tailTrace_1654677
  have hstable : (prefixWord ++ tailWord_1654677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654677).length < 2 ^ (prefixWord ++ tailWord_1654677).sum := by decide
  have hdescent : baseEnd_1654677 < baseStart_1654677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654687 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 3, 5]
def baseStart_1654687 : Nat := 118140960795 + 1654687 * 2 ^ 59
def prefixEnd_1654687 : Nat := 4983230072969 + 3 ^ 40 * 1654687 * 2
def baseEnd_1654687 : Nat := 283216587915424254400913

theorem tailTrace_1654687 : CollatzResearch.WordTrace tailWord_1654687 prefixEnd_1654687 283216587915424254400913 := by
  unfold tailWord_1654687
  simp only [CollatzResearch.WordTrace]
  refine ⟨60351392956359071885930315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40234261970906047923953543 60351392956359071885930315)
  ·
    refine ⟨90527089434538607828895473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60351392956359071885930315 90527089434538607828895473)
    ·
      refine ⟨67895317075903955871671605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90527089434538607828895473 67895317075903955871671605)
      ·
        refine ⟨6365185975865995862969213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67895317075903955871671605 6365185975865995862969213)
        ·
          refine ⟨2386944740949748448613455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6365185975865995862969213 2386944740949748448613455)
          ·
            refine ⟨3580417111424622672920183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2386944740949748448613455 3580417111424622672920183)
            ·
              refine ⟨5370625667136934009380275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3580417111424622672920183 5370625667136934009380275)
              ·
                refine ⟨8055938500705401014070413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5370625667136934009380275 8055938500705401014070413)
                ·
                  refine ⟨3020976937764525380276405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8055938500705401014070413 3020976937764525380276405)
                  ·
                    refine ⟨283216587915424254400913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3020976937764525380276405 283216587915424254400913)
                    ·
                      rfl

theorem cell23_1654687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 3, 5].length) (baseStart_1654687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654687 prefixEnd_1654687 := by exact prefixLift 1654687
  have htrace : WordTrace (prefixWord ++ tailWord_1654687) baseStart_1654687 baseEnd_1654687 := by
    simpa [prefixWord, tailWord_1654687, baseEnd_1654687] using wordTrace_append hprefix tailTrace_1654687
  have hstable : (prefixWord ++ tailWord_1654687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654687).length < 2 ^ (prefixWord ++ tailWord_1654687).sum := by decide
  have hdescent : baseEnd_1654687 < baseStart_1654687 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654718 : List Nat := [4, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3]
def baseStart_1654718 : Nat := 118140960795 + 1654718 * 2 ^ 59
def prefixEnd_1654718 : Nat := 4983230072969 + 3 ^ 40 * 1654718 * 2
def baseEnd_1654718 : Nat := 849665681646562141915097

theorem tailTrace_1654718 : CollatzResearch.WordTrace tailWord_1654718 prefixEnd_1654718 849665681646562141915097 := by
  unfold tailWord_1654718
  simp only [CollatzResearch.WordTrace]
  refine ⟨7544065452405845522538601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40235015746164509453539205 7544065452405845522538601)
  ·
    refine ⟨5658049089304384141903951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7544065452405845522538601 5658049089304384141903951)
    ·
      refine ⟨8487073633956576212855927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5658049089304384141903951 8487073633956576212855927)
      ·
        refine ⟨12730610450934864319283891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8487073633956576212855927 12730610450934864319283891)
        ·
          refine ⟨19095915676402296478925837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12730610450934864319283891 19095915676402296478925837)
          ·
            refine ⟨7160968378650861179597189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19095915676402296478925837 7160968378650861179597189)
            ·
              refine ⟨1342681570997036471174473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7160968378650861179597189 1342681570997036471174473)
              ·
                refine ⟨1007011178247777353380855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1342681570997036471174473 1007011178247777353380855)
                ·
                  refine ⟨1510516767371666030071283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007011178247777353380855 1510516767371666030071283)
                  ·
                    refine ⟨2265775151057499045106925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1510516767371666030071283 2265775151057499045106925)
                    ·
                      refine ⟨849665681646562141915097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2265775151057499045106925 849665681646562141915097)
                      ·
                        rfl

theorem cell23_1654718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_1654718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654718 prefixEnd_1654718 := by exact prefixLift 1654718
  have htrace : WordTrace (prefixWord ++ tailWord_1654718) baseStart_1654718 baseEnd_1654718 := by
    simpa [prefixWord, tailWord_1654718, baseEnd_1654718] using wordTrace_append hprefix tailTrace_1654718
  have hstable : (prefixWord ++ tailWord_1654718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654718).length < 2 ^ (prefixWord ++ tailWord_1654718).sum := by decide
  have hdescent : baseEnd_1654718 < baseStart_1654718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654720 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 4]
def baseStart_1654720 : Nat := 118140960795 + 1654720 * 2 ^ 59
def prefixEnd_1654720 : Nat := 4983230072969 + 3 ^ 40 * 1654720 * 2
def baseEnd_1654720 : Nat := 849666708607871134090087

theorem tailTrace_1654720 : CollatzResearch.WordTrace tailWord_1654720 prefixEnd_1654720 849666708607871134090087 := by
  unfold tailWord_1654720
  simp only [CollatzResearch.WordTrace]
  refine ⟨30176298282619759260940807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40235064376826345681254409 30176298282619759260940807)
  ·
    refine ⟨45264447423929638891411211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30176298282619759260940807 45264447423929638891411211)
    ·
      refine ⟨67896671135894458337116817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45264447423929638891411211 67896671135894458337116817)
      ·
        refine ⟨50922503351920843752837613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67896671135894458337116817 50922503351920843752837613)
        ·
          refine ⟨19095938756970316407314105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50922503351920843752837613 19095938756970316407314105)
          ·
            refine ⟨14321954067727737305485579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19095938756970316407314105 14321954067727737305485579)
            ·
              refine ⟨21482931101591605958228369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14321954067727737305485579 21482931101591605958228369)
              ·
                refine ⟨16112198326193704468671277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21482931101591605958228369 16112198326193704468671277)
                ·
                  refine ⟨6042074372322639175751729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16112198326193704468671277 6042074372322639175751729)
                  ·
                    refine ⟨4531555779241979381813797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6042074372322639175751729 4531555779241979381813797)
                    ·
                      refine ⟨849666708607871134090087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4531555779241979381813797 849666708607871134090087)
                      ·
                        rfl

theorem cell23_1654720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_1654720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654720 prefixEnd_1654720 := by exact prefixLift 1654720
  have htrace : WordTrace (prefixWord ++ tailWord_1654720) baseStart_1654720 baseEnd_1654720 := by
    simpa [prefixWord, tailWord_1654720, baseEnd_1654720] using wordTrace_append hprefix tailTrace_1654720
  have hstable : (prefixWord ++ tailWord_1654720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654720).length < 2 ^ (prefixWord ++ tailWord_1654720).sum := by decide
  have hdescent : baseEnd_1654720 < baseStart_1654720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654730 : List Nat := [3, 1, 2, 1, 2, 1, 5, 8]
def baseStart_1654730 : Nat := 118140960795 + 1654730 * 2 ^ 59
def prefixEnd_1654730 : Nat := 4983230072969 + 3 ^ 40 * 1654730 * 2
def baseEnd_1654730 : Nat := 31469327533867262776483

theorem tailTrace_1654730 : CollatzResearch.WordTrace tailWord_1654730 prefixEnd_1654730 31469327533867262776483 := by
  unfold tailWord_1654730
  simp only [CollatzResearch.WordTrace]
  refine ⟨15088240323800822557436411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40235307530135526819830429 15088240323800822557436411)
  ·
    refine ⟨22632360485701233836154617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15088240323800822557436411 22632360485701233836154617)
    ·
      refine ⟨16974270364275925377115963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22632360485701233836154617 16974270364275925377115963)
      ·
        refine ⟨25461405546413888065673945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16974270364275925377115963 25461405546413888065673945)
        ·
          refine ⟨19096054159810416049255459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25461405546413888065673945 19096054159810416049255459)
          ·
            refine ⟨28644081239715624073883189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19096054159810416049255459 28644081239715624073883189)
            ·
              refine ⟨2685382616223339756926549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28644081239715624073883189 2685382616223339756926549)
              ·
                refine ⟨31469327533867262776483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2685382616223339756926549 31469327533867262776483)
                ·
                  rfl

theorem cell23_1654730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 8].length) (baseStart_1654730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654730 prefixEnd_1654730 := by exact prefixLift 1654730
  have htrace : WordTrace (prefixWord ++ tailWord_1654730) baseStart_1654730 baseEnd_1654730 := by
    simpa [prefixWord, tailWord_1654730, baseEnd_1654730] using wordTrace_append hprefix tailTrace_1654730
  have hstable : (prefixWord ++ tailWord_1654730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654730).length < 2 ^ (prefixWord ++ tailWord_1654730).sum := by decide
  have hdescent : baseEnd_1654730 < baseStart_1654730 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654741 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 3, 2, 2]
def baseStart_1654741 : Nat := 118140960795 + 1654741 * 2 ^ 59
def prefixEnd_1654741 : Nat := 4983230072969 + 3 ^ 40 * 1654741 * 2
def baseEnd_1654741 : Nat := 849677491701615551927491

theorem tailTrace_1654741 : CollatzResearch.WordTrace tailWord_1654741 prefixEnd_1654741 849677491701615551927491 := by
  unfold tailWord_1654741
  simp only [CollatzResearch.WordTrace]
  refine ⟨60353362498163439108396077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40235574998775626072264051 60353362498163439108396077)
  ·
    refine ⟨22632510936811289665648529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60353362498163439108396077 22632510936811289665648529)
    ·
      refine ⟨16974383202608467249236397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22632510936811289665648529 16974383202608467249236397)
      ·
        refine ⟨6365393700978175218463649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16974383202608467249236397 6365393700978175218463649)
        ·
          refine ⟨4774045275733631413847737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6365393700978175218463649 4774045275733631413847737)
          ·
            refine ⟨3580533956800223560385803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4774045275733631413847737 3580533956800223560385803)
            ·
              refine ⟨5370800935200335340578705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3580533956800223560385803 5370800935200335340578705)
              ·
                refine ⟨4028100701400251505434029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5370800935200335340578705 4028100701400251505434029)
                ·
                  refine ⟨1510537763025094314537761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4028100701400251505434029 1510537763025094314537761)
                  ·
                    refine ⟨1132903322268820735903321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1510537763025094314537761 1132903322268820735903321)
                    ·
                      refine ⟨849677491701615551927491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1132903322268820735903321 849677491701615551927491)
                      ·
                        rfl

theorem cell23_1654741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_1654741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654741 prefixEnd_1654741 := by exact prefixLift 1654741
  have htrace : WordTrace (prefixWord ++ tailWord_1654741) baseStart_1654741 baseEnd_1654741 := by
    simpa [prefixWord, tailWord_1654741, baseEnd_1654741] using wordTrace_append hprefix tailTrace_1654741
  have hstable : (prefixWord ++ tailWord_1654741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654741).length < 2 ^ (prefixWord ++ tailWord_1654741).sum := by decide
  have hdescent : baseEnd_1654741 < baseStart_1654741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654788 : List Nat := [2, 3, 2, 4, 2, 1, 1, 1, 1, 2, 4]
def baseStart_1654788 : Nat := 118140960795 + 1654788 * 2 ^ 59
def prefixEnd_1654788 : Nat := 4983230072969 + 3 ^ 40 * 1654788 * 2
def baseEnd_1654788 : Nat := 849701625292376868039775

theorem tailTrace_1654788 : CollatzResearch.WordTrace tailWord_1654788 prefixEnd_1654788 849701625292376868039775 := by
  unfold tailWord_1654788
  simp only [CollatzResearch.WordTrace]
  refine ⟨30177538364496583067678509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40236717819328777423571345 30177538364496583067678509)
  ·
    refine ⟨11316576886686218650379441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30177538364496583067678509 11316576886686218650379441)
    ·
      refine ⟨8487432665014663987784581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11316576886686218650379441 8487432665014663987784581)
      ·
        refine ⟨1591393624690249497709609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8487432665014663987784581 1591393624690249497709609)
        ·
          refine ⟨1193545218517687123282207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1591393624690249497709609 1193545218517687123282207)
          ·
            refine ⟨1790317827776530684923311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193545218517687123282207 1790317827776530684923311)
            ·
              refine ⟨2685476741664796027384967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1790317827776530684923311 2685476741664796027384967)
              ·
                refine ⟨4028215112497194041077451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2685476741664796027384967 4028215112497194041077451)
                ·
                  refine ⟨6042322668745791061616177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4028215112497194041077451 6042322668745791061616177)
                  ·
                    refine ⟨4531742001559343296212133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6042322668745791061616177 4531742001559343296212133)
                    ·
                      refine ⟨849701625292376868039775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4531742001559343296212133 849701625292376868039775)
                      ·
                        rfl

theorem cell23_1654788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_1654788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654788 prefixEnd_1654788 := by exact prefixLift 1654788
  have htrace : WordTrace (prefixWord ++ tailWord_1654788) baseStart_1654788 baseEnd_1654788 := by
    simpa [prefixWord, tailWord_1654788, baseEnd_1654788] using wordTrace_append hprefix tailTrace_1654788
  have hstable : (prefixWord ++ tailWord_1654788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654788).length < 2 ^ (prefixWord ++ tailWord_1654788).sum := by decide
  have hdescent : baseEnd_1654788 < baseStart_1654788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654800 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 5]
def baseStart_1654800 : Nat := 118140960795 + 1654800 * 2 ^ 59
def prefixEnd_1654800 : Nat := 4983230072969 + 3 ^ 40 * 1654800 * 2
def baseEnd_1654800 : Nat := 849707787060230821089719

theorem tailTrace_1654800 : CollatzResearch.WordTrace tailWord_1654800 prefixEnd_1654800 849707787060230821089719 := by
  unfold tailWord_1654800
  simp only [CollatzResearch.WordTrace]
  refine ⟨30177757202474846092396927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40237009603299794789862569 30177757202474846092396927)
  ·
    refine ⟨45266635803712269138595391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30177757202474846092396927 45266635803712269138595391)
    ·
      refine ⟨67899953705568403707893087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45266635803712269138595391 67899953705568403707893087)
      ·
        refine ⟨101849930558352605561839631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67899953705568403707893087 101849930558352605561839631)
        ·
          refine ⟨152774895837528908342759447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101849930558352605561839631 152774895837528908342759447)
          ·
            refine ⟨229162343756293362514139171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152774895837528908342759447 229162343756293362514139171)
            ·
              refine ⟨343743515634440043771208757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229162343756293362514139171 343743515634440043771208757)
              ·
                refine ⟨32225954590728754103550821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 343743515634440043771208757 32225954590728754103550821)
                ·
                  refine ⟨6042366485761641394415779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32225954590728754103550821 6042366485761641394415779)
                  ·
                    refine ⟨9063549728642462091623669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6042366485761641394415779 9063549728642462091623669)
                    ·
                      refine ⟨849707787060230821089719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9063549728642462091623669 849707787060230821089719)
                      ·
                        rfl

theorem cell23_1654800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 5].length) (baseStart_1654800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654800 prefixEnd_1654800 := by exact prefixLift 1654800
  have htrace : WordTrace (prefixWord ++ tailWord_1654800) baseStart_1654800 baseEnd_1654800 := by
    simpa [prefixWord, tailWord_1654800, baseEnd_1654800] using wordTrace_append hprefix tailTrace_1654800
  have hstable : (prefixWord ++ tailWord_1654800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654800).length < 2 ^ (prefixWord ++ tailWord_1654800).sum := by decide
  have hdescent : baseEnd_1654800 < baseStart_1654800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654837 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 7]
def baseStart_1654837 : Nat := 118140960795 + 1654837 * 2 ^ 59
def prefixEnd_1654837 : Nat := 4983230072969 + 3 ^ 40 * 1654837 * 2
def baseEnd_1654837 : Nat := 94414087316049686258561

theorem tailTrace_1654837 : CollatzResearch.WordTrace tailWord_1654837 prefixEnd_1654837 94414087316049686258561 := by
  unfold tailWord_1654837
  simp only [CollatzResearch.WordTrace]
  refine ⟨60356863905815647503890765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40237909270543765002593843 60356863905815647503890765)
  ·
    refine ⟨22633823964680867813959037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60356863905815647503890765 22633823964680867813959037)
    ·
      refine ⟨8487683986755325430234639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22633823964680867813959037 8487683986755325430234639)
      ·
        refine ⟨12731525980132988145351959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8487683986755325430234639 12731525980132988145351959)
        ·
          refine ⟨19097288970199482218027939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12731525980132988145351959 19097288970199482218027939)
          ·
            refine ⟨28645933455299223327041909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19097288970199482218027939 28645933455299223327041909)
            ·
              refine ⟨2685556261434302186910179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28645933455299223327041909 2685556261434302186910179)
              ·
                refine ⟨4028334392151453280365269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2685556261434302186910179 4028334392151453280365269)
                ·
                  refine ⟨94414087316049686258561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4028334392151453280365269 94414087316049686258561)
                  ·
                    rfl

theorem cell23_1654837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 7].length) (baseStart_1654837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654837 prefixEnd_1654837 := by exact prefixLift 1654837
  have htrace : WordTrace (prefixWord ++ tailWord_1654837) baseStart_1654837 baseEnd_1654837 := by
    simpa [prefixWord, tailWord_1654837, baseEnd_1654837] using wordTrace_append hprefix tailTrace_1654837
  have hstable : (prefixWord ++ tailWord_1654837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654837).length < 2 ^ (prefixWord ++ tailWord_1654837).sum := by decide
  have hdescent : baseEnd_1654837 < baseStart_1654837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654847 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 3]
def baseStart_1654847 : Nat := 118140960795 + 1654847 * 2 ^ 59
def prefixEnd_1654847 : Nat := 4983230072969 + 3 ^ 40 * 1654847 * 2
def baseEnd_1654847 : Nat := 849731920650992137202003

theorem tailTrace_1654847 : CollatzResearch.WordTrace tailWord_1654847 prefixEnd_1654847 849731920650992137202003 := by
  unfold tailWord_1654847
  simp only [CollatzResearch.WordTrace]
  refine ⟨60357228635779419211754795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40238152423852946141169863 60357228635779419211754795)
  ·
    refine ⟨90535842953669128817632193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60357228635779419211754795 90535842953669128817632193)
    ·
      refine ⟨67901882215251846613224145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90535842953669128817632193 67901882215251846613224145)
      ·
        refine ⟨50926411661438884959918109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67901882215251846613224145 50926411661438884959918109)
        ·
          refine ⟨19097404373039581859969291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50926411661438884959918109 19097404373039581859969291)
          ·
            refine ⟨28646106559559372789953937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19097404373039581859969291 28646106559559372789953937)
            ·
              refine ⟨21484579919669529592465453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28646106559559372789953937 21484579919669529592465453)
              ·
                refine ⟨8056717469876073597174545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21484579919669529592465453 8056717469876073597174545)
                ·
                  refine ⟨6042538102407055197880909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8056717469876073597174545 6042538102407055197880909)
                  ·
                    refine ⟨2265951788402645699205341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6042538102407055197880909 2265951788402645699205341)
                    ·
                      refine ⟨849731920650992137202003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2265951788402645699205341 849731920650992137202003)
                      ·
                        rfl

theorem cell23_1654847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 3, 3].length) (baseStart_1654847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654847 prefixEnd_1654847 := by exact prefixLift 1654847
  have htrace : WordTrace (prefixWord ++ tailWord_1654847) baseStart_1654847 baseEnd_1654847 := by
    simpa [prefixWord, tailWord_1654847, baseEnd_1654847] using wordTrace_append hprefix tailTrace_1654847
  have hstable : (prefixWord ++ tailWord_1654847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654847).length < 2 ^ (prefixWord ++ tailWord_1654847).sum := by decide
  have hdescent : baseEnd_1654847 < baseStart_1654847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654848 : List Nat := [2, 1, 1, 2, 2, 4, 4, 1, 2, 2, 2]
def baseStart_1654848 : Nat := 118140960795 + 1654848 * 2 ^ 59
def prefixEnd_1654848 : Nat := 4983230072969 + 3 ^ 40 * 1654848 * 2
def baseEnd_1654848 : Nat := 849732434131646633289499

theorem tailTrace_1654848 : CollatzResearch.WordTrace tailWord_1654848 prefixEnd_1654848 849732434131646633289499 := by
  unfold tailWord_1654848
  simp only [CollatzResearch.WordTrace]
  refine ⟨30178632554387898191270599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40238176739183864255027465 30178632554387898191270599)
  ·
    refine ⟨45267948831581847286905899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30178632554387898191270599 45267948831581847286905899)
    ·
      refine ⟨67901923247372770930358849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45267948831581847286905899 67901923247372770930358849)
      ·
        refine ⟨50926442435529578197769137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67901923247372770930358849 50926442435529578197769137)
        ·
          refine ⟨38194831826647183648326853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50926442435529578197769137 38194831826647183648326853)
          ·
            refine ⟨7161530967496346934061285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38194831826647183648326853 7161530967496346934061285)
            ·
              refine ⟨1342787056405565050136491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7161530967496346934061285 1342787056405565050136491)
              ·
                refine ⟨2014180584608347575204737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1342787056405565050136491 2014180584608347575204737)
                ·
                  refine ⟨1510635438456260681403553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2014180584608347575204737 1510635438456260681403553)
                  ·
                    refine ⟨1132976578842195511052665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1510635438456260681403553 1132976578842195511052665)
                    ·
                      refine ⟨849732434131646633289499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1132976578842195511052665 849732434131646633289499)
                      ·
                        rfl

theorem cell23_1654848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 1, 2, 2, 2].length) (baseStart_1654848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654848 prefixEnd_1654848 := by exact prefixLift 1654848
  have htrace : WordTrace (prefixWord ++ tailWord_1654848) baseStart_1654848 baseEnd_1654848 := by
    simpa [prefixWord, tailWord_1654848, baseEnd_1654848] using wordTrace_append hprefix tailTrace_1654848
  have hstable : (prefixWord ++ tailWord_1654848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654848).length < 2 ^ (prefixWord ++ tailWord_1654848).sum := by decide
  have hdescent : baseEnd_1654848 < baseStart_1654848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654854 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 9]
def baseStart_1654854 : Nat := 118140960795 + 1654854 * 2 ^ 59
def prefixEnd_1654854 : Nat := 4983230072969 + 3 ^ 40 * 1654854 * 2
def baseEnd_1654854 : Nat := 94415057223952623312719

theorem tailTrace_1654854 : CollatzResearch.WordTrace tailWord_1654854 prefixEnd_1654854 94415057223952623312719 := by
  unfold tailWord_1654854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1886171373336064356476863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40238322631169372938173077 1886171373336064356476863)
  ·
    refine ⟨2829257060004096534715295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1886171373336064356476863 2829257060004096534715295)
    ·
      refine ⟨4243885590006144802072943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2829257060004096534715295 4243885590006144802072943)
      ·
        refine ⟨6365828385009217203109415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4243885590006144802072943 6365828385009217203109415)
        ·
          refine ⟨9548742577513825804664123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6365828385009217203109415 9548742577513825804664123)
          ·
            refine ⟨14323113866270738706996185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9548742577513825804664123 14323113866270738706996185)
            ·
              refine ⟨10742335399703054030247139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14323113866270738706996185 10742335399703054030247139)
              ·
                refine ⟨16113503099554581045370709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10742335399703054030247139 16113503099554581045370709)
                ·
                  refine ⟨94415057223952623312719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16113503099554581045370709 94415057223952623312719)
                  ·
                    rfl

theorem cell23_1654854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_1654854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654854 prefixEnd_1654854 := by exact prefixLift 1654854
  have htrace : WordTrace (prefixWord ++ tailWord_1654854) baseStart_1654854 baseEnd_1654854 := by
    simpa [prefixWord, tailWord_1654854, baseEnd_1654854] using wordTrace_append hprefix tailTrace_1654854
  have hstable : (prefixWord ++ tailWord_1654854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654854).length < 2 ^ (prefixWord ++ tailWord_1654854).sum := by decide
  have hdescent : baseEnd_1654854 < baseStart_1654854 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654937 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 1, 7, 3]
def baseStart_1654937 : Nat := 118140960795 + 1654937 * 2 ^ 59
def prefixEnd_1654937 : Nat := 4983230072969 + 3 ^ 40 * 1654937 * 2
def baseEnd_1654937 : Nat := 849778133909896785076589

theorem tailTrace_1654937 : CollatzResearch.WordTrace tailWord_1654937 prefixEnd_1654937 849778133909896785076589 := by
  unfold tailWord_1654937
  simp only [CollatzResearch.WordTrace]
  refine ⟨60360511205453364582531065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40240340803635576388354043 60360511205453364582531065)
  ·
    refine ⟨45270383404090023436898299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60360511205453364582531065 45270383404090023436898299)
    ·
      refine ⟨67905575106135035155347449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45270383404090023436898299 67905575106135035155347449)
      ·
        refine ⟨50929181329601276366510587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67905575106135035155347449 50929181329601276366510587)
        ·
          refine ⟨76393771994401914549765881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50929181329601276366510587 76393771994401914549765881)
          ·
            refine ⟨57295328995801435912324411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76393771994401914549765881 57295328995801435912324411)
            ·
              refine ⟨85942993493702153868486617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57295328995801435912324411 85942993493702153868486617)
              ·
                refine ⟨64457245120276615401364963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85942993493702153868486617 64457245120276615401364963)
                ·
                  refine ⟨96685867680414923102047445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64457245120276615401364963 96685867680414923102047445)
                  ·
                    refine ⟨2266075023759724760204237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 96685867680414923102047445 2266075023759724760204237)
                    ·
                      refine ⟨849778133909896785076589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2266075023759724760204237 849778133909896785076589)
                      ·
                        rfl

theorem cell23_1654937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_1654937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654937 prefixEnd_1654937 := by exact prefixLift 1654937
  have htrace : WordTrace (prefixWord ++ tailWord_1654937) baseStart_1654937 baseEnd_1654937 := by
    simpa [prefixWord, tailWord_1654937, baseEnd_1654937] using wordTrace_append hprefix tailTrace_1654937
  have hstable : (prefixWord ++ tailWord_1654937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654937).length < 2 ^ (prefixWord ++ tailWord_1654937).sum := by decide
  have hdescent : baseEnd_1654937 < baseStart_1654937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654944 : List Nat := [2, 1, 1, 4, 2, 2, 3, 2, 6]
def baseStart_1654944 : Nat := 118140960795 + 1654944 * 2 ^ 59
def prefixEnd_1654944 : Nat := 4983230072969 + 3 ^ 40 * 1654944 * 2
def baseEnd_1654944 : Nat := 94420192030497584187673

theorem tailTrace_1654944 : CollatzResearch.WordTrace tailWord_1654944 prefixEnd_1654944 94420192030497584187673 := by
  unfold tailWord_1654944
  simp only [CollatzResearch.WordTrace]
  refine ⟨30180383258214002389017943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40240511010952003185357257 30180383258214002389017943)
  ·
    refine ⟨45270574887321003583526915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30180383258214002389017943 45270574887321003583526915)
    ·
      refine ⟨67905862330981505375290373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45270574887321003583526915 67905862330981505375290373)
      ·
        refine ⟨12732349187059032257866945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67905862330981505375290373 12732349187059032257866945)
        ·
          refine ⟨9549261890294274193400209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12732349187059032257866945 9549261890294274193400209)
          ·
            refine ⟨7161946417720705645050157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9549261890294274193400209 7161946417720705645050157)
            ·
              refine ⟨2685729906645264616893809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7161946417720705645050157 2685729906645264616893809)
              ·
                refine ⟨2014297429983948462670357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2685729906645264616893809 2014297429983948462670357)
                ·
                  refine ⟨94420192030497584187673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2014297429983948462670357 94420192030497584187673)
                  ·
                    rfl

theorem cell23_1654944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 6].length) (baseStart_1654944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654944 prefixEnd_1654944 := by exact prefixLift 1654944
  have htrace : WordTrace (prefixWord ++ tailWord_1654944) baseStart_1654944 baseEnd_1654944 := by
    simpa [prefixWord, tailWord_1654944, baseEnd_1654944] using wordTrace_append hprefix tailTrace_1654944
  have hstable : (prefixWord ++ tailWord_1654944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654944).length < 2 ^ (prefixWord ++ tailWord_1654944).sum := by decide
  have hdescent : baseEnd_1654944 < baseStart_1654944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1654987 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 3, 6]
def baseStart_1654987 : Nat := 118140960795 + 1654987 * 2 ^ 59
def prefixEnd_1654987 : Nat := 4983230072969 + 3 ^ 40 * 1654987 * 2
def baseEnd_1654987 : Nat := 283267935980873863150453

theorem tailTrace_1654987 : CollatzResearch.WordTrace tailWord_1654987 prefixEnd_1654987 283267935980873863150453 := by
  unfold tailWord_1654987
  simp only [CollatzResearch.WordTrace]
  refine ⟨60362334855272223121851215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40241556570181482081234143 60362334855272223121851215)
  ·
    refine ⟨90543502282908334682776823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60362334855272223121851215 90543502282908334682776823)
    ·
      refine ⟨135815253424362502024165235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90543502282908334682776823 135815253424362502024165235)
      ·
        refine ⟨203722880136543753036247853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135815253424362502024165235 203722880136543753036247853)
        ·
          refine ⟨76396080051203907388592945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203722880136543753036247853 76396080051203907388592945)
          ·
            refine ⟨57297060038402930541444709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76396080051203907388592945 57297060038402930541444709)
            ·
              refine ⟨10743198757200549476520883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57297060038402930541444709 10743198757200549476520883)
              ·
                refine ⟨16114798135800824214781325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10743198757200549476520883 16114798135800824214781325)
                ·
                  refine ⟨6043049300925309080542997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16114798135800824214781325 6043049300925309080542997)
                  ·
                    refine ⟨283267935980873863150453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6043049300925309080542997 283267935980873863150453)
                    ·
                      rfl

theorem cell23_1654987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 6].length) (baseStart_1654987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1654987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1654987 prefixEnd_1654987 := by exact prefixLift 1654987
  have htrace : WordTrace (prefixWord ++ tailWord_1654987) baseStart_1654987 baseEnd_1654987 := by
    simpa [prefixWord, tailWord_1654987, baseEnd_1654987] using wordTrace_append hprefix tailTrace_1654987
  have hstable : (prefixWord ++ tailWord_1654987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1654987).length < 2 ^ (prefixWord ++ tailWord_1654987).sum := by decide
  have hdescent : baseEnd_1654987 < baseStart_1654987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1654987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655005 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_1655005 : Nat := 118140960795 + 1655005 * 2 ^ 59
def prefixEnd_1655005 : Nat := 4983230072969 + 3 ^ 40 * 1655005 * 2
def baseEnd_1655005 : Nat := 849813050594402519026277

theorem tailTrace_1655005 : CollatzResearch.WordTrace tailWord_1655005 prefixEnd_1655005 849813050594402519026277 := by
  unfold tailWord_1655005
  simp only [CollatzResearch.WordTrace]
  refine ⟨60362991369207012196006469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40241994246138008130670979 60362991369207012196006469)
  ·
    refine ⟨11318060881726314786751213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60362991369207012196006469 11318060881726314786751213)
    ·
      refine ⟨4244272830647368045031705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11318060881726314786751213 4244272830647368045031705)
      ·
        refine ⟨3183204622985526033773779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4244272830647368045031705 3183204622985526033773779)
        ·
          refine ⟨4774806934478289050660669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3183204622985526033773779 4774806934478289050660669)
          ·
            refine ⟨1790552600429358393997751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4774806934478289050660669 1790552600429358393997751)
            ·
              refine ⟨2685828900644037590996627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1790552600429358393997751 2685828900644037590996627)
              ·
                refine ⟨4028743350966056386494941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2685828900644037590996627 4028743350966056386494941)
                ·
                  refine ⟨1510778756612271144935603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4028743350966056386494941 1510778756612271144935603)
                  ·
                    refine ⟨2266168134918406717403405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1510778756612271144935603 2266168134918406717403405)
                    ·
                      refine ⟨849813050594402519026277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2266168134918406717403405 849813050594402519026277)
                      ·
                        rfl

theorem cell23_1655005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_1655005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655005 prefixEnd_1655005 := by exact prefixLift 1655005
  have htrace : WordTrace (prefixWord ++ tailWord_1655005) baseStart_1655005 baseEnd_1655005 := by
    simpa [prefixWord, tailWord_1655005, baseEnd_1655005] using wordTrace_append hprefix tailTrace_1655005
  have hstable : (prefixWord ++ tailWord_1655005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655005).length < 2 ^ (prefixWord ++ tailWord_1655005).sum := by decide
  have hdescent : baseEnd_1655005 < baseStart_1655005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655061 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 4, 1, 3]
def baseStart_1655061 : Nat := 118140960795 + 1655061 * 2 ^ 59
def prefixEnd_1655061 : Nat := 4983230072969 + 3 ^ 40 * 1655061 * 2
def baseEnd_1655061 : Nat := 849841805511054299926019

theorem tailTrace_1655061 : CollatzResearch.WordTrace tailWord_1655061 prefixEnd_1655061 849841805511054299926019 := by
  unfold tailWord_1655061
  simp only [CollatzResearch.WordTrace]
  refine ⟨60365033857004133760045037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40243355904669422506696691 60365033857004133760045037)
  ·
    refine ⟨22636887696376550160016889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60365033857004133760045037 22636887696376550160016889)
    ·
      refine ⟨16977665772282412620012667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22636887696376550160016889 16977665772282412620012667)
      ·
        refine ⟨25466498658423618930019001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16977665772282412620012667 25466498658423618930019001)
        ·
          refine ⟨19099873993817714197514251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25466498658423618930019001 19099873993817714197514251)
          ·
            refine ⟨28649810990726571296271377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19099873993817714197514251 28649810990726571296271377)
            ·
              refine ⟨21487358243044928472203533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28649810990726571296271377 21487358243044928472203533)
              ·
                refine ⟨8057759341141848177076325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21487358243044928472203533 8057759341141848177076325)
                ·
                  refine ⟨1510829876464096533201811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8057759341141848177076325 1510829876464096533201811)
                  ·
                    refine ⟨2266244814696144799802717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1510829876464096533201811 2266244814696144799802717)
                    ·
                      refine ⟨849841805511054299926019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2266244814696144799802717 849841805511054299926019)
                      ·
                        rfl

theorem cell23_1655061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_1655061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655061 prefixEnd_1655061 := by exact prefixLift 1655061
  have htrace : WordTrace (prefixWord ++ tailWord_1655061) baseStart_1655061 baseEnd_1655061 := by
    simpa [prefixWord, tailWord_1655061, baseEnd_1655061] using wordTrace_append hprefix tailTrace_1655061
  have hstable : (prefixWord ++ tailWord_1655061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655061).length < 2 ^ (prefixWord ++ tailWord_1655061).sum := by decide
  have hdescent : baseEnd_1655061 < baseStart_1655061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655079 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_1655079 : Nat := 118140960795 + 1655079 * 2 ^ 59
def prefixEnd_1655079 : Nat := 4983230072969 + 3 ^ 40 * 1655079 * 2
def baseEnd_1655079 : Nat := 849851048162835229500937

theorem tailTrace_1655079 : CollatzResearch.WordTrace tailWord_1655079 prefixEnd_1655079 849851048162835229500937 := by
  unfold tailWord_1655079
  simp only [CollatzResearch.WordTrace]
  refine ⟨60365690370938922834200291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40243793580625948556133527 60365690370938922834200291)
  ·
    refine ⟨90548535556408384251300437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60365690370938922834200291 90548535556408384251300437)
    ·
      refine ⟨1061115651051660752944927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 90548535556408384251300437 1061115651051660752944927)
      ·
        refine ⟨1591673476577491129417391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1061115651051660752944927 1591673476577491129417391)
        ·
          refine ⟨2387510214866236694126087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1591673476577491129417391 2387510214866236694126087)
          ·
            refine ⟨3581265322299355041189131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387510214866236694126087 3581265322299355041189131)
            ·
              refine ⟨5371897983449032561783697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3581265322299355041189131 5371897983449032561783697)
              ·
                refine ⟨4028923487586774421337773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5371897983449032561783697 4028923487586774421337773)
                ·
                  refine ⟨1510846307845040408001665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4028923487586774421337773 1510846307845040408001665)
                  ·
                    refine ⟨1133134730883780306001249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1510846307845040408001665 1133134730883780306001249)
                    ·
                      refine ⟨849851048162835229500937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133134730883780306001249 849851048162835229500937)
                      ·
                        rfl

theorem cell23_1655079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_1655079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655079 prefixEnd_1655079 := by exact prefixLift 1655079
  have htrace : WordTrace (prefixWord ++ tailWord_1655079) baseStart_1655079 baseEnd_1655079 := by
    simpa [prefixWord, tailWord_1655079, baseEnd_1655079] using wordTrace_append hprefix tailTrace_1655079
  have hstable : (prefixWord ++ tailWord_1655079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655079).length < 2 ^ (prefixWord ++ tailWord_1655079).sum := by decide
  have hdescent : baseEnd_1655079 < baseStart_1655079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655104 : List Nat := [2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 3]
def baseStart_1655104 : Nat := 118140960795 + 1655104 * 2 ^ 59
def prefixEnd_1655104 : Nat := 4983230072969 + 3 ^ 40 * 1655104 * 2
def baseEnd_1655104 : Nat := 849863885179197631688321

theorem tailTrace_1655104 : CollatzResearch.WordTrace tailWord_1655104 prefixEnd_1655104 849863885179197631688321 := by
  unfold tailWord_1655104
  simp only [CollatzResearch.WordTrace]
  refine ⟨30183301097924176051930183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40244401463898901402573577 30183301097924176051930183)
  ·
    refine ⟨45274951646886264077895275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30183301097924176051930183 45274951646886264077895275)
    ·
      refine ⟨67912427470329396116842913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45274951646886264077895275 67912427470329396116842913)
      ·
        refine ⟨50934320602747047087632185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67912427470329396116842913 50934320602747047087632185)
        ·
          refine ⟨38200740452060285315724139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50934320602747047087632185 38200740452060285315724139)
          ·
            refine ⟨57301110678090427973586209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38200740452060285315724139 57301110678090427973586209)
            ·
              refine ⟨42975833008567820980189657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57301110678090427973586209 42975833008567820980189657)
              ·
                refine ⟨32231874756425865735142243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42975833008567820980189657 32231874756425865735142243)
                ·
                  refine ⟨48347812134638798602713365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32231874756425865735142243 48347812134638798602713365)
                  ·
                    refine ⟨2266303693811193684502189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48347812134638798602713365 2266303693811193684502189)
                    ·
                      refine ⟨849863885179197631688321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2266303693811193684502189 849863885179197631688321)
                      ·
                        rfl

theorem cell23_1655104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_1655104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655104 prefixEnd_1655104 := by exact prefixLift 1655104
  have htrace : WordTrace (prefixWord ++ tailWord_1655104) baseStart_1655104 baseEnd_1655104 := by
    simpa [prefixWord, tailWord_1655104, baseEnd_1655104] using wordTrace_append hprefix tailTrace_1655104
  have hstable : (prefixWord ++ tailWord_1655104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655104).length < 2 ^ (prefixWord ++ tailWord_1655104).sum := by decide
  have hdescent : baseEnd_1655104 < baseStart_1655104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655161 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 1, 7, 2]
def baseStart_1655161 : Nat := 118140960795 + 1655161 * 2 ^ 59
def prefixEnd_1655161 : Nat := 4983230072969 + 3 ^ 40 * 1655161 * 2
def baseEnd_1655161 : Nat := 849893153576503908675559

theorem tailTrace_1655161 : CollatzResearch.WordTrace tailWord_1655161 prefixEnd_1655161 849893153576503908675559 := by
  unfold tailWord_1655161
  simp only [CollatzResearch.WordTrace]
  refine ⟨60368681156641850838685337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40245787437761233892456891 60368681156641850838685337)
  ·
    refine ⟨45276510867481388129014003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60368681156641850838685337 45276510867481388129014003)
    ·
      refine ⟨67914766301222082193521005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45276510867481388129014003 67914766301222082193521005)
      ·
        refine ⟨25468037362958280822570377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67914766301222082193521005 25468037362958280822570377)
        ·
          refine ⟨19101028022218710616927783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25468037362958280822570377 19101028022218710616927783)
          ·
            refine ⟨28651542033328065925391675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19101028022218710616927783 28651542033328065925391675)
            ·
              refine ⟨42977313049992098888087513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28651542033328065925391675 42977313049992098888087513)
              ·
                refine ⟨32232984787494074166065635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42977313049992098888087513 32232984787494074166065635)
                ·
                  refine ⟨48349477181241111249098453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32232984787494074166065635 48349477181241111249098453)
                  ·
                    refine ⟨1133190871435338544900745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48349477181241111249098453 1133190871435338544900745)
                    ·
                      refine ⟨849893153576503908675559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133190871435338544900745 849893153576503908675559)
                      ·
                        rfl

theorem cell23_1655161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 7, 2].length) (baseStart_1655161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655161 prefixEnd_1655161 := by exact prefixLift 1655161
  have htrace : WordTrace (prefixWord ++ tailWord_1655161) baseStart_1655161 baseEnd_1655161 := by
    simpa [prefixWord, tailWord_1655161, baseEnd_1655161] using wordTrace_append hprefix tailTrace_1655161
  have hstable : (prefixWord ++ tailWord_1655161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655161).length < 2 ^ (prefixWord ++ tailWord_1655161).sum := by decide
  have hdescent : baseEnd_1655161 < baseStart_1655161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655282 : List Nat := [3, 2, 1, 4, 3, 1, 1, 2, 6]
def baseStart_1655282 : Nat := 118140960795 + 1655282 * 2 ^ 59
def prefixEnd_1655282 : Nat := 4983230072969 + 3 ^ 40 * 1655282 * 2
def baseEnd_1655282 : Nat := 94439476081744215029167

theorem tailTrace_1655282 : CollatzResearch.WordTrace tailWord_1655282 prefixEnd_1655282 94439476081744215029167 := by
  unfold tailWord_1655282
  simp only [CollatzResearch.WordTrace]
  refine ⟨15093273597300872125960025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40248729592802325669226733 15093273597300872125960025)
  ·
    refine ⟨11319955197975654094470019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15093273597300872125960025 11319955197975654094470019)
    ·
      refine ⟨16979932796963481141705029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11319955197975654094470019 16979932796963481141705029)
      ·
        refine ⟨3183737399430652714069693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16979932796963481141705029 3183737399430652714069693)
        ·
          refine ⟨1193901524786494767776135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3183737399430652714069693 1193901524786494767776135)
          ·
            refine ⟨1790852287179742151664203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193901524786494767776135 1790852287179742151664203)
            ·
              refine ⟨2686278430769613227496305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1790852287179742151664203 2686278430769613227496305)
              ·
                refine ⟨2014708823077209920622229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2686278430769613227496305 2014708823077209920622229)
                ·
                  refine ⟨94439476081744215029167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2014708823077209920622229 94439476081744215029167)
                  ·
                    rfl

theorem cell23_1655282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 6].length) (baseStart_1655282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655282 prefixEnd_1655282 := by exact prefixLift 1655282
  have htrace : WordTrace (prefixWord ++ tailWord_1655282) baseStart_1655282 baseEnd_1655282 := by
    simpa [prefixWord, tailWord_1655282, baseEnd_1655282] using wordTrace_append hprefix tailTrace_1655282
  have hstable : (prefixWord ++ tailWord_1655282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655282).length < 2 ^ (prefixWord ++ tailWord_1655282).sum := by decide
  have hdescent : baseEnd_1655282 < baseStart_1655282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655301 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 3, 1, 5]
def baseStart_1655301 : Nat := 118140960795 + 1655301 * 2 ^ 59
def prefixEnd_1655301 : Nat := 4983230072969 + 3 ^ 40 * 1655301 * 2
def baseEnd_1655301 : Nat := 849965040868133360924915

theorem tailTrace_1655301 : CollatzResearch.WordTrace tailWord_1655301 prefixEnd_1655301 849965040868133360924915 := by
  unfold tailWord_1655301
  simp only [CollatzResearch.WordTrace]
  refine ⟨60373787376134654748781757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40249191584089769832521171 60373787376134654748781757)
  ·
    refine ⟨22640170266050495530793159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60373787376134654748781757 22640170266050495530793159)
    ·
      refine ⟨33960255399075743296189739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22640170266050495530793159 33960255399075743296189739)
      ·
        refine ⟨50940383098613614944284609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33960255399075743296189739 50940383098613614944284609)
        ·
          refine ⟨38205287323960211208213457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50940383098613614944284609 38205287323960211208213457)
          ·
            refine ⟨28653965492970158406160093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38205287323960211208213457 28653965492970158406160093)
            ·
              refine ⟨10745237059863809402310035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28653965492970158406160093 10745237059863809402310035)
              ·
                refine ⟨16117855589795714103465053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10745237059863809402310035 16117855589795714103465053)
                ·
                  refine ⟨6044195846173392788799395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16117855589795714103465053 6044195846173392788799395)
                  ·
                    refine ⟨9066293769260089183199093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6044195846173392788799395 9066293769260089183199093)
                    ·
                      refine ⟨849965040868133360924915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9066293769260089183199093 849965040868133360924915)
                      ·
                        rfl

theorem cell23_1655301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 1, 5].length) (baseStart_1655301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655301 prefixEnd_1655301 := by exact prefixLift 1655301
  have htrace : WordTrace (prefixWord ++ tailWord_1655301) baseStart_1655301 baseEnd_1655301 := by
    simpa [prefixWord, tailWord_1655301, baseEnd_1655301] using wordTrace_append hprefix tailTrace_1655301
  have hstable : (prefixWord ++ tailWord_1655301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655301).length < 2 ^ (prefixWord ++ tailWord_1655301).sum := by decide
  have hdescent : baseEnd_1655301 < baseStart_1655301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655308 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 1, 6]
def baseStart_1655308 : Nat := 118140960795 + 1655308 * 2 ^ 59
def prefixEnd_1655308 : Nat := 4983230072969 + 3 ^ 40 * 1655308 * 2
def baseEnd_1655308 : Nat := 283322878410904944512461

theorem tailTrace_1655308 : CollatzResearch.WordTrace tailWord_1655308 prefixEnd_1655308 283322878410904944512461 := by
  unfold tailWord_1655308
  simp only [CollatzResearch.WordTrace]
  refine ⟨30187021343554647472143289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40249361791406196629524385 30187021343554647472143289)
  ·
    refine ⟨22640266007665985604107467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30187021343554647472143289 22640266007665985604107467)
    ·
      refine ⟨33960399011498978406161201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22640266007665985604107467 33960399011498978406161201)
      ·
        refine ⟨25470299258624233804620901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33960399011498978406161201 25470299258624233804620901)
        ·
          refine ⟨4775681110992043838366419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25470299258624233804620901 4775681110992043838366419)
          ·
            refine ⟨7163521666488065757549629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4775681110992043838366419 7163521666488065757549629)
            ·
              refine ⟨2686320624933024659081111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7163521666488065757549629 2686320624933024659081111)
              ·
                refine ⟨4029480937399536988621667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2686320624933024659081111 4029480937399536988621667)
                ·
                  refine ⟨6044221406099305482932501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4029480937399536988621667 6044221406099305482932501)
                  ·
                    refine ⟨283322878410904944512461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6044221406099305482932501 283322878410904944512461)
                    ·
                      rfl

theorem cell23_1655308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_1655308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655308 prefixEnd_1655308 := by exact prefixLift 1655308
  have htrace : WordTrace (prefixWord ++ tailWord_1655308) baseStart_1655308 baseEnd_1655308 := by
    simpa [prefixWord, tailWord_1655308, baseEnd_1655308] using wordTrace_append hprefix tailTrace_1655308
  have hstable : (prefixWord ++ tailWord_1655308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655308).length < 2 ^ (prefixWord ++ tailWord_1655308).sum := by decide
  have hdescent : baseEnd_1655308 < baseStart_1655308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655309 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_1655309 : Nat := 118140960795 + 1655309 * 2 ^ 59
def prefixEnd_1655309 : Nat := 4983230072969 + 3 ^ 40 * 1655309 * 2
def baseEnd_1655309 : Nat := 849969148713369329624879

theorem tailTrace_1655309 : CollatzResearch.WordTrace tailWord_1655309 prefixEnd_1655309 849969148713369329624879 := by
  unfold tailWord_1655309
  simp only [CollatzResearch.WordTrace]
  refine ⟨60374079160105672115072981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40249386106737114743381987 60374079160105672115072981)
  ·
    refine ⟨1415017480314976690197023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 60374079160105672115072981 1415017480314976690197023)
    ·
      refine ⟨2122526220472465035295535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1415017480314976690197023 2122526220472465035295535)
      ·
        refine ⟨3183789330708697552943303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2122526220472465035295535 3183789330708697552943303)
        ·
          refine ⟨4775683996063046329414955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3183789330708697552943303 4775683996063046329414955)
          ·
            refine ⟨7163525994094569494122433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4775683996063046329414955 7163525994094569494122433)
            ·
              refine ⟨5372644495570927120591825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7163525994094569494122433 5372644495570927120591825)
              ·
                refine ⟨4029483371678195340443869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5372644495570927120591825 4029483371678195340443869)
                ·
                  refine ⟨1511056264379323252666451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4029483371678195340443869 1511056264379323252666451)
                  ·
                    refine ⟨2266584396568984878999677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1511056264379323252666451 2266584396568984878999677)
                    ·
                      refine ⟨849969148713369329624879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2266584396568984878999677 849969148713369329624879)
                      ·
                        rfl

theorem cell23_1655309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_1655309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655309 prefixEnd_1655309 := by exact prefixLift 1655309
  have htrace : WordTrace (prefixWord ++ tailWord_1655309) baseStart_1655309 baseEnd_1655309 := by
    simpa [prefixWord, tailWord_1655309, baseEnd_1655309] using wordTrace_append hprefix tailTrace_1655309
  have hstable : (prefixWord ++ tailWord_1655309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655309).length < 2 ^ (prefixWord ++ tailWord_1655309).sum := by decide
  have hdescent : baseEnd_1655309 < baseStart_1655309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655315 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 3, 2, 2]
def baseStart_1655315 : Nat := 118140960795 + 1655315 * 2 ^ 59
def prefixEnd_1655315 : Nat := 4983230072969 + 3 ^ 40 * 1655315 * 2
def baseEnd_1655315 : Nat := 849972229597296306149851

theorem tailTrace_1655315 : CollatzResearch.WordTrace tailWord_1655315 prefixEnd_1655315 849972229597296306149851 := by
  unfold tailWord_1655315
  simp only [CollatzResearch.WordTrace]
  refine ⟨60374297998083935139791399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40249531998722623426527599 60374297998083935139791399)
  ·
    refine ⟨90561446997125902709687099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60374297998083935139791399 90561446997125902709687099)
    ·
      refine ⟨135842170495688854064530649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90561446997125902709687099 135842170495688854064530649)
      ·
        refine ⟨101881627871766640548397987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135842170495688854064530649 101881627871766640548397987)
        ·
          refine ⟨152822441807649960822596981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101881627871766640548397987 152822441807649960822596981)
          ·
            refine ⟨14327103919467183827118467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 152822441807649960822596981 14327103919467183827118467)
            ·
              refine ⟨21490655879200775740677701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14327103919467183827118467 21490655879200775740677701)
              ·
                refine ⟨4029497977350145451377069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21490655879200775740677701 4029497977350145451377069)
                ·
                  refine ⟨1511061741506304544266401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4029497977350145451377069 1511061741506304544266401)
                  ·
                    refine ⟨1133296306129728408199801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1511061741506304544266401 1133296306129728408199801)
                    ·
                      refine ⟨849972229597296306149851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133296306129728408199801 849972229597296306149851)
                      ·
                        rfl

theorem cell23_1655315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 2, 2].length) (baseStart_1655315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655315 prefixEnd_1655315 := by exact prefixLift 1655315
  have htrace : WordTrace (prefixWord ++ tailWord_1655315) baseStart_1655315 baseEnd_1655315 := by
    simpa [prefixWord, tailWord_1655315, baseEnd_1655315] using wordTrace_append hprefix tailTrace_1655315
  have hstable : (prefixWord ++ tailWord_1655315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655315).length < 2 ^ (prefixWord ++ tailWord_1655315).sum := by decide
  have hdescent : baseEnd_1655315 < baseStart_1655315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655338 : List Nat := [3, 1, 4, 1, 1, 4, 9]
def baseStart_1655338 : Nat := 118140960795 + 1655338 * 2 ^ 59
def prefixEnd_1655338 : Nat := 4983230072969 + 3 ^ 40 * 1655338 * 2
def baseEnd_1655338 : Nat := 10493630119164811310645

theorem tailTrace_1655338 : CollatzResearch.WordTrace tailWord_1655338 prefixEnd_1655338 10493630119164811310645 := by
  unfold tailWord_1655338
  simp only [CollatzResearch.WordTrace]
  refine ⟨15093784219250152516969667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40250091251333740045252445 15093784219250152516969667)
  ·
    refine ⟨22640676328875228775454501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15093784219250152516969667 22640676328875228775454501)
    ·
      refine ⟨4245126811664105395397719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22640676328875228775454501 4245126811664105395397719)
      ·
        refine ⟨6367690217496158093096579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4245126811664105395397719 6367690217496158093096579)
        ·
          refine ⟨9551535326244237139644869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6367690217496158093096579 9551535326244237139644869)
          ·
            refine ⟨1790912873670794463683413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9551535326244237139644869 1790912873670794463683413)
            ·
              refine ⟨10493630119164811310645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1790912873670794463683413 10493630119164811310645)
              ·
                rfl

theorem cell23_1655338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 9].length) (baseStart_1655338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655338 prefixEnd_1655338 := by exact prefixLift 1655338
  have htrace : WordTrace (prefixWord ++ tailWord_1655338) baseStart_1655338 baseEnd_1655338 := by
    simpa [prefixWord, tailWord_1655338, baseEnd_1655338] using wordTrace_append hprefix tailTrace_1655338
  have hstable : (prefixWord ++ tailWord_1655338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655338).length < 2 ^ (prefixWord ++ tailWord_1655338).sum := by decide
  have hdescent : baseEnd_1655338 < baseStart_1655338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655351 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 2, 7]
def baseStart_1655351 : Nat := 118140960795 + 1655351 * 2 ^ 59
def prefixEnd_1655351 : Nat := 4983230072969 + 3 ^ 40 * 1655351 * 2
def baseEnd_1655351 : Nat := 283330238300286055099895

theorem tailTrace_1655351 : CollatzResearch.WordTrace tailWord_1655351 prefixEnd_1655351 283330238300286055099895 := by
  unfold tailWord_1655351
  simp only [CollatzResearch.WordTrace]
  refine ⟨60375611025953513288101907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40250407350635675525401271 60375611025953513288101907)
  ·
    refine ⟨90563416538930269932152861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60375611025953513288101907 90563416538930269932152861)
    ·
      refine ⟨33961281202098851224557323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90563416538930269932152861 33961281202098851224557323)
      ·
        refine ⟨50941921803148276836835985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33961281202098851224557323 50941921803148276836835985)
        ·
          refine ⟨38206441352361207627626989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50941921803148276836835985 38206441352361207627626989)
          ·
            refine ⟨14327415507135452860360121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38206441352361207627626989 14327415507135452860360121)
            ·
              refine ⟨10745561630351589645270091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14327415507135452860360121 10745561630351589645270091)
              ·
                refine ⟨16118342445527384467905137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10745561630351589645270091 16118342445527384467905137)
                ·
                  refine ⟨12088756834145538350928853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16118342445527384467905137 12088756834145538350928853)
                  ·
                    refine ⟨283330238300286055099895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12088756834145538350928853 283330238300286055099895)
                    ·
                      rfl

theorem cell23_1655351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 7].length) (baseStart_1655351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655351 prefixEnd_1655351 := by exact prefixLift 1655351
  have htrace : WordTrace (prefixWord ++ tailWord_1655351) baseStart_1655351 baseEnd_1655351 := by
    simpa [prefixWord, tailWord_1655351, baseEnd_1655351] using wordTrace_append hprefix tailTrace_1655351
  have hstable : (prefixWord ++ tailWord_1655351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655351).length < 2 ^ (prefixWord ++ tailWord_1655351).sum := by decide
  have hdescent : baseEnd_1655351 < baseStart_1655351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655400 : List Nat := [2, 1, 4, 3, 3, 1, 2, 2, 1, 2, 2]
def baseStart_1655400 : Nat := 118140960795 + 1655400 * 2 ^ 59
def prefixEnd_1655400 : Nat := 4983230072969 + 3 ^ 40 * 1655400 * 2
def baseEnd_1655400 : Nat := 850015875452928473586961

theorem tailTrace_1655400 : CollatzResearch.WordTrace tailWord_1655400 prefixEnd_1655400 850015875452928473586961 := by
  unfold tailWord_1655400
  simp only [CollatzResearch.WordTrace]
  refine ⟨30188699101387997328317827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40251598801850663104423769 30188699101387997328317827)
  ·
    refine ⟨45283048652081995992476741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30188699101387997328317827 45283048652081995992476741)
    ·
      refine ⟨8490571622265374248589389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45283048652081995992476741 8490571622265374248589389)
      ·
        refine ⟨3183964358349515343221021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8490571622265374248589389 3183964358349515343221021)
        ·
          refine ⟨1193986634381068253707883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3183964358349515343221021 1193986634381068253707883)
          ·
            refine ⟨1790979951571602380561825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193986634381068253707883 1790979951571602380561825)
            ·
              refine ⟨1343234963678701785421369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1790979951571602380561825 1343234963678701785421369)
              ·
                refine ⟨1007426222759026339066027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1343234963678701785421369 1007426222759026339066027)
                ·
                  refine ⟨1511139334138539508599041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007426222759026339066027 1511139334138539508599041)
                  ·
                    refine ⟨1133354500603904631449281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1511139334138539508599041 1133354500603904631449281)
                    ·
                      refine ⟨850015875452928473586961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133354500603904631449281 850015875452928473586961)
                      ·
                        rfl

theorem cell23_1655400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_1655400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655400 prefixEnd_1655400 := by exact prefixLift 1655400
  have htrace : WordTrace (prefixWord ++ tailWord_1655400) baseStart_1655400 baseEnd_1655400 := by
    simpa [prefixWord, tailWord_1655400, baseEnd_1655400] using wordTrace_append hprefix tailTrace_1655400
  have hstable : (prefixWord ++ tailWord_1655400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655400).length < 2 ^ (prefixWord ++ tailWord_1655400).sum := by decide
  have hdescent : baseEnd_1655400 < baseStart_1655400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655401 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 2, 3, 6]
def baseStart_1655401 : Nat := 118140960795 + 1655401 * 2 ^ 59
def prefixEnd_1655401 : Nat := 4983230072969 + 3 ^ 40 * 1655401 * 2
def baseEnd_1655401 : Nat := 850016388933582969674455

theorem tailTrace_1655401 : CollatzResearch.WordTrace tailWord_1655401 prefixEnd_1655401 850016388933582969674455 := by
  unfold tailWord_1655401
  simp only [CollatzResearch.WordTrace]
  refine ⟨60377434675772371827422057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40251623117181581218281371 60377434675772371827422057)
  ·
    refine ⟨45283076006829278870566543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60377434675772371827422057 45283076006829278870566543)
    ·
      refine ⟨67924614010243918305849815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45283076006829278870566543 67924614010243918305849815)
      ·
        refine ⟨101886921015365877458774723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67924614010243918305849815 101886921015365877458774723)
        ·
          refine ⟨152830381523048816188162085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101886921015365877458774723 152830381523048816188162085)
          ·
            refine ⟨28655696535571653035280391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 152830381523048816188162085 28655696535571653035280391)
            ·
              refine ⟨42983544803357479552920587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28655696535571653035280391 42983544803357479552920587)
              ·
                refine ⟨64475317205036219329380881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42983544803357479552920587 64475317205036219329380881)
                ·
                  refine ⟨48356487903777164497035661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64475317205036219329380881 48356487903777164497035661)
                  ·
                    refine ⟨18133682963916436686388373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48356487903777164497035661 18133682963916436686388373)
                    ·
                      refine ⟨850016388933582969674455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18133682963916436686388373 850016388933582969674455)
                      ·
                        rfl

theorem cell23_1655401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_1655401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655401 prefixEnd_1655401 := by exact prefixLift 1655401
  have htrace : WordTrace (prefixWord ++ tailWord_1655401) baseStart_1655401 baseEnd_1655401 := by
    simpa [prefixWord, tailWord_1655401, baseEnd_1655401] using wordTrace_append hprefix tailTrace_1655401
  have hstable : (prefixWord ++ tailWord_1655401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655401).length < 2 ^ (prefixWord ++ tailWord_1655401).sum := by decide
  have hdescent : baseEnd_1655401 < baseStart_1655401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655428 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 9]
def baseStart_1655428 : Nat := 118140960795 + 1655428 * 2 ^ 59
def prefixEnd_1655428 : Nat := 4983230072969 + 3 ^ 40 * 1655428 * 2
def baseEnd_1655428 : Nat := 94447805879028262670759

theorem tailTrace_1655428 : CollatzResearch.WordTrace tailWord_1655428 prefixEnd_1655428 94447805879028262670759 := by
  unfold tailWord_1655428
  simp only [CollatzResearch.WordTrace]
  refine ⟨30189209723337277719327469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40252279631116370292436625 30189209723337277719327469)
  ·
    refine ⟨11320953646251479144747801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30189209723337277719327469 11320953646251479144747801)
    ·
      refine ⟨8490715234688609358560851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11320953646251479144747801 8490715234688609358560851)
      ·
        refine ⟨12736072852032914037841277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8490715234688609358560851 12736072852032914037841277)
        ·
          refine ⟨4776027319512342764190479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12736072852032914037841277 4776027319512342764190479)
          ·
            refine ⟨7164040979268514146285719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4776027319512342764190479 7164040979268514146285719)
            ·
              refine ⟨10746061468902771219428579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7164040979268514146285719 10746061468902771219428579)
              ·
                refine ⟨16119092203354156829142869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10746061468902771219428579 16119092203354156829142869)
                ·
                  refine ⟨94447805879028262670759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16119092203354156829142869 94447805879028262670759)
                  ·
                    rfl

theorem cell23_1655428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_1655428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655428 prefixEnd_1655428 := by exact prefixLift 1655428
  have htrace : WordTrace (prefixWord ++ tailWord_1655428) baseStart_1655428 baseEnd_1655428 := by
    simpa [prefixWord, tailWord_1655428, baseEnd_1655428] using wordTrace_append hprefix tailTrace_1655428
  have hstable : (prefixWord ++ tailWord_1655428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655428).length < 2 ^ (prefixWord ++ tailWord_1655428).sum := by decide
  have hdescent : baseEnd_1655428 < baseStart_1655428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655456 : List Nat := [2, 1, 1, 4, 4, 2, 1, 2, 2, 2, 2]
def baseStart_1655456 : Nat := 118140960795 + 1655456 * 2 ^ 59
def prefixEnd_1655456 : Nat := 4983230072969 + 3 ^ 40 * 1655456 * 2
def baseEnd_1655456 : Nat := 850044630369580254486703

theorem tailTrace_1655456 : CollatzResearch.WordTrace tailWord_1655456 prefixEnd_1655456 850044630369580254486703 := by
  unfold tailWord_1655456
  simp only [CollatzResearch.WordTrace]
  refine ⟨30189720345286558110337111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40252960460382077480449481 30189720345286558110337111)
  ·
    refine ⟨45284580517929837165505667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30189720345286558110337111 45284580517929837165505667)
    ·
      refine ⟨67926870776894755748258501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45284580517929837165505667 67926870776894755748258501)
      ·
        refine ⟨12736288270667766702798469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67926870776894755748258501 12736288270667766702798469)
        ·
          refine ⟨2388054050750206256774713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12736288270667766702798469 2388054050750206256774713)
          ·
            refine ⟨1791040538062654692581035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2388054050750206256774713 1791040538062654692581035)
            ·
              refine ⟨2686560807093982038871553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791040538062654692581035 2686560807093982038871553)
              ·
                refine ⟨2014920605320486529153665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2686560807093982038871553 2014920605320486529153665)
                ·
                  refine ⟨1511190453990364896865249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2014920605320486529153665 1511190453990364896865249)
                  ·
                    refine ⟨1133392840492773672648937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1511190453990364896865249 1133392840492773672648937)
                    ·
                      refine ⟨850044630369580254486703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133392840492773672648937 850044630369580254486703)
                      ·
                        rfl

theorem cell23_1655456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_1655456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655456 prefixEnd_1655456 := by exact prefixLift 1655456
  have htrace : WordTrace (prefixWord ++ tailWord_1655456) baseStart_1655456 baseEnd_1655456 := by
    simpa [prefixWord, tailWord_1655456, baseEnd_1655456] using wordTrace_append hprefix tailTrace_1655456
  have hstable : (prefixWord ++ tailWord_1655456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655456).length < 2 ^ (prefixWord ++ tailWord_1655456).sum := by decide
  have hdescent : baseEnd_1655456 < baseStart_1655456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655473 : List Nat := [1, 2, 2, 6, 1, 1, 3, 1, 2, 2, 2]
def baseStart_1655473 : Nat := 118140960795 + 1655473 * 2 ^ 59
def prefixEnd_1655473 : Nat := 4983230072969 + 3 ^ 40 * 1655473 * 2
def baseEnd_1655473 : Nat := 850053359540706687974125

theorem tailTrace_1655473 : CollatzResearch.WordTrace tailWord_1655473 prefixEnd_1655473 850053359540706687974125 := by
  unfold tailWord_1655473
  simp only [CollatzResearch.WordTrace]
  refine ⟨60380060731511528124043073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40253373821007685416028715 60380060731511528124043073)
  ·
    refine ⟨45285045548633646093032305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60380060731511528124043073 45285045548633646093032305)
    ·
      refine ⟨33963784161475234569774229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45285045548633646093032305 33963784161475234569774229)
      ·
        refine ⟨1592052382569151620458167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33963784161475234569774229 1592052382569151620458167)
        ·
          refine ⟨2388078573853727430687251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1592052382569151620458167 2388078573853727430687251)
          ·
            refine ⟨3582117860780591146030877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388078573853727430687251 3582117860780591146030877)
            ·
              refine ⟨1343294197792721679761579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3582117860780591146030877 1343294197792721679761579)
              ·
                refine ⟨2014941296689082519642369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1343294197792721679761579 2014941296689082519642369)
                ·
                  refine ⟨1511205972516811889731777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2014941296689082519642369 1511205972516811889731777)
                  ·
                    refine ⟨1133404479387608917298833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1511205972516811889731777 1133404479387608917298833)
                    ·
                      refine ⟨850053359540706687974125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133404479387608917298833 850053359540706687974125)
                      ·
                        rfl

theorem cell23_1655473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_1655473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655473 prefixEnd_1655473 := by exact prefixLift 1655473
  have htrace : WordTrace (prefixWord ++ tailWord_1655473) baseStart_1655473 baseEnd_1655473 := by
    simpa [prefixWord, tailWord_1655473, baseEnd_1655473] using wordTrace_append hprefix tailTrace_1655473
  have hstable : (prefixWord ++ tailWord_1655473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655473).length < 2 ^ (prefixWord ++ tailWord_1655473).sum := by decide
  have hdescent : baseEnd_1655473 < baseStart_1655473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655495 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 4, 4, 2]
def baseStart_1655495 : Nat := 118140960795 + 1655495 * 2 ^ 59
def prefixEnd_1655495 : Nat := 4983230072969 + 3 ^ 40 * 1655495 * 2
def baseEnd_1655495 : Nat := 850064656115105601899023

theorem tailTrace_1655495 : CollatzResearch.WordTrace tailWord_1655495 prefixEnd_1655495 850064656115105601899023 := by
  unfold tailWord_1655495
  simp only [CollatzResearch.WordTrace]
  refine ⟨60380863137431825881343939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40253908758287883920895959 60380863137431825881343939)
  ·
    refine ⟨90571294706147738822015909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60380863137431825881343939 90571294706147738822015909)
    ·
      refine ⟨16982117757402701029127983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90571294706147738822015909 16982117757402701029127983)
      ·
        refine ⟨25473176636104051543691975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16982117757402701029127983 25473176636104051543691975)
        ·
          refine ⟨38209764954156077315537963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25473176636104051543691975 38209764954156077315537963)
          ·
            refine ⟨57314647431234115973306945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38209764954156077315537963 57314647431234115973306945)
            ·
              refine ⟨42985985573425586979980209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57314647431234115973306945 42985985573425586979980209)
              ·
                refine ⟨32239489180069190234985157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42985985573425586979980209 32239489180069190234985157)
                ·
                  refine ⟨6044904221262973169059717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32239489180069190234985157 6044904221262973169059717)
                  ·
                    refine ⟨1133419541486807469198697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6044904221262973169059717 1133419541486807469198697)
                    ·
                      refine ⟨850064656115105601899023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133419541486807469198697 850064656115105601899023)
                      ·
                        rfl

theorem cell23_1655495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_1655495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655495 prefixEnd_1655495 := by exact prefixLift 1655495
  have htrace : WordTrace (prefixWord ++ tailWord_1655495) baseStart_1655495 baseEnd_1655495 := by
    simpa [prefixWord, tailWord_1655495, baseEnd_1655495] using wordTrace_append hprefix tailTrace_1655495
  have hstable : (prefixWord ++ tailWord_1655495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655495).length < 2 ^ (prefixWord ++ tailWord_1655495).sum := by decide
  have hdescent : baseEnd_1655495 < baseStart_1655495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655535 : List Nat := [1, 1, 2, 1, 5, 3, 1, 3, 6]
def baseStart_1655535 : Nat := 118140960795 + 1655535 * 2 ^ 59
def prefixEnd_1655535 : Nat := 4983230072969 + 3 ^ 40 * 1655535 * 2
def baseEnd_1655535 : Nat := 94453910593476160599871

theorem tailTrace_1655535 : CollatzResearch.WordTrace tailWord_1655535 prefixEnd_1655535 94453910593476160599871 := by
  unfold tailWord_1655535
  simp only [CollatzResearch.WordTrace]
  refine ⟨60382322057286912712800059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40254881371524608475200039 60382322057286912712800059)
  ·
    refine ⟨90573483085930369069200089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60382322057286912712800059 90573483085930369069200089)
    ·
      refine ⟨67930112314447776801900067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90573483085930369069200089 67930112314447776801900067)
      ·
        refine ⟨101895168471671665202850101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67930112314447776801900067 101895168471671665202850101)
        ·
          refine ⟨9552672044219218612767197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101895168471671665202850101 9552672044219218612767197)
          ·
            refine ⟨3582252016582206979787699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9552672044219218612767197 3582252016582206979787699)
            ·
              refine ⟨5373378024873310469681549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582252016582206979787699 5373378024873310469681549)
              ·
                refine ⟨2015016759327491426130581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5373378024873310469681549 2015016759327491426130581)
                ·
                  refine ⟨94453910593476160599871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2015016759327491426130581 94453910593476160599871)
                  ·
                    rfl

theorem cell23_1655535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 6].length) (baseStart_1655535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655535 prefixEnd_1655535 := by exact prefixLift 1655535
  have htrace : WordTrace (prefixWord ++ tailWord_1655535) baseStart_1655535 baseEnd_1655535 := by
    simpa [prefixWord, tailWord_1655535, baseEnd_1655535] using wordTrace_append hprefix tailTrace_1655535
  have hstable : (prefixWord ++ tailWord_1655535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655535).length < 2 ^ (prefixWord ++ tailWord_1655535).sum := by decide
  have hdescent : baseEnd_1655535 < baseStart_1655535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655585 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_1655585 : Nat := 118140960795 + 1655585 * 2 ^ 59
def prefixEnd_1655585 : Nat := 4983230072969 + 3 ^ 40 * 1655585 * 2
def baseEnd_1655585 : Nat := 850110869374010249773609

theorem tailTrace_1655585 : CollatzResearch.WordTrace tailWord_1655585 prefixEnd_1655585 850110869374010249773609 := by
  unfold tailWord_1655585
  simp only [CollatzResearch.WordTrace]
  refine ⟨60384145707105771252120209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40256097138070514168080139 60384145707105771252120209)
  ·
    refine ⟨45288109280329328439090157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60384145707105771252120209 45288109280329328439090157)
    ·
      refine ⟨16983040980123498164658809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45288109280329328439090157 16983040980123498164658809)
      ·
        refine ⟨12737280735092623623494107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16983040980123498164658809 12737280735092623623494107)
        ·
          refine ⟨19105921102638935435241161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12737280735092623623494107 19105921102638935435241161)
          ·
            refine ⟨14329440826979201576430871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19105921102638935435241161 14329440826979201576430871)
            ·
              refine ⟨21494161240468802364646307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14329440826979201576430871 21494161240468802364646307)
              ·
                refine ⟨32241241860703203546969461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21494161240468802364646307 32241241860703203546969461)
                ·
                  refine ⟨3022616424440925332528387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32241241860703203546969461 3022616424440925332528387)
                  ·
                    refine ⟨4533924636661387998792581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3022616424440925332528387 4533924636661387998792581)
                    ·
                      refine ⟨850110869374010249773609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4533924636661387998792581 850110869374010249773609)
                      ·
                        rfl

theorem cell23_1655585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_1655585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655585 prefixEnd_1655585 := by exact prefixLift 1655585
  have htrace : WordTrace (prefixWord ++ tailWord_1655585) baseStart_1655585 baseEnd_1655585 := by
    simpa [prefixWord, tailWord_1655585, baseEnd_1655585] using wordTrace_append hprefix tailTrace_1655585
  have hstable : (prefixWord ++ tailWord_1655585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655585).length < 2 ^ (prefixWord ++ tailWord_1655585).sum := by decide
  have hdescent : baseEnd_1655585 < baseStart_1655585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655602 : List Nat := [3, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4]
def baseStart_1655602 : Nat := 118140960795 + 1655602 * 2 ^ 59
def prefixEnd_1655602 : Nat := 4983230072969 + 3 ^ 40 * 1655602 * 2
def baseEnd_1655602 : Nat := 850119598545136683261031

theorem tailTrace_1655602 : CollatzResearch.WordTrace tailWord_1655602 prefixEnd_1655602 850119598545136683261031 := by
  unfold tailWord_1655602
  simp only [CollatzResearch.WordTrace]
  refine ⟨15096191437011045788872265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40256510498696122103659373 15096191437011045788872265)
  ·
    refine ⟨11322143577758284341654199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15096191437011045788872265 11322143577758284341654199)
    ·
      refine ⟨16983215366637426512481299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11322143577758284341654199 16983215366637426512481299)
      ·
        refine ⟨25474823049956139768721949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16983215366637426512481299 25474823049956139768721949)
        ·
          refine ⟨9553058643733552413270731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25474823049956139768721949 9553058643733552413270731)
          ·
            refine ⟨14329587965600328619906097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9553058643733552413270731 14329587965600328619906097)
            ·
              refine ⟨10747190974200246464929573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14329587965600328619906097 10747190974200246464929573)
              ·
                refine ⟨2015098307662546212174295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10747190974200246464929573 2015098307662546212174295)
                ·
                  refine ⟨3022647461493819318261443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2015098307662546212174295 3022647461493819318261443)
                  ·
                    refine ⟨4533971192240728977392165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3022647461493819318261443 4533971192240728977392165)
                    ·
                      refine ⟨850119598545136683261031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4533971192240728977392165 850119598545136683261031)
                      ·
                        rfl

theorem cell23_1655602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_1655602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655602 prefixEnd_1655602 := by exact prefixLift 1655602
  have htrace : WordTrace (prefixWord ++ tailWord_1655602) baseStart_1655602 baseEnd_1655602 := by
    simpa [prefixWord, tailWord_1655602, baseEnd_1655602] using wordTrace_append hprefix tailTrace_1655602
  have hstable : (prefixWord ++ tailWord_1655602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655602).length < 2 ^ (prefixWord ++ tailWord_1655602).sum := by decide
  have hdescent : baseEnd_1655602 < baseStart_1655602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655606 : List Nat := [5, 1, 2, 2, 2, 1, 1, 1, 1, 5, 2]
def baseStart_1655606 : Nat := 118140960795 + 1655606 * 2 ^ 59
def prefixEnd_1655606 : Nat := 4983230072969 + 3 ^ 40 * 1655606 * 2
def baseEnd_1655606 : Nat := 850121652467754667611013

theorem tailTrace_1655606 : CollatzResearch.WordTrace tailWord_1655606 prefixEnd_1655606 850121652467754667611013 := by
  unfold tailWord_1655606
  simp only [CollatzResearch.WordTrace]
  refine ⟨3774056977501855739914667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40256607760019794559089781 3774056977501855739914667)
  ·
    refine ⟨5661085466252783609872001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3774056977501855739914667 5661085466252783609872001)
    ·
      refine ⟨4245814099689587707404001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5661085466252783609872001 4245814099689587707404001)
      ·
        refine ⟨3184360574767190780553001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4245814099689587707404001 3184360574767190780553001)
        ·
          refine ⟨2388270431075393085414751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3184360574767190780553001 2388270431075393085414751)
          ·
            refine ⟨3582405646613089628122127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388270431075393085414751 3582405646613089628122127)
            ·
              refine ⟨5373608469919634442183191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582405646613089628122127 5373608469919634442183191)
              ·
                refine ⟨8060412704879451663274787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5373608469919634442183191 8060412704879451663274787)
                ·
                  refine ⟨12090619057319177494912181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8060412704879451663274787 12090619057319177494912181)
                  ·
                    refine ⟨1133495536623672890148017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12090619057319177494912181 1133495536623672890148017)
                    ·
                      refine ⟨850121652467754667611013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1133495536623672890148017 850121652467754667611013)
                      ·
                        rfl

theorem cell23_1655606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_1655606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655606 prefixEnd_1655606 := by exact prefixLift 1655606
  have htrace : WordTrace (prefixWord ++ tailWord_1655606) baseStart_1655606 baseEnd_1655606 := by
    simpa [prefixWord, tailWord_1655606, baseEnd_1655606] using wordTrace_append hprefix tailTrace_1655606
  have hstable : (prefixWord ++ tailWord_1655606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655606).length < 2 ^ (prefixWord ++ tailWord_1655606).sum := by decide
  have hdescent : baseEnd_1655606 < baseStart_1655606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655613 : List Nat := [1, 4, 1, 4, 2, 1, 2, 3, 1, 1, 3]
def baseStart_1655613 : Nat := 118140960795 + 1655613 * 2 ^ 59
def prefixEnd_1655613 : Nat := 4983230072969 + 3 ^ 40 * 1655613 * 2
def baseEnd_1655613 : Nat := 850125246832336140223481

theorem tailTrace_1655613 : CollatzResearch.WordTrace tailWord_1655613 prefixEnd_1655613 850125246832336140223481 := by
  unfold tailWord_1655613
  simp only [CollatzResearch.WordTrace]
  refine ⟨60385166951004332034139493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40256777967336221356092995 60385166951004332034139493)
  ·
    refine ⟨11322218803313312256401155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60385166951004332034139493 11322218803313312256401155)
    ·
      refine ⟨16983328204969968384601733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11322218803313312256401155 16983328204969968384601733)
      ·
        refine ⟨3184374038431869072112825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16983328204969968384601733 3184374038431869072112825)
        ·
          refine ⟨2388280528823901804084619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3184374038431869072112825 2388280528823901804084619)
          ·
            refine ⟨3582420793235852706126929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388280528823901804084619 3582420793235852706126929)
            ·
              refine ⟨2686815594926889529595197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3582420793235852706126929 2686815594926889529595197)
              ·
                refine ⟨1007555848097583573598199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2686815594926889529595197 1007555848097583573598199)
                ·
                  refine ⟨1511333772146375360397299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007555848097583573598199 1511333772146375360397299)
                  ·
                    refine ⟨2267000658219563040595949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1511333772146375360397299 2267000658219563040595949)
                    ·
                      refine ⟨850125246832336140223481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2267000658219563040595949 850125246832336140223481)
                      ·
                        rfl

theorem cell23_1655613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_1655613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655613 prefixEnd_1655613 := by exact prefixLift 1655613
  have htrace : WordTrace (prefixWord ++ tailWord_1655613) baseStart_1655613 baseEnd_1655613 := by
    simpa [prefixWord, tailWord_1655613, baseEnd_1655613] using wordTrace_append hprefix tailTrace_1655613
  have hstable : (prefixWord ++ tailWord_1655613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655613).length < 2 ^ (prefixWord ++ tailWord_1655613).sum := by decide
  have hdescent : baseEnd_1655613 < baseStart_1655613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1655635 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 3]
def baseStart_1655635 : Nat := 118140960795 + 1655635 * 2 ^ 59
def prefixEnd_1655635 : Nat := 4983230072969 + 3 ^ 40 * 1655635 * 2
def baseEnd_1655635 : Nat := 850136543406735054148379

theorem tailTrace_1655635 : CollatzResearch.WordTrace tailWord_1655635 prefixEnd_1655635 850136543406735054148379 := by
  unfold tailWord_1655635
  simp only [CollatzResearch.WordTrace]
  refine ⟨60385969356924629791440359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40257312904616419860960239 60385969356924629791440359)
  ·
    refine ⟨90578954035386944687160539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60385969356924629791440359 90578954035386944687160539)
    ·
      refine ⟨135868431053080417030740809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90578954035386944687160539 135868431053080417030740809)
      ·
        refine ⟨101901323289810312773055607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135868431053080417030740809 101901323289810312773055607)
        ·
          refine ⟨152851984934715469159583411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101901323289810312773055607 152851984934715469159583411)
          ·
            refine ⟨229277977402073203739375117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152851984934715469159583411 229277977402073203739375117)
            ·
              refine ⟨85979241525777451402265669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 229277977402073203739375117 85979241525777451402265669)
              ·
                refine ⟨16121107786083272137924813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85979241525777451402265669 16121107786083272137924813)
                ·
                  refine ⟨6045415419781227051721805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16121107786083272137924813 6045415419781227051721805)
                  ·
                    refine ⟨2267030782417960144395677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6045415419781227051721805 2267030782417960144395677)
                    ·
                      refine ⟨850136543406735054148379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2267030782417960144395677 850136543406735054148379)
                      ·
                        rfl

theorem cell23_1655635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 3, 3].length) (baseStart_1655635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1655635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1655635 prefixEnd_1655635 := by exact prefixLift 1655635
  have htrace : WordTrace (prefixWord ++ tailWord_1655635) baseStart_1655635 baseEnd_1655635 := by
    simpa [prefixWord, tailWord_1655635, baseEnd_1655635] using wordTrace_append hprefix tailTrace_1655635
  have hstable : (prefixWord ++ tailWord_1655635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1655635).length < 2 ^ (prefixWord ++ tailWord_1655635).sum := by decide
  have hdescent : baseEnd_1655635 < baseStart_1655635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1655635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
