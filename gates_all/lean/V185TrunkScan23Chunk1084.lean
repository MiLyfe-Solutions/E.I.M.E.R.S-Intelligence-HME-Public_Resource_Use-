import V185TrunkScan23Chunk1083

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6418101 : List Nat := [1, 3, 3, 3, 2, 1, 1, 3, 1, 1, 4]
def baseStart_6418101 : Nat := 118140960795 + 6418101 * 2 ^ 59
def prefixEnd_6418101 : Nat := 4983230072969 + 3 ^ 40 * 6418101 * 2
def baseEnd_6418101 : Nat := 3295570702102098884021197

theorem tailTrace_6418101 : CollatzResearch.WordTrace tailWord_6418101 prefixEnd_6418101 3295570702102098884021197 := by
  unfold tailWord_6418101
  simp only [CollatzResearch.WordTrace]
  refine ⟨234087374521323676228990157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156058249680882450819326771 234087374521323676228990157)
  ·
    refine ⟨87782765445496378585871309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234087374521323676228990157 87782765445496378585871309)
    ·
      refine ⟨32918537042061141969701741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87782765445496378585871309 32918537042061141969701741)
      ·
        refine ⟨12344451390772928238638153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32918537042061141969701741 12344451390772928238638153)
        ·
          refine ⟨9258338543079696178978615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12344451390772928238638153 9258338543079696178978615)
          ·
            refine ⟨13887507814619544268467923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9258338543079696178978615 13887507814619544268467923)
            ·
              refine ⟨20831261721929316402701885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13887507814619544268467923 20831261721929316402701885)
              ·
                refine ⟨7811723145723493651013207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20831261721929316402701885 7811723145723493651013207)
                ·
                  refine ⟨11717584718585240476519811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7811723145723493651013207 11717584718585240476519811)
                  ·
                    refine ⟨17576377077877860714779717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11717584718585240476519811 17576377077877860714779717)
                    ·
                      refine ⟨3295570702102098884021197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17576377077877860714779717 3295570702102098884021197)
                      ·
                        rfl

theorem cell23_6418101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_6418101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418101 prefixEnd_6418101 := by exact prefixLift 6418101
  have htrace : WordTrace (prefixWord ++ tailWord_6418101) baseStart_6418101 baseEnd_6418101 := by
    simpa [prefixWord, tailWord_6418101, baseEnd_6418101] using wordTrace_append hprefix tailTrace_6418101
  have hstable : (prefixWord ++ tailWord_6418101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418101).length < 2 ^ (prefixWord ++ tailWord_6418101).sum := by decide
  have hdescent : baseEnd_6418101 < baseStart_6418101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418144 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 3, 3, 2]
def baseStart_6418144 : Nat := 118140960795 + 6418144 * 2 ^ 59
def prefixEnd_6418144 : Nat := 4983230072969 + 3 ^ 40 * 6418144 * 2
def baseEnd_6418144 : Nat := 3295592781770242215783499

theorem tailTrace_6418144 : CollatzResearch.WordTrace tailWord_6418144 prefixEnd_6418144 3295592781770242215783499 := by
  unfold tailWord_6418144
  simp only [CollatzResearch.WordTrace]
  refine ⟨117044471430083947286402743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156059295240111929715203657 117044471430083947286402743)
  ·
    refine ⟨175566707145125920929604115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117044471430083947286402743 175566707145125920929604115)
    ·
      refine ⟨263350060717688881394406173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175566707145125920929604115 263350060717688881394406173)
      ·
        refine ⟨98756272769133330522902315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263350060717688881394406173 98756272769133330522902315)
        ·
          refine ⟨148134409153699995784353473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98756272769133330522902315 148134409153699995784353473)
          ·
            refine ⟨111100806865274996838265105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148134409153699995784353473 111100806865274996838265105)
            ·
              refine ⟨83325605148956247628698829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111100806865274996838265105 83325605148956247628698829)
              ·
                refine ⟨31247101930858592860762061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83325605148956247628698829 31247101930858592860762061)
                ·
                  refine ⟨11717663224071972322785773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31247101930858592860762061 11717663224071972322785773)
                  ·
                    refine ⟨4394123709026989621044665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11717663224071972322785773 4394123709026989621044665)
                    ·
                      refine ⟨3295592781770242215783499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4394123709026989621044665 3295592781770242215783499)
                      ·
                        rfl

theorem cell23_6418144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 3, 3, 2].length) (baseStart_6418144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418144 prefixEnd_6418144 := by exact prefixLift 6418144
  have htrace : WordTrace (prefixWord ++ tailWord_6418144) baseStart_6418144 baseEnd_6418144 := by
    simpa [prefixWord, tailWord_6418144, baseEnd_6418144] using wordTrace_append hprefix tailTrace_6418144
  have hstable : (prefixWord ++ tailWord_6418144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418144).length < 2 ^ (prefixWord ++ tailWord_6418144).sum := by decide
  have hdescent : baseEnd_6418144 < baseStart_6418144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418161 : List Nat := [1, 2, 2, 2, 2, 3, 2, 3, 1, 3, 2]
def baseStart_6418161 : Nat := 118140960795 + 6418161 * 2 ^ 59
def prefixEnd_6418161 : Nat := 4983230072969 + 3 ^ 40 * 6418161 * 2
def baseEnd_6418161 : Nat := 3295601510941368649270921

theorem tailTrace_6418161 : CollatzResearch.WordTrace tailWord_6418161 prefixEnd_6418161 3295601510941368649270921 := by
  unfold tailWord_6418161
  simp only [CollatzResearch.WordTrace]
  refine ⟨234089562901106306476174337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156059708600737537650782891 234089562901106306476174337)
  ·
    refine ⟨175567172175829729857130753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234089562901106306476174337 175567172175829729857130753)
    ·
      refine ⟨131675379131872297392848065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175567172175829729857130753 131675379131872297392848065)
      ·
        refine ⟨98756534348904223044636049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131675379131872297392848065 98756534348904223044636049)
        ·
          refine ⟨74067400761678167283477037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98756534348904223044636049 74067400761678167283477037)
          ·
            refine ⟨27775275285629312731303889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74067400761678167283477037 27775275285629312731303889)
            ·
              refine ⟨20831456464221984548477917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27775275285629312731303889 20831456464221984548477917)
              ·
                refine ⟨7811796174083244205679219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20831456464221984548477917 7811796174083244205679219)
                ·
                  refine ⟨11717694261124866308518829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7811796174083244205679219 11717694261124866308518829)
                  ·
                    refine ⟨4394135347921824865694561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11717694261124866308518829 4394135347921824865694561)
                    ·
                      refine ⟨3295601510941368649270921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4394135347921824865694561 3295601510941368649270921)
                      ·
                        rfl

theorem cell23_6418161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 3, 2].length) (baseStart_6418161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418161 prefixEnd_6418161 := by exact prefixLift 6418161
  have htrace : WordTrace (prefixWord ++ tailWord_6418161) baseStart_6418161 baseEnd_6418161 := by
    simpa [prefixWord, tailWord_6418161, baseEnd_6418161] using wordTrace_append hprefix tailTrace_6418161
  have hstable : (prefixWord ++ tailWord_6418161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418161).length < 2 ^ (prefixWord ++ tailWord_6418161).sum := by decide
  have hdescent : baseEnd_6418161 < baseStart_6418161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418187 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 4]
def baseStart_6418187 : Nat := 118140960795 + 6418187 * 2 ^ 59
def prefixEnd_6418187 : Nat := 4983230072969 + 3 ^ 40 * 6418187 * 2
def baseEnd_6418187 : Nat := 3295614861438385547545801

theorem tailTrace_6418187 : CollatzResearch.WordTrace tailWord_6418187 prefixEnd_6418187 3295614861438385547545801 := by
  unfold tailWord_6418187
  simp only [CollatzResearch.WordTrace]
  refine ⟨234090511199012112916620815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156060340799341408611080543 234090511199012112916620815)
  ·
    refine ⟨351135766798518169374931223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234090511199012112916620815 351135766798518169374931223)
    ·
      refine ⟨526703650197777254062396835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351135766798518169374931223 526703650197777254062396835)
      ·
        refine ⟨790055475296665881093595253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526703650197777254062396835 790055475296665881093595253)
        ·
          refine ⟨74067700809062426352524555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 790055475296665881093595253 74067700809062426352524555)
          ·
            refine ⟨111101551213593639528786833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74067700809062426352524555 111101551213593639528786833)
            ·
              refine ⟨83326163410195229646590125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111101551213593639528786833 83326163410195229646590125)
              ·
                refine ⟨31247311278823211117471297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83326163410195229646590125 31247311278823211117471297)
                ·
                  refine ⟨23435483459117408338103473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31247311278823211117471297 23435483459117408338103473)
                  ·
                    refine ⟨17576612594338056253577605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23435483459117408338103473 17576612594338056253577605)
                    ·
                      refine ⟨3295614861438385547545801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17576612594338056253577605 3295614861438385547545801)
                      ·
                        rfl

theorem cell23_6418187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 4].length) (baseStart_6418187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418187 prefixEnd_6418187 := by exact prefixLift 6418187
  have htrace : WordTrace (prefixWord ++ tailWord_6418187) baseStart_6418187 baseEnd_6418187 := by
    simpa [prefixWord, tailWord_6418187, baseEnd_6418187] using wordTrace_append hprefix tailTrace_6418187
  have hstable : (prefixWord ++ tailWord_6418187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418187).length < 2 ^ (prefixWord ++ tailWord_6418187).sum := by decide
  have hdescent : baseEnd_6418187 < baseStart_6418187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418189 : List Nat := [1, 7, 2, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_6418189 : Nat := 118140960795 + 6418189 * 2 ^ 59
def prefixEnd_6418189 : Nat := 4983230072969 + 3 ^ 40 * 6418189 * 2
def baseEnd_6418189 : Nat := 3295615888399694539720793

theorem tailTrace_6418189 : CollatzResearch.WordTrace tailWord_6418189 prefixEnd_6418189 3295615888399694539720793 := by
  unfold tailWord_6418189
  simp only [CollatzResearch.WordTrace]
  refine ⟨234090584145004867258193621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156060389430003244838795747 234090584145004867258193621)
  ·
    refine ⟨5486498065898551576363913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 234090584145004867258193621 5486498065898551576363913)
    ·
      refine ⟨4114873549423913682272935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5486498065898551576363913 4114873549423913682272935)
      ·
        refine ⟨6172310324135870523409403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4114873549423913682272935 6172310324135870523409403)
        ·
          refine ⟨9258465486203805785114105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6172310324135870523409403 9258465486203805785114105)
          ·
            refine ⟨6943849114652854338835579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9258465486203805785114105 6943849114652854338835579)
            ·
              refine ⟨10415773671979281508253369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6943849114652854338835579 10415773671979281508253369)
              ·
                refine ⟨7811830253984461131190027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10415773671979281508253369 7811830253984461131190027)
                ·
                  refine ⟨11717745380976691696785041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7811830253984461131190027 11717745380976691696785041)
                  ·
                    refine ⟨8788309035732518772588781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11717745380976691696785041 8788309035732518772588781)
                    ·
                      refine ⟨3295615888399694539720793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8788309035732518772588781 3295615888399694539720793)
                      ·
                        rfl

theorem cell23_6418189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_6418189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418189 prefixEnd_6418189 := by exact prefixLift 6418189
  have htrace : WordTrace (prefixWord ++ tailWord_6418189) baseStart_6418189 baseEnd_6418189 := by
    simpa [prefixWord, tailWord_6418189, baseEnd_6418189] using wordTrace_append hprefix tailTrace_6418189
  have hstable : (prefixWord ++ tailWord_6418189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418189).length < 2 ^ (prefixWord ++ tailWord_6418189).sum := by decide
  have hdescent : baseEnd_6418189 < baseStart_6418189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418261 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 2, 5]
def baseStart_6418261 : Nat := 118140960795 + 6418261 * 2 ^ 59
def prefixEnd_6418261 : Nat := 4983230072969 + 3 ^ 40 * 6418261 * 2
def baseEnd_6418261 : Nat := 1098550953002272752673487

theorem tailTrace_6418261 : CollatzResearch.WordTrace tailWord_6418261 prefixEnd_6418261 1098550953002272752673487 := by
  unfold tailWord_6418261
  simp only [CollatzResearch.WordTrace]
  refine ⟨234093210200744023554814637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156062140133829349036543091 234093210200744023554814637)
  ·
    refine ⟨87784953825279008833055489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234093210200744023554814637 87784953825279008833055489)
    ·
      refine ⟨65838715368959256624791617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87784953825279008833055489 65838715368959256624791617)
      ·
        refine ⟨49379036526719442468593713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65838715368959256624791617 49379036526719442468593713)
        ·
          refine ⟨37034277395039581851445285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49379036526719442468593713 37034277395039581851445285)
          ·
            refine ⟨6943927011569921597145991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37034277395039581851445285 6943927011569921597145991)
            ·
              refine ⟨10415890517354882395718987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6943927011569921597145991 10415890517354882395718987)
              ·
                refine ⟨15623835776032323593578481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10415890517354882395718987 15623835776032323593578481)
                ·
                  refine ⟨11717876832024242695183861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15623835776032323593578481 11717876832024242695183861)
                  ·
                    refine ⟨1098550953002272752673487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11717876832024242695183861 1098550953002272752673487)
                    ·
                      rfl

theorem cell23_6418261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 5].length) (baseStart_6418261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418261 prefixEnd_6418261 := by exact prefixLift 6418261
  have htrace : WordTrace (prefixWord ++ tailWord_6418261) baseStart_6418261 baseEnd_6418261 := by
    simpa [prefixWord, tailWord_6418261, baseEnd_6418261] using wordTrace_append hprefix tailTrace_6418261
  have hstable : (prefixWord ++ tailWord_6418261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418261).length < 2 ^ (prefixWord ++ tailWord_6418261).sum := by decide
  have hdescent : baseEnd_6418261 < baseStart_6418261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418347 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 2, 10]
def baseStart_6418347 : Nat := 118140960795 + 6418347 * 2 ^ 59
def prefixEnd_6418347 : Nat := 4983230072969 + 3 ^ 40 * 6418347 * 2
def baseEnd_6418347 : Nat := 1098565672781034973848355

theorem tailTrace_6418347 : CollatzResearch.WordTrace tailWord_6418347 prefixEnd_6418347 1098565672781034973848355 := by
  unfold tailWord_6418347
  simp only [CollatzResearch.WordTrace]
  refine ⟨234096346878432460242445295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156064231252288306828296863 234096346878432460242445295)
  ·
    refine ⟨351144520317648690363667943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234096346878432460242445295 351144520317648690363667943)
    ·
      refine ⟨526716780476473035545501915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351144520317648690363667943 526716780476473035545501915)
      ·
        refine ⟨790075170714709553318252873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526716780476473035545501915 790075170714709553318252873)
        ·
          refine ⟨592556378036032164988689655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 790075170714709553318252873 592556378036032164988689655)
          ·
            refine ⟨888834567054048247483034483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592556378036032164988689655 888834567054048247483034483)
            ·
              refine ⟨1333251850581072371224551725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888834567054048247483034483 1333251850581072371224551725)
              ·
                refine ⟨499969443967902139209206897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1333251850581072371224551725 499969443967902139209206897)
                ·
                  refine ⟨374977082975926604406905173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 499969443967902139209206897 374977082975926604406905173)
                  ·
                    refine ⟨1098565672781034973848355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 374977082975926604406905173 1098565672781034973848355)
                    ·
                      rfl

theorem cell23_6418347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 10].length) (baseStart_6418347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418347 prefixEnd_6418347 := by exact prefixLift 6418347
  have htrace : WordTrace (prefixWord ++ tailWord_6418347) baseStart_6418347 baseEnd_6418347 := by
    simpa [prefixWord, tailWord_6418347, baseEnd_6418347] using wordTrace_append hprefix tailTrace_6418347
  have hstable : (prefixWord ++ tailWord_6418347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418347).length < 2 ^ (prefixWord ++ tailWord_6418347).sum := by decide
  have hdescent : baseEnd_6418347 < baseStart_6418347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418384 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 4]
def baseStart_6418384 : Nat := 118140960795 + 6418384 * 2 ^ 59
def prefixEnd_6418384 : Nat := 4983230072969 + 3 ^ 40 * 6418384 * 2
def baseEnd_6418384 : Nat := 3295716017127321276782395

theorem tailTrace_6418384 : CollatzResearch.WordTrace tailWord_6418384 prefixEnd_6418384 3295716017127321276782395 := by
  unfold tailWord_6418384
  simp only [CollatzResearch.WordTrace]
  refine ⟨117048848189649207780771103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156065130919532277041028137 117048848189649207780771103)
  ·
    refine ⟨175573272284473811671156655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117048848189649207780771103 175573272284473811671156655)
    ·
      refine ⟨263359908426710717506734983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175573272284473811671156655 263359908426710717506734983)
      ·
        refine ⟨395039862640066076260102475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263359908426710717506734983 395039862640066076260102475)
        ·
          refine ⟨592559793960099114390153713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395039862640066076260102475 592559793960099114390153713)
          ·
            refine ⟨444419845470074335792615285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 592559793960099114390153713 444419845470074335792615285)
            ·
              refine ⟨41664360512819468980557683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 444419845470074335792615285 41664360512819468980557683)
              ·
                refine ⟨62496540769229203470836525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41664360512819468980557683 62496540769229203470836525)
                ·
                  refine ⟨23436202788460951301563697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62496540769229203470836525 23436202788460951301563697)
                  ·
                    refine ⟨17577152091345713476172773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23436202788460951301563697 17577152091345713476172773)
                    ·
                      refine ⟨3295716017127321276782395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17577152091345713476172773 3295716017127321276782395)
                      ·
                        rfl

theorem cell23_6418384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 4].length) (baseStart_6418384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418384 prefixEnd_6418384 := by exact prefixLift 6418384
  have htrace : WordTrace (prefixWord ++ tailWord_6418384) baseStart_6418384 baseEnd_6418384 := by
    simpa [prefixWord, tailWord_6418384, baseEnd_6418384] using wordTrace_append hprefix tailTrace_6418384
  have hstable : (prefixWord ++ tailWord_6418384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418384).length < 2 ^ (prefixWord ++ tailWord_6418384).sum := by decide
  have hdescent : baseEnd_6418384 < baseStart_6418384 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418394 : List Nat := [3, 1, 1, 2, 5, 11]
def baseStart_6418394 : Nat := 118140960795 + 6418394 * 2 ^ 59
def prefixEnd_6418394 : Nat := 4983230072969 + 3 ^ 40 * 6418394 * 2
def baseEnd_6418394 : Nat := 13562638485324552418343

theorem tailTrace_6418394 : CollatzResearch.WordTrace tailWord_6418394 prefixEnd_6418394 13562638485324552418343 := by
  unfold tailWord_6418394
  simp only [CollatzResearch.WordTrace]
  refine ⟨58524515277315546817351559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156065374072841458179604157 58524515277315546817351559)
  ·
    refine ⟨87786772915973320226027339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58524515277315546817351559 87786772915973320226027339)
    ·
      refine ⟨131680159373959980339041009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87786772915973320226027339 131680159373959980339041009)
      ·
        refine ⟨98760119530469985254280757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131680159373959980339041009 98760119530469985254280757)
        ·
          refine ⟨9258761205981561117588821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98760119530469985254280757 9258761205981561117588821)
          ·
            refine ⟨13562638485324552418343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9258761205981561117588821 13562638485324552418343)
            ·
              rfl

theorem cell23_6418394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 11].length) (baseStart_6418394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418394 prefixEnd_6418394 := by exact prefixLift 6418394
  have htrace : WordTrace (prefixWord ++ tailWord_6418394) baseStart_6418394 baseEnd_6418394 := by
    simpa [prefixWord, tailWord_6418394, baseEnd_6418394] using wordTrace_append hprefix tailTrace_6418394
  have hstable : (prefixWord ++ tailWord_6418394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418394).length < 2 ^ (prefixWord ++ tailWord_6418394).sum := by decide
  have hdescent : baseEnd_6418394 < baseStart_6418394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418422 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2]
def baseStart_6418422 : Nat := 118140960795 + 6418422 * 2 ^ 59
def prefixEnd_6418422 : Nat := 4983230072969 + 3 ^ 40 * 6418422 * 2
def baseEnd_6418422 : Nat := 3295735529392192128107221

theorem tailTrace_6418422 : CollatzResearch.WordTrace tailWord_6418422 prefixEnd_6418422 3295735529392192128107221 := by
  unfold tailWord_6418422
  simp only [CollatzResearch.WordTrace]
  refine ⟨14631192647072546753214095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156066054902107165367617013 14631192647072546753214095)
  ·
    refine ⟨21946788970608820129821143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14631192647072546753214095 21946788970608820129821143)
    ·
      refine ⟨32920183455913230194731715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21946788970608820129821143 32920183455913230194731715)
      ·
        refine ⟨49380275183869845292097573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32920183455913230194731715 49380275183869845292097573)
        ·
          refine ⟨9258801596975595992268295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49380275183869845292097573 9258801596975595992268295)
          ·
            refine ⟨13888202395463393988402443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9258801596975595992268295 13888202395463393988402443)
            ·
              refine ⟨20832303593195090982603665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13888202395463393988402443 20832303593195090982603665)
              ·
                refine ⟨15624227694896318236952749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20832303593195090982603665 15624227694896318236952749)
                ·
                  refine ⟨5859085385586119338857281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15624227694896318236952749 5859085385586119338857281)
                  ·
                    refine ⟨4394314039189589504142961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5859085385586119338857281 4394314039189589504142961)
                    ·
                      refine ⟨3295735529392192128107221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4394314039189589504142961 3295735529392192128107221)
                      ·
                        rfl

theorem cell23_6418422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2].length) (baseStart_6418422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418422 prefixEnd_6418422 := by exact prefixLift 6418422
  have htrace : WordTrace (prefixWord ++ tailWord_6418422) baseStart_6418422 baseEnd_6418422 := by
    simpa [prefixWord, tailWord_6418422, baseEnd_6418422] using wordTrace_append hprefix tailTrace_6418422
  have hstable : (prefixWord ++ tailWord_6418422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418422).length < 2 ^ (prefixWord ++ tailWord_6418422).sum := by decide
  have hdescent : baseEnd_6418422 < baseStart_6418422 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418442 : List Nat := [3, 1, 2, 2, 4, 2, 2, 1, 1, 2, 3]
def baseStart_6418442 : Nat := 118140960795 + 6418442 * 2 ^ 59
def prefixEnd_6418442 : Nat := 4983230072969 + 3 ^ 40 * 6418442 * 2
def baseEnd_6418442 : Nat := 3295745799005282049857129

theorem tailTrace_6418442 : CollatzResearch.WordTrace tailWord_6418442 prefixEnd_6418442 3295745799005282049857129 := by
  unfold tailWord_6418442
  simp only [CollatzResearch.WordTrace]
  refine ⟨58524952953272072866788395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156066541208725527644769053 58524952953272072866788395)
  ·
    refine ⟨87787429429908109300182593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58524952953272072866788395 87787429429908109300182593)
    ·
      refine ⟨65840572072431081975136945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87787429429908109300182593 65840572072431081975136945)
      ·
        refine ⟨49380429054323311481352709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65840572072431081975136945 49380429054323311481352709)
        ·
          refine ⟨9258830447685620902753633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49380429054323311481352709 9258830447685620902753633)
          ·
            refine ⟨6944122835764215677065225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9258830447685620902753633 6944122835764215677065225)
            ·
              refine ⟨5208092126823161757798919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6944122835764215677065225 5208092126823161757798919)
              ·
                refine ⟨7812138190234742636698379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5208092126823161757798919 7812138190234742636698379)
                ·
                  refine ⟨11718207285352113955047569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7812138190234742636698379 11718207285352113955047569)
                  ·
                    refine ⟨8788655464014085466285677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11718207285352113955047569 8788655464014085466285677)
                    ·
                      refine ⟨3295745799005282049857129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8788655464014085466285677 3295745799005282049857129)
                      ·
                        rfl

theorem cell23_6418442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_6418442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418442 prefixEnd_6418442 := by exact prefixLift 6418442
  have htrace : WordTrace (prefixWord ++ tailWord_6418442) baseStart_6418442 baseEnd_6418442 := by
    simpa [prefixWord, tailWord_6418442, baseEnd_6418442] using wordTrace_append hprefix tailTrace_6418442
  have hstable : (prefixWord ++ tailWord_6418442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418442).length < 2 ^ (prefixWord ++ tailWord_6418442).sum := by decide
  have hdescent : baseEnd_6418442 < baseStart_6418442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418445 : List Nat := [1, 7, 1, 2, 1, 1, 10]
def baseStart_6418445 : Nat := 118140960795 + 6418445 * 2 ^ 59
def prefixEnd_6418445 : Nat := 4983230072969 + 3 ^ 40 * 6418445 * 2
def baseEnd_6418445 : Nat := 40688238758607969606415

theorem tailTrace_6418445 : CollatzResearch.WordTrace tailWord_6418445 prefixEnd_6418445 40688238758607969606415 := by
  unfold tailWord_6418445
  simp only [CollatzResearch.WordTrace]
  refine ⟨234099921232077422979512789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156066614154718281986341859 234099921232077422979512789)
  ·
    refine ⟨5486716903876814601082331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 234099921232077422979512789 5486716903876814601082331)
    ·
      refine ⟨8230075355815221901623497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5486716903876814601082331 8230075355815221901623497)
      ·
        refine ⟨6172556516861416426217623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8230075355815221901623497 6172556516861416426217623)
        ·
          refine ⟨9258834775292124639326435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6172556516861416426217623 9258834775292124639326435)
          ·
            refine ⟨13888252162938186958989653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9258834775292124639326435 13888252162938186958989653)
            ·
              refine ⟨40688238758607969606415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13888252162938186958989653 40688238758607969606415)
              ·
                rfl

theorem cell23_6418445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 10].length) (baseStart_6418445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418445 prefixEnd_6418445 := by exact prefixLift 6418445
  have htrace : WordTrace (prefixWord ++ tailWord_6418445) baseStart_6418445 baseEnd_6418445 := by
    simpa [prefixWord, tailWord_6418445, baseEnd_6418445] using wordTrace_append hprefix tailTrace_6418445
  have hstable : (prefixWord ++ tailWord_6418445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418445).length < 2 ^ (prefixWord ++ tailWord_6418445).sum := by decide
  have hdescent : baseEnd_6418445 < baseStart_6418445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418448 : List Nat := [2, 1, 1, 1, 1, 1, 1, 9, 1, 3, 2]
def baseStart_6418448 : Nat := 118140960795 + 6418448 * 2 ^ 59
def prefixEnd_6418448 : Nat := 4983230072969 + 3 ^ 40 * 6418448 * 2
def baseEnd_6418448 : Nat := 3295748879889209026382101

theorem tailTrace_6418448 : CollatzResearch.WordTrace tailWord_6418448 prefixEnd_6418448 3295748879889209026382101 := by
  unfold tailWord_6418448
  simp only [CollatzResearch.WordTrace]
  refine ⟨117050015325533277245935999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156066687100711036327914665 117050015325533277245935999)
  ·
    refine ⟨175575022988299915868903999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117050015325533277245935999 175575022988299915868903999)
    ·
      refine ⟨263362534482449873803355999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175575022988299915868903999 263362534482449873803355999)
      ·
        refine ⟨395043801723674810705033999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263362534482449873803355999 395043801723674810705033999)
        ·
          refine ⟨592565702585512216057550999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395043801723674810705033999 592565702585512216057550999)
          ·
            refine ⟨888848553878268324086326499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592565702585512216057550999 888848553878268324086326499)
            ·
              refine ⟨1333272830817402486129489749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888848553878268324086326499 1333272830817402486129489749)
              ·
                refine ⟨7812145493070717692164979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1333272830817402486129489749 7812145493070717692164979)
                ·
                  refine ⟨11718218239606076538247469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7812145493070717692164979 11718218239606076538247469)
                  ·
                    refine ⟨4394331839852278701842801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11718218239606076538247469 4394331839852278701842801)
                    ·
                      refine ⟨3295748879889209026382101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4394331839852278701842801 3295748879889209026382101)
                      ·
                        rfl

theorem cell23_6418448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 1, 3, 2].length) (baseStart_6418448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418448 prefixEnd_6418448 := by exact prefixLift 6418448
  have htrace : WordTrace (prefixWord ++ tailWord_6418448) baseStart_6418448 baseEnd_6418448 := by
    simpa [prefixWord, tailWord_6418448, baseEnd_6418448] using wordTrace_append hprefix tailTrace_6418448
  have hstable : (prefixWord ++ tailWord_6418448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418448).length < 2 ^ (prefixWord ++ tailWord_6418448).sum := by decide
  have hdescent : baseEnd_6418448 < baseStart_6418448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418455 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 4, 1, 3]
def baseStart_6418455 : Nat := 118140960795 + 6418455 * 2 ^ 59
def prefixEnd_6418455 : Nat := 4983230072969 + 3 ^ 40 * 6418455 * 2
def baseEnd_6418455 : Nat := 3295752474253790498994569

theorem tailTrace_6418455 : CollatzResearch.WordTrace tailWord_6418455 prefixEnd_6418455 3295752474253790498994569 := by
  unfold tailWord_6418455
  simp only [CollatzResearch.WordTrace]
  refine ⟨234100285962041194687376819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156066857308027463124917879 234100285962041194687376819)
  ·
    refine ⟨351150428943061792031065229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234100285962041194687376819 351150428943061792031065229)
    ·
      refine ⟨131681410853648172011649461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351150428943061792031065229 131681410853648172011649461)
      ·
        refine ⟨12345132267529516126092137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131681410853648172011649461 12345132267529516126092137)
        ·
          refine ⟨9258849200647137094569103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12345132267529516126092137 9258849200647137094569103)
          ·
            refine ⟨13888273800970705641853655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9258849200647137094569103 13888273800970705641853655)
            ·
              refine ⟨20832410701456058462780483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13888273800970705641853655 20832410701456058462780483)
              ·
                refine ⟨31248616052184087694170725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20832410701456058462780483 31248616052184087694170725)
                ·
                  refine ⟨5859115509784516442657011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31248616052184087694170725 5859115509784516442657011)
                  ·
                    refine ⟨8788673264676774663985517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5859115509784516442657011 8788673264676774663985517)
                    ·
                      refine ⟨3295752474253790498994569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8788673264676774663985517 3295752474253790498994569)
                      ·
                        rfl

theorem cell23_6418455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_6418455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418455 prefixEnd_6418455 := by exact prefixLift 6418455
  have htrace : WordTrace (prefixWord ++ tailWord_6418455) baseStart_6418455 baseEnd_6418455 := by
    simpa [prefixWord, tailWord_6418455, baseEnd_6418455] using wordTrace_append hprefix tailTrace_6418455
  have hstable : (prefixWord ++ tailWord_6418455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418455).length < 2 ^ (prefixWord ++ tailWord_6418455).sum := by decide
  have hdescent : baseEnd_6418455 < baseStart_6418455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418472 : List Nat := [2, 1, 5, 3, 1, 2, 1, 1, 1, 3, 3]
def baseStart_6418472 : Nat := 118140960795 + 6418472 * 2 ^ 59
def prefixEnd_6418472 : Nat := 4983230072969 + 3 ^ 40 * 6418472 * 2
def baseEnd_6418472 : Nat := 3295761203424916932481991

theorem tailTrace_6418472 : CollatzResearch.WordTrace tailWord_6418472 prefixEnd_6418472 3295761203424916932481991 := by
  unfold tailWord_6418472
  simp only [CollatzResearch.WordTrace]
  refine ⟨117050453001489803295372835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156067270668653071060497113 117050453001489803295372835)
  ·
    refine ⟨175575679502234704943059253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117050453001489803295372835 175575679502234704943059253)
    ·
      refine ⟨16460219953334503588411805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 175575679502234704943059253 16460219953334503588411805)
      ·
        refine ⟨6172582482500438845654427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16460219953334503588411805 6172582482500438845654427)
        ·
          refine ⟨9258873723750658268481641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6172582482500438845654427 9258873723750658268481641)
          ·
            refine ⟨6944155292812993701361231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9258873723750658268481641 6944155292812993701361231)
            ·
              refine ⟨10416232939219490552041847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6944155292812993701361231 10416232939219490552041847)
              ·
                refine ⟨15624349408829235828062771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10416232939219490552041847 15624349408829235828062771)
                ·
                  refine ⟨23436524113243853742094157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15624349408829235828062771 23436524113243853742094157)
                  ·
                    refine ⟨8788696542466445153285309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23436524113243853742094157 8788696542466445153285309)
                    ·
                      refine ⟨3295761203424916932481991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8788696542466445153285309 3295761203424916932481991)
                      ·
                        rfl

theorem cell23_6418472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_6418472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418472 prefixEnd_6418472 := by exact prefixLift 6418472
  have htrace : WordTrace (prefixWord ++ tailWord_6418472) baseStart_6418472 baseEnd_6418472 := by
    simpa [prefixWord, tailWord_6418472, baseEnd_6418472] using wordTrace_append hprefix tailTrace_6418472
  have hstable : (prefixWord ++ tailWord_6418472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418472).length < 2 ^ (prefixWord ++ tailWord_6418472).sum := by decide
  have hdescent : baseEnd_6418472 < baseStart_6418472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418541 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_6418541 : Nat := 118140960795 + 6418541 * 2 ^ 59
def prefixEnd_6418541 : Nat := 4983230072969 + 3 ^ 40 * 6418541 * 2
def baseEnd_6418541 : Nat := 3295796633590077162519173

theorem tailTrace_6418541 : CollatzResearch.WordTrace tailWord_6418541 prefixEnd_6418541 3295796633590077162519173 := by
  unfold tailWord_6418541
  simp only [CollatzResearch.WordTrace]
  refine ⟨234103422639729631375007477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156068948426486420916671651 234103422639729631375007477)
  ·
    refine ⟨21947195872474652941406951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234103422639729631375007477 21947195872474652941406951)
    ·
      refine ⟨32920793808711979412110427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21947195872474652941406951 32920793808711979412110427)
      ·
        refine ⟨49381190713067969118165641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32920793808711979412110427 49381190713067969118165641)
        ·
          refine ⟨37035893034800976838624231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49381190713067969118165641 37035893034800976838624231)
          ·
            refine ⟨55553839552201465257936347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37035893034800976838624231 55553839552201465257936347)
            ·
              refine ⟨83330759328302197886904521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55553839552201465257936347 83330759328302197886904521)
              ·
                refine ⟨62498069496226648415178391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83330759328302197886904521 62498069496226648415178391)
                ·
                  refine ⟨93747104244339972622767587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62498069496226648415178391 93747104244339972622767587)
                  ·
                    refine ⟨140620656366509958934151381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93747104244339972622767587 140620656366509958934151381)
                    ·
                      refine ⟨3295796633590077162519173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140620656366509958934151381 3295796633590077162519173)
                      ·
                        rfl

theorem cell23_6418541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_6418541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418541 prefixEnd_6418541 := by exact prefixLift 6418541
  have htrace : WordTrace (prefixWord ++ tailWord_6418541) baseStart_6418541 baseEnd_6418541 := by
    simpa [prefixWord, tailWord_6418541, baseEnd_6418541] using wordTrace_append hprefix tailTrace_6418541
  have hstable : (prefixWord ++ tailWord_6418541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418541).length < 2 ^ (prefixWord ++ tailWord_6418541).sum := by decide
  have hdescent : baseEnd_6418541 < baseStart_6418541 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418571 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 3]
def baseStart_6418571 : Nat := 118140960795 + 6418571 * 2 ^ 59
def prefixEnd_6418571 : Nat := 4983230072969 + 3 ^ 40 * 6418571 * 2
def baseEnd_6418571 : Nat := 3295812038009712045144035

theorem tailTrace_6418571 : CollatzResearch.WordTrace tailWord_6418571 prefixEnd_6418571 3295812038009712045144035 := by
  unfold tailWord_6418571
  simp only [CollatzResearch.WordTrace]
  refine ⟨234104516829620946498599567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156069677886413964332399711 234104516829620946498599567)
  ·
    refine ⟨351156775244431419747899351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234104516829620946498599567 351156775244431419747899351)
    ·
      refine ⟨526735162866647129621849027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351156775244431419747899351 526735162866647129621849027)
      ·
        refine ⟨790102744299970694432773541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526735162866647129621849027 790102744299970694432773541)
        ·
          refine ⟨148144264556244505206145039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 790102744299970694432773541 148144264556244505206145039)
          ·
            refine ⟨222216396834366757809217559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148144264556244505206145039 222216396834366757809217559)
            ·
              refine ⟨333324595251550136713826339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222216396834366757809217559 333324595251550136713826339)
              ·
                refine ⟨499986892877325205070739509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333324595251550136713826339 499986892877325205070739509)
                ·
                  refine ⟨46873771207249237975381829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 499986892877325205070739509 46873771207249237975381829)
                  ·
                    refine ⟨8788832101359232120384093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46873771207249237975381829 8788832101359232120384093)
                    ·
                      refine ⟨3295812038009712045144035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8788832101359232120384093 3295812038009712045144035)
                      ·
                        rfl

theorem cell23_6418571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 4, 3].length) (baseStart_6418571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418571 prefixEnd_6418571 := by exact prefixLift 6418571
  have htrace : WordTrace (prefixWord ++ tailWord_6418571) baseStart_6418571 baseEnd_6418571 := by
    simpa [prefixWord, tailWord_6418571, baseEnd_6418571] using wordTrace_append hprefix tailTrace_6418571
  have hstable : (prefixWord ++ tailWord_6418571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418571).length < 2 ^ (prefixWord ++ tailWord_6418571).sum := by decide
  have hdescent : baseEnd_6418571 < baseStart_6418571 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418588 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_6418588 : Nat := 118140960795 + 6418588 * 2 ^ 59
def prefixEnd_6418588 : Nat := 4983230072969 + 3 ^ 40 * 6418588 * 2
def baseEnd_6418588 : Nat := 3295820767180838478631457

theorem tailTrace_6418588 : CollatzResearch.WordTrace tailWord_6418588 prefixEnd_6418588 3295820767180838478631457 := by
  unfold tailWord_6418588
  simp only [CollatzResearch.WordTrace]
  refine ⟨117052568435279679200984209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156070091247039572267978945 117052568435279679200984209)
  ·
    refine ⟨87789426326459759400738157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117052568435279679200984209 87789426326459759400738157)
    ·
      refine ⟨32921034872422409775276809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87789426326459759400738157 32921034872422409775276809)
      ·
        refine ⟨24690776154316807331457607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32921034872422409775276809 24690776154316807331457607)
        ·
          refine ⟨37036164231475210997186411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24690776154316807331457607 37036164231475210997186411)
          ·
            refine ⟨55554246347212816495779617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37036164231475210997186411 55554246347212816495779617)
            ·
              refine ⟨41665684760409612371834713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55554246347212816495779617 41665684760409612371834713)
              ·
                refine ⟨31249263570307209278876035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41665684760409612371834713 31249263570307209278876035)
                ·
                  refine ⟨46873895355460813918314053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31249263570307209278876035 46873895355460813918314053)
                  ·
                    refine ⟨8788855379148902609683885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46873895355460813918314053 8788855379148902609683885)
                    ·
                      refine ⟨3295820767180838478631457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8788855379148902609683885 3295820767180838478631457)
                      ·
                        rfl

theorem cell23_6418588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_6418588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418588 prefixEnd_6418588 := by exact prefixLift 6418588
  have htrace : WordTrace (prefixWord ++ tailWord_6418588) baseStart_6418588 baseEnd_6418588 := by
    simpa [prefixWord, tailWord_6418588, baseEnd_6418588] using wordTrace_append hprefix tailTrace_6418588
  have hstable : (prefixWord ++ tailWord_6418588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418588).length < 2 ^ (prefixWord ++ tailWord_6418588).sum := by decide
  have hdescent : baseEnd_6418588 < baseStart_6418588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418605 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_6418605 : Nat := 118140960795 + 6418605 * 2 ^ 59
def prefixEnd_6418605 : Nat := 4983230072969 + 3 ^ 40 * 6418605 * 2
def baseEnd_6418605 : Nat := 3295829496351964912118879

theorem tailTrace_6418605 : CollatzResearch.WordTrace tailWord_6418605 prefixEnd_6418605 3295829496351964912118879 := by
  unfold tailWord_6418605
  simp only [CollatzResearch.WordTrace]
  refine ⟨234105756911497770305337269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156070504607665180203558179 234105756911497770305337269)
  ·
    refine ⟨21947414710452915966125369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234105756911497770305337269 21947414710452915966125369)
    ·
      refine ⟨16460561032839686974594027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21947414710452915966125369 16460561032839686974594027)
      ·
        refine ⟨24690841549259530461891041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16460561032839686974594027 24690841549259530461891041)
        ·
          refine ⟨18518131161944647846418281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24690841549259530461891041 18518131161944647846418281)
          ·
            refine ⟨13888598371458485884813711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18518131161944647846418281 13888598371458485884813711)
            ·
              refine ⟨20832897557187728827220567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13888598371458485884813711 20832897557187728827220567)
              ·
                refine ⟨31249346335781593240830851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20832897557187728827220567 31249346335781593240830851)
                ·
                  refine ⟨46874019503672389861246277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31249346335781593240830851 46874019503672389861246277)
                  ·
                    refine ⟨8788878656938573098983677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46874019503672389861246277 8788878656938573098983677)
                    ·
                      refine ⟨3295829496351964912118879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8788878656938573098983677 3295829496351964912118879)
                      ·
                        rfl

theorem cell23_6418605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_6418605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418605 prefixEnd_6418605 := by exact prefixLift 6418605
  have htrace : WordTrace (prefixWord ++ tailWord_6418605) baseStart_6418605 baseEnd_6418605 := by
    simpa [prefixWord, tailWord_6418605, baseEnd_6418605] using wordTrace_append hprefix tailTrace_6418605
  have hstable : (prefixWord ++ tailWord_6418605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418605).length < 2 ^ (prefixWord ++ tailWord_6418605).sum := by decide
  have hdescent : baseEnd_6418605 < baseStart_6418605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418625 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 8]
def baseStart_6418625 : Nat := 118140960795 + 6418625 * 2 ^ 59
def prefixEnd_6418625 : Nat := 4983230072969 + 3 ^ 40 * 6418625 * 2
def baseEnd_6418625 : Nat := 366204418440561648207643

theorem tailTrace_6418625 : CollatzResearch.WordTrace tailWord_6418625 prefixEnd_6418625 366204418440561648207643 := by
  unfold tailWord_6418625
  simp only [CollatzResearch.WordTrace]
  refine ⟨234106486371425313721065329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156070990914283542480710219 234106486371425313721065329)
  ·
    refine ⟨175579864778568985290798997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234106486371425313721065329 175579864778568985290798997)
    ·
      refine ⟨8230306161495421185506203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 175579864778568985290798997 8230306161495421185506203)
      ·
        refine ⟨12345459242243131778259305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8230306161495421185506203 12345459242243131778259305)
        ·
          refine ⟨9259094431682348833694479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12345459242243131778259305 9259094431682348833694479)
          ·
            refine ⟨13888641647523523250541719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9259094431682348833694479 13888641647523523250541719)
            ·
              refine ⟨20832962471285284875812579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13888641647523523250541719 20832962471285284875812579)
              ·
                refine ⟨31249443706927927313718869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20832962471285284875812579 31249443706927927313718869)
                ·
                  refine ⟨366204418440561648207643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31249443706927927313718869 366204418440561648207643)
                  ·
                    rfl

theorem cell23_6418625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 8].length) (baseStart_6418625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418625 prefixEnd_6418625 := by exact prefixLift 6418625
  have htrace : WordTrace (prefixWord ++ tailWord_6418625) baseStart_6418625 baseEnd_6418625 := by
    simpa [prefixWord, tailWord_6418625, baseEnd_6418625] using wordTrace_append hprefix tailTrace_6418625
  have hstable : (prefixWord ++ tailWord_6418625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418625).length < 2 ^ (prefixWord ++ tailWord_6418625).sum := by decide
  have hdescent : baseEnd_6418625 < baseStart_6418625 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418628 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 1, 2, 6]
def baseStart_6418628 : Nat := 118140960795 + 6418628 * 2 ^ 59
def prefixEnd_6418628 : Nat := 4983230072969 + 3 ^ 40 * 6418628 * 2
def baseEnd_6418628 : Nat := 3295841306407018322131273

theorem tailTrace_6418628 : CollatzResearch.WordTrace tailWord_6418628 prefixEnd_6418628 3295841306407018322131273 := by
  unfold tailWord_6418628
  simp only [CollatzResearch.WordTrace]
  refine ⟨117053297895207222616712269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156071063860276296822283025 117053297895207222616712269)
  ·
    refine ⟨43894986710702708481267101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117053297895207222616712269 43894986710702708481267101)
    ·
      refine ⟨16460620016513515680475163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43894986710702708481267101 16460620016513515680475163)
      ·
        refine ⟨24690930024770273520712745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16460620016513515680475163 24690930024770273520712745)
        ·
          refine ⟨18518197518577705140534559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24690930024770273520712745 18518197518577705140534559)
          ·
            refine ⟨27777296277866557710801839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18518197518577705140534559 27777296277866557710801839)
            ·
              refine ⟨41665944416799836566202759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27777296277866557710801839 41665944416799836566202759)
              ·
                refine ⟨62498916625199754849304139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41665944416799836566202759 62498916625199754849304139)
                ·
                  refine ⟨93748374937799632273956209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62498916625199754849304139 93748374937799632273956209)
                  ·
                    refine ⟨70311281203349724205467157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93748374937799632273956209 70311281203349724205467157)
                    ·
                      refine ⟨3295841306407018322131273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70311281203349724205467157 3295841306407018322131273)
                      ·
                        rfl

theorem cell23_6418628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_6418628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418628 prefixEnd_6418628 := by exact prefixLift 6418628
  have htrace : WordTrace (prefixWord ++ tailWord_6418628) baseStart_6418628 baseEnd_6418628 := by
    simpa [prefixWord, tailWord_6418628, baseEnd_6418628] using wordTrace_append hprefix tailTrace_6418628
  have hstable : (prefixWord ++ tailWord_6418628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418628).length < 2 ^ (prefixWord ++ tailWord_6418628).sum := by decide
  have hdescent : baseEnd_6418628 < baseStart_6418628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418635 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 3, 1, 3]
def baseStart_6418635 : Nat := 118140960795 + 6418635 * 2 ^ 59
def prefixEnd_6418635 : Nat := 4983230072969 + 3 ^ 40 * 6418635 * 2
def baseEnd_6418635 : Nat := 3295844900771599794743741

theorem tailTrace_6418635 : CollatzResearch.WordTrace tailWord_6418635 prefixEnd_6418635 3295844900771599794743741 := by
  unfold tailWord_6418635
  simp only [CollatzResearch.WordTrace]
  refine ⟨234106851101389085428929359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156071234067592723619286239 234106851101389085428929359)
  ·
    refine ⟨351160276652083628143394039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234106851101389085428929359 351160276652083628143394039)
    ·
      refine ⟨526740414978125442215091059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351160276652083628143394039 526740414978125442215091059)
      ·
        refine ⟨790110622467188163322636589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526740414978125442215091059 790110622467188163322636589)
        ·
          refine ⟨296291483425195561245988721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 790110622467188163322636589 296291483425195561245988721)
          ·
            refine ⟨222218612568896670934491541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296291483425195561245988721 222218612568896670934491541)
            ·
              refine ⟨10416497464167031450054291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 222218612568896670934491541 10416497464167031450054291)
              ·
                refine ⟨15624746196250547175081437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10416497464167031450054291 15624746196250547175081437)
                ·
                  refine ⟨5859279823593955190655539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15624746196250547175081437 5859279823593955190655539)
                  ·
                    refine ⟨8788919735390932785983309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5859279823593955190655539 8788919735390932785983309)
                    ·
                      refine ⟨3295844900771599794743741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8788919735390932785983309 3295844900771599794743741)
                      ·
                        rfl

theorem cell23_6418635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 3, 1, 3].length) (baseStart_6418635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418635 prefixEnd_6418635 := by exact prefixLift 6418635
  have htrace : WordTrace (prefixWord ++ tailWord_6418635) baseStart_6418635 baseEnd_6418635 := by
    simpa [prefixWord, tailWord_6418635, baseEnd_6418635] using wordTrace_append hprefix tailTrace_6418635
  have hstable : (prefixWord ++ tailWord_6418635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418635).length < 2 ^ (prefixWord ++ tailWord_6418635).sum := by decide
  have hdescent : baseEnd_6418635 < baseStart_6418635 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418668 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 6, 4]
def baseStart_6418668 : Nat := 118140960795 + 6418668 * 2 ^ 59
def prefixEnd_6418668 : Nat := 4983230072969 + 3 ^ 40 * 6418668 * 2
def baseEnd_6418668 : Nat := 1098620615211066055210363

theorem tailTrace_6418668 : CollatzResearch.WordTrace tailWord_6418668 prefixEnd_6418668 1098620615211066055210363 := by
  unfold tailWord_6418668
  simp only [CollatzResearch.WordTrace]
  refine ⟨117054027355134766032440329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156072036473513021376587105 117054027355134766032440329)
  ·
    refine ⟨87790520516351074524330247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117054027355134766032440329 87790520516351074524330247)
    ·
      refine ⟨131685780774526611786495371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87790520516351074524330247 131685780774526611786495371)
      ·
        refine ⟨197528671161789917679743057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131685780774526611786495371 197528671161789917679743057)
        ·
          refine ⟨148146503371342438259807293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197528671161789917679743057 148146503371342438259807293)
          ·
            refine ⟨55554938764253414347427735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148146503371342438259807293 55554938764253414347427735)
            ·
              refine ⟨83332408146380121521141603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55554938764253414347427735 83332408146380121521141603)
              ·
                refine ⟨124998612219570182281712405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83332408146380121521141603 124998612219570182281712405)
                ·
                  refine ⟨5859309947792352294455269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 124998612219570182281712405 5859309947792352294455269)
                  ·
                    refine ⟨1098620615211066055210363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5859309947792352294455269 1098620615211066055210363)
                    ·
                      rfl

theorem cell23_6418668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 4].length) (baseStart_6418668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418668 prefixEnd_6418668 := by exact prefixLift 6418668
  have htrace : WordTrace (prefixWord ++ tailWord_6418668) baseStart_6418668 baseEnd_6418668 := by
    simpa [prefixWord, tailWord_6418668, baseEnd_6418668] using wordTrace_append hprefix tailTrace_6418668
  have hstable : (prefixWord ++ tailWord_6418668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418668).length < 2 ^ (prefixWord ++ tailWord_6418668).sum := by decide
  have hdescent : baseEnd_6418668 < baseStart_6418668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418686 : List Nat := [4, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3]
def baseStart_6418686 : Nat := 118140960795 + 6418686 * 2 ^ 59
def prefixEnd_6418686 : Nat := 4983230072969 + 3 ^ 40 * 6418686 * 2
def baseEnd_6418686 : Nat := 3295871088284979095206007

theorem tailTrace_6418686 : CollatzResearch.WordTrace tailWord_6418686 prefixEnd_6418686 3295871088284979095206007 := by
  unfold tailWord_6418686
  simp only [CollatzResearch.WordTrace]
  refine ⟨29263588903025540142379489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156072474149469547426023941 29263588903025540142379489)
  ·
    refine ⟨21947691677269155106784617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29263588903025540142379489 21947691677269155106784617)
    ·
      refine ⟨16460768757951866330088463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21947691677269155106784617 16460768757951866330088463)
      ·
        refine ⟨24691153136927799495132695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16460768757951866330088463 24691153136927799495132695)
        ·
          refine ⟨37036729705391699242699043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24691153136927799495132695 37036729705391699242699043)
          ·
            refine ⟨55555094558087548864048565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37036729705391699242699043 55555094558087548864048565)
            ·
              refine ⟨5208290114820707706004553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55555094558087548864048565 5208290114820707706004553)
              ·
                refine ⟨3906217586115530779503415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5208290114820707706004553 3906217586115530779503415)
                ·
                  refine ⟨5859326379173296169255123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3906217586115530779503415 5859326379173296169255123)
                  ·
                    refine ⟨8788989568759944253882685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5859326379173296169255123 8788989568759944253882685)
                    ·
                      refine ⟨3295871088284979095206007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8788989568759944253882685 3295871088284979095206007)
                      ·
                        rfl

theorem cell23_6418686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3].length) (baseStart_6418686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418686 prefixEnd_6418686 := by exact prefixLift 6418686
  have htrace : WordTrace (prefixWord ++ tailWord_6418686) baseStart_6418686 baseEnd_6418686 := by
    simpa [prefixWord, tailWord_6418686, baseEnd_6418686] using wordTrace_append hprefix tailTrace_6418686
  have hstable : (prefixWord ++ tailWord_6418686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418686).length < 2 ^ (prefixWord ++ tailWord_6418686).sum := by decide
  have hdescent : baseEnd_6418686 < baseStart_6418686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418748 : List Nat := [2, 2, 2, 2, 1, 2, 1, 1, 1, 5, 4]
def baseStart_6418748 : Nat := 118140960795 + 6418748 * 2 ^ 59
def prefixEnd_6418748 : Nat := 4983230072969 + 3 ^ 40 * 6418748 * 2
def baseEnd_6418748 : Nat := 3295902924085557852630721

theorem tailTrace_6418748 : CollatzResearch.WordTrace tailWord_6418748 prefixEnd_6418748 3295902924085557852630721 := by
  unfold tailWord_6418748
  simp only [CollatzResearch.WordTrace]
  refine ⟨117055486274989852863896449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156073981699986470485195265 117055486274989852863896449)
  ·
    refine ⟨87791614706242389647922337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117055486274989852863896449 87791614706242389647922337)
    ·
      refine ⟨65843711029681792235941753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87791614706242389647922337 65843711029681792235941753)
      ·
        refine ⟨49382783272261344176956315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65843711029681792235941753 49382783272261344176956315)
        ·
          refine ⟨74074174908392016265434473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49382783272261344176956315 74074174908392016265434473)
          ·
            refine ⟨55555631181294012199075855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74074174908392016265434473 55555631181294012199075855)
            ·
              refine ⟨83333446771941018298613783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55555631181294012199075855 83333446771941018298613783)
              ·
                refine ⟨125000170157911527447920675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83333446771941018298613783 125000170157911527447920675)
                ·
                  refine ⟨187500255236867291171881013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125000170157911527447920675 187500255236867291171881013)
                  ·
                    refine ⟨17578148928456308547363845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 187500255236867291171881013 17578148928456308547363845)
                    ·
                      refine ⟨3295902924085557852630721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17578148928456308547363845 3295902924085557852630721)
                      ·
                        rfl

theorem cell23_6418748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_6418748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418748 prefixEnd_6418748 := by exact prefixLift 6418748
  have htrace : WordTrace (prefixWord ++ tailWord_6418748) baseStart_6418748 baseEnd_6418748 := by
    simpa [prefixWord, tailWord_6418748, baseEnd_6418748] using wordTrace_append hprefix tailTrace_6418748
  have hstable : (prefixWord ++ tailWord_6418748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418748).length < 2 ^ (prefixWord ++ tailWord_6418748).sum := by decide
  have hdescent : baseEnd_6418748 < baseStart_6418748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418778 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4]
def baseStart_6418778 : Nat := 118140960795 + 6418778 * 2 ^ 59
def prefixEnd_6418778 : Nat := 4983230072969 + 3 ^ 40 * 6418778 * 2
def baseEnd_6418778 : Nat := 3295918328505192735255583

theorem tailTrace_6418778 : CollatzResearch.WordTrace tailWord_6418778 prefixEnd_6418778 3295918328505192735255583 := by
  unfold tailWord_6418778
  simp only [CollatzResearch.WordTrace]
  refine ⟨58528016684967755212846247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156074711159914013900923325 58528016684967755212846247)
  ·
    refine ⟨87792025027451632819269371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58528016684967755212846247 87792025027451632819269371)
    ·
      refine ⟨131688037541177449228904057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87792025027451632819269371 131688037541177449228904057)
      ·
        refine ⟨98766028155883086921678043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131688037541177449228904057 98766028155883086921678043)
        ·
          refine ⟨148149042233824630382517065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98766028155883086921678043 148149042233824630382517065)
          ·
            refine ⟨111111781675368472786887799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148149042233824630382517065 111111781675368472786887799)
            ·
              refine ⟨166667672513052709180331699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111111781675368472786887799 166667672513052709180331699)
              ·
                refine ⟨250001508769579063770497549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166667672513052709180331699 250001508769579063770497549)
                ·
                  refine ⟨93750565788592148913936581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250001508769579063770497549 93750565788592148913936581)
                  ·
                    refine ⟨17578231085361027921363109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93750565788592148913936581 17578231085361027921363109)
                    ·
                      refine ⟨3295918328505192735255583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17578231085361027921363109 3295918328505192735255583)
                      ·
                        rfl

theorem cell23_6418778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_6418778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418778 prefixEnd_6418778 := by exact prefixLift 6418778
  have htrace : WordTrace (prefixWord ++ tailWord_6418778) baseStart_6418778 baseEnd_6418778 := by
    simpa [prefixWord, tailWord_6418778, baseEnd_6418778] using wordTrace_append hprefix tailTrace_6418778
  have hstable : (prefixWord ++ tailWord_6418778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418778).length < 2 ^ (prefixWord ++ tailWord_6418778).sum := by decide
  have hdescent : baseEnd_6418778 < baseStart_6418778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418786 : List Nat := [3, 3, 2, 1, 1, 2, 4, 1, 1, 3, 2]
def baseStart_6418786 : Nat := 118140960795 + 6418786 * 2 ^ 59
def prefixEnd_6418786 : Nat := 4983230072969 + 3 ^ 40 * 6418786 * 2
def baseEnd_6418786 : Nat := 3295922436350428703955547

theorem tailTrace_6418786 : CollatzResearch.WordTrace tailWord_6418786 prefixEnd_6418786 3295922436350428703955547 := by
  unfold tailWord_6418786
  simp only [CollatzResearch.WordTrace]
  refine ⟨58528089630960509554419053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156074905682561358811784141 58528089630960509554419053)
  ·
    refine ⟨21948033611610191082907145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58528089630960509554419053 21948033611610191082907145)
    ·
      refine ⟨16461025208707643312180359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21948033611610191082907145 16461025208707643312180359)
      ·
        refine ⟨24691537813061464968270539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16461025208707643312180359 24691537813061464968270539)
        ·
          refine ⟨37037306719592197452405809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24691537813061464968270539 37037306719592197452405809)
          ·
            refine ⟨27777980039694148089304357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37037306719592197452405809 27777980039694148089304357)
            ·
              refine ⟨5208371257442652766744567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27777980039694148089304357 5208371257442652766744567)
              ·
                refine ⟨7812556886163979150116851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5208371257442652766744567 7812556886163979150116851)
                ·
                  refine ⟨11718835329245968725175277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7812556886163979150116851 11718835329245968725175277)
                  ·
                    refine ⟨4394563248467238271940729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11718835329245968725175277 4394563248467238271940729)
                    ·
                      refine ⟨3295922436350428703955547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4394563248467238271940729 3295922436350428703955547)
                      ·
                        rfl

theorem cell23_6418786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_6418786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418786 prefixEnd_6418786 := by exact prefixLift 6418786
  have htrace : WordTrace (prefixWord ++ tailWord_6418786) baseStart_6418786 baseEnd_6418786 := by
    simpa [prefixWord, tailWord_6418786, baseEnd_6418786] using wordTrace_append hprefix tailTrace_6418786
  have hstable : (prefixWord ++ tailWord_6418786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418786).length < 2 ^ (prefixWord ++ tailWord_6418786).sum := by decide
  have hdescent : baseEnd_6418786 < baseStart_6418786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418788 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 9]
def baseStart_6418788 : Nat := 118140960795 + 6418788 * 2 ^ 59
def prefixEnd_6418788 : Nat := 4983230072969 + 3 ^ 40 * 6418788 * 2
def baseEnd_6418788 : Nat := 366213718145748632903393

theorem tailTrace_6418788 : CollatzResearch.WordTrace tailWord_6418788 prefixEnd_6418788 366213718145748632903393 := by
  unfold tailWord_6418788
  simp only [CollatzResearch.WordTrace]
  refine ⟨117056215734917396279624509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156074954313223195039499345 117056215734917396279624509)
  ·
    refine ⟨43896080900594023604859191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117056215734917396279624509 43896080900594023604859191)
    ·
      refine ⟨65844121350891035407288787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43896080900594023604859191 65844121350891035407288787)
      ·
        refine ⟨98766182026336553110933181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65844121350891035407288787 98766182026336553110933181)
        ·
          refine ⟨37037318259876207416599943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98766182026336553110933181 37037318259876207416599943)
          ·
            refine ⟨55555977389814311124899915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37037318259876207416599943 55555977389814311124899915)
            ·
              refine ⟨83333966084721466687349873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55555977389814311124899915 83333966084721466687349873)
              ·
                refine ⟨62500474563541100015512405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83333966084721466687349873 62500474563541100015512405)
                ·
                  refine ⟨366213718145748632903393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62500474563541100015512405 366213718145748632903393)
                  ·
                    rfl

theorem cell23_6418788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 9].length) (baseStart_6418788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418788 prefixEnd_6418788 := by exact prefixLift 6418788
  have htrace : WordTrace (prefixWord ++ tailWord_6418788) baseStart_6418788 baseEnd_6418788 := by
    simpa [prefixWord, tailWord_6418788, baseEnd_6418788] using wordTrace_append hprefix tailTrace_6418788
  have hstable : (prefixWord ++ tailWord_6418788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418788).length < 2 ^ (prefixWord ++ tailWord_6418788).sum := by decide
  have hdescent : baseEnd_6418788 < baseStart_6418788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418805 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 7]
def baseStart_6418805 : Nat := 118140960795 + 6418805 * 2 ^ 59
def prefixEnd_6418805 : Nat := 4983230072969 + 3 ^ 40 * 6418805 * 2
def baseEnd_6418805 : Nat := 366214688053651569957551

theorem tailTrace_6418805 : CollatzResearch.WordTrace tailWord_6418805 prefixEnd_6418805 366214688053651569957551 := by
  unfold tailWord_6418805
  simp only [CollatzResearch.WordTrace]
  refine ⟨234113051510773204462617869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156075367673848802975078579 234113051510773204462617869)
  ·
    refine ⟨87792394316539951673481701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234113051510773204462617869 87792394316539951673481701)
    ·
      refine ⟨16461073934351240938777819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87792394316539951673481701 16461073934351240938777819)
      ·
        refine ⟨24691610901526861408166729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16461073934351240938777819 24691610901526861408166729)
        ·
          refine ⟨18518708176145146056125047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24691610901526861408166729 18518708176145146056125047)
          ·
            refine ⟨27778062264217719084187571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18518708176145146056125047 27778062264217719084187571)
            ·
              refine ⟨41667093396326578626281357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27778062264217719084187571 41667093396326578626281357)
              ·
                refine ⟨15625160023622466984855509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41667093396326578626281357 15625160023622466984855509)
                ·
                  refine ⟨366214688053651569957551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15625160023622466984855509 366214688053651569957551)
                  ·
                    rfl

theorem cell23_6418805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 7].length) (baseStart_6418805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418805 prefixEnd_6418805 := by exact prefixLift 6418805
  have htrace : WordTrace (prefixWord ++ tailWord_6418805) baseStart_6418805 baseEnd_6418805 := by
    simpa [prefixWord, tailWord_6418805, baseEnd_6418805] using wordTrace_append hprefix tailTrace_6418805
  have hstable : (prefixWord ++ tailWord_6418805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418805).length < 2 ^ (prefixWord ++ tailWord_6418805).sum := by decide
  have hdescent : baseEnd_6418805 < baseStart_6418805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418856 : List Nat := [2, 1, 6, 1, 1, 2, 3, 2, 5]
def baseStart_6418856 : Nat := 118140960795 + 6418856 * 2 ^ 59
def prefixEnd_6418856 : Nat := 4983230072969 + 3 ^ 40 * 6418856 * 2
def baseEnd_6418856 : Nat := 366217597777360381120025

theorem tailTrace_6418856 : CollatzResearch.WordTrace tailWord_6418856 prefixEnd_6418856 366217597777360381120025 := by
  unfold tailWord_6418856
  simp only [CollatzResearch.WordTrace]
  refine ⟨117057455816794220086362211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156076607755725626781816281 117057455816794220086362211)
  ·
    refine ⟨175586183725191330129543317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117057455816794220086362211 175586183725191330129543317)
    ·
      refine ⟨8230602362118343599822343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 175586183725191330129543317 8230602362118343599822343)
      ·
        refine ⟨12345903543177515399733515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8230602362118343599822343 12345903543177515399733515)
        ·
          refine ⟨18518855314766273099600273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12345903543177515399733515 18518855314766273099600273)
          ·
            refine ⟨13889141486074704824700205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18518855314766273099600273 13889141486074704824700205)
            ·
              refine ⟨5208428057278014309262577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13889141486074704824700205 5208428057278014309262577)
              ·
                refine ⟨3906321042958510731946933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5208428057278014309262577 3906321042958510731946933)
                ·
                  refine ⟨366217597777360381120025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3906321042958510731946933 366217597777360381120025)
                  ·
                    rfl

theorem cell23_6418856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 5].length) (baseStart_6418856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418856 prefixEnd_6418856 := by exact prefixLift 6418856
  have htrace : WordTrace (prefixWord ++ tailWord_6418856) baseStart_6418856 baseEnd_6418856 := by
    simpa [prefixWord, tailWord_6418856, baseEnd_6418856] using wordTrace_append hprefix tailTrace_6418856
  have hstable : (prefixWord ++ tailWord_6418856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418856).length < 2 ^ (prefixWord ++ tailWord_6418856).sum := by decide
  have hdescent : baseEnd_6418856 < baseStart_6418856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418902 : List Nat := [5, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_6418902 : Nat := 118140960795 + 6418902 * 2 ^ 59
def prefixEnd_6418902 : Nat := 4983230072969 + 3 ^ 40 * 6418902 * 2
def baseEnd_6418902 : Nat := 3295982000106350250105013

theorem tailTrace_6418902 : CollatzResearch.WordTrace tailWord_6418902 prefixEnd_6418902 3295982000106350250105013 := by
  unfold tailWord_6418902
  simp only [CollatzResearch.WordTrace]
  refine ⟨14632286836963861876806185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156077726260947860019265973 14632286836963861876806185)
  ·
    refine ⟨10974215127722896407604639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14632286836963861876806185 10974215127722896407604639)
    ·
      refine ⟨16461322691584344611406959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10974215127722896407604639 16461322691584344611406959)
      ·
        refine ⟨24691984037376516917110439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16461322691584344611406959 24691984037376516917110439)
        ·
          refine ⟨37037976056064775375665659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24691984037376516917110439 37037976056064775375665659)
          ·
            refine ⟨55556964084097163063498489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37037976056064775375665659 55556964084097163063498489)
            ·
              refine ⟨41667723063072872297623867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55556964084097163063498489 41667723063072872297623867)
              ·
                refine ⟨62501584594609308446435801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41667723063072872297623867 62501584594609308446435801)
                ·
                  refine ⟨46876188445956981334826851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62501584594609308446435801 46876188445956981334826851)
                  ·
                    refine ⟨70314282668935472002240277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46876188445956981334826851 70314282668935472002240277)
                    ·
                      refine ⟨3295982000106350250105013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70314282668935472002240277 3295982000106350250105013)
                      ·
                        rfl

theorem cell23_6418902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_6418902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418902 prefixEnd_6418902 := by exact prefixLift 6418902
  have htrace : WordTrace (prefixWord ++ tailWord_6418902) baseStart_6418902 baseEnd_6418902 := by
    simpa [prefixWord, tailWord_6418902, baseEnd_6418902] using wordTrace_append hprefix tailTrace_6418902
  have hstable : (prefixWord ++ tailWord_6418902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418902).length < 2 ^ (prefixWord ++ tailWord_6418902).sum := by decide
  have hdescent : baseEnd_6418902 < baseStart_6418902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418949 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 2, 3, 2]
def baseStart_6418949 : Nat := 118140960795 + 6418949 * 2 ^ 59
def prefixEnd_6418949 : Nat := 4983230072969 + 3 ^ 40 * 6418949 * 2
def baseEnd_6418949 : Nat := 3296006133697111566217297

theorem tailTrace_6418949 : CollatzResearch.WordTrace tailWord_6418949 prefixEnd_6418949 3296006133697111566217297 := by
  unfold tailWord_6418949
  simp only [CollatzResearch.WordTrace]
  refine ⟨234118303622251517055859901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156078869081501011370573267 234118303622251517055859901)
  ·
    refine ⟨87794363858344318895947463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234118303622251517055859901 87794363858344318895947463)
    ·
      refine ⟨131691545787516478343921195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87794363858344318895947463 131691545787516478343921195)
      ·
        refine ⟨197537318681274717515881793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131691545787516478343921195 197537318681274717515881793)
        ·
          refine ⟨148152989010956038136911345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197537318681274717515881793 148152989010956038136911345)
          ·
            refine ⟨111114741758217028602683509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148152989010956038136911345 111114741758217028602683509)
            ·
              refine ⟨10417007039832846431501579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111114741758217028602683509 10417007039832846431501579)
              ·
                refine ⟨15625510559749269647252369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10417007039832846431501579 15625510559749269647252369)
                ·
                  refine ⟨11719132919811952235439277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15625510559749269647252369 11719132919811952235439277)
                  ·
                    refine ⟨4394674844929482088289729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11719132919811952235439277 4394674844929482088289729)
                    ·
                      refine ⟨3296006133697111566217297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4394674844929482088289729 3296006133697111566217297)
                      ·
                        rfl

theorem cell23_6418949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 3, 2].length) (baseStart_6418949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418949 prefixEnd_6418949 := by exact prefixLift 6418949
  have htrace : WordTrace (prefixWord ++ tailWord_6418949) baseStart_6418949 baseEnd_6418949 := by
    simpa [prefixWord, tailWord_6418949, baseEnd_6418949] using wordTrace_append hprefix tailTrace_6418949
  have hstable : (prefixWord ++ tailWord_6418949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418949).length < 2 ^ (prefixWord ++ tailWord_6418949).sum := by decide
  have hdescent : baseEnd_6418949 < baseStart_6418949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418950 : List Nat := [6, 2, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_6418950 : Nat := 118140960795 + 6418950 * 2 ^ 59
def prefixEnd_6418950 : Nat := 4983230072969 + 3 ^ 40 * 6418950 * 2
def baseEnd_6418950 : Nat := 1098668882392588687434931

theorem tailTrace_6418950 : CollatzResearch.WordTrace tailWord_6418950 prefixEnd_6418950 1098668882392588687434931 := by
  unfold tailWord_6418950
  simp only [CollatzResearch.WordTrace]
  refine ⟨7316198127976496694582697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 156078893396831929484430869 7316198127976496694582697)
  ·
    refine ⟨5487148595982372520937023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7316198127976496694582697 5487148595982372520937023)
    ·
      refine ⟨8230722893973558781405535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5487148595982372520937023 8230722893973558781405535)
      ·
        refine ⟨12346084340960338172108303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8230722893973558781405535 12346084340960338172108303)
        ·
          refine ⟨18519126511440507258162455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12346084340960338172108303 18519126511440507258162455)
          ·
            refine ⟨27778689767160760887243683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18519126511440507258162455 27778689767160760887243683)
            ·
              refine ⟨41668034650741141330865525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27778689767160760887243683 41668034650741141330865525)
              ·
                refine ⟨3906378248506981999768643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41668034650741141330865525 3906378248506981999768643)
                ·
                  refine ⟨5859567372760472999652965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3906378248506981999768643 5859567372760472999652965)
                  ·
                    refine ⟨1098668882392588687434931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5859567372760472999652965 1098668882392588687434931)
                    ·
                      rfl

theorem cell23_6418950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_6418950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418950 prefixEnd_6418950 := by exact prefixLift 6418950
  have htrace : WordTrace (prefixWord ++ tailWord_6418950) baseStart_6418950 baseEnd_6418950 := by
    simpa [prefixWord, tailWord_6418950, baseEnd_6418950] using wordTrace_append hprefix tailTrace_6418950
  have hstable : (prefixWord ++ tailWord_6418950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418950).length < 2 ^ (prefixWord ++ tailWord_6418950).sum := by decide
  have hdescent : baseEnd_6418950 < baseStart_6418950 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418956 : List Nat := [2, 2, 1, 2, 4, 1, 1, 5, 1, 1, 3]
def baseStart_6418956 : Nat := 118140960795 + 6418956 * 2 ^ 59
def prefixEnd_6418956 : Nat := 4983230072969 + 3 ^ 40 * 6418956 * 2
def baseEnd_6418956 : Nat := 3296009728061693038829765

theorem tailTrace_6418956 : CollatzResearch.WordTrace tailWord_6418956 prefixEnd_6418956 3296009728061693038829765 := by
  unfold tailWord_6418956
  simp only [CollatzResearch.WordTrace]
  refine ⟨117059279466613078625682361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156079039288817438167576481 117059279466613078625682361)
  ·
    refine ⟨87794459599959808969261771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117059279466613078625682361 87794459599959808969261771)
    ·
      refine ⟨131691689399939713453892657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87794459599959808969261771 131691689399939713453892657)
      ·
        refine ⟨98768767049954785090419493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131691689399939713453892657 98768767049954785090419493)
        ·
          refine ⟨18519143821866522204453655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98768767049954785090419493 18519143821866522204453655)
          ·
            refine ⟨27778715732799783306680483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18519143821866522204453655 27778715732799783306680483)
            ·
              refine ⟨41668073599199674960020725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27778715732799783306680483 41668073599199674960020725)
              ·
                refine ⟨3906381899924969527501943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41668073599199674960020725 3906381899924969527501943)
                ·
                  refine ⟨5859572849887454291252915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3906381899924969527501943 5859572849887454291252915)
                  ·
                    refine ⟨8789359274831181436879373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5859572849887454291252915 8789359274831181436879373)
                    ·
                      refine ⟨3296009728061693038829765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8789359274831181436879373 3296009728061693038829765)
                      ·
                        rfl

theorem cell23_6418956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_6418956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418956 prefixEnd_6418956 := by exact prefixLift 6418956
  have htrace : WordTrace (prefixWord ++ tailWord_6418956) baseStart_6418956 baseEnd_6418956 := by
    simpa [prefixWord, tailWord_6418956, baseEnd_6418956] using wordTrace_append hprefix tailTrace_6418956
  have hstable : (prefixWord ++ tailWord_6418956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418956).length < 2 ^ (prefixWord ++ tailWord_6418956).sum := by decide
  have hdescent : baseEnd_6418956 < baseStart_6418956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418975 : List Nat := [1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 6]
def baseStart_6418975 : Nat := 118140960795 + 6418975 * 2 ^ 59
def prefixEnd_6418975 : Nat := 4983230072969 + 3 ^ 40 * 6418975 * 2
def baseEnd_6418975 : Nat := 3296019484194128464492177

theorem tailTrace_6418975 : CollatzResearch.WordTrace tailWord_6418975 prefixEnd_6418975 3296019484194128464492177 := by
  unfold tailWord_6418975
  simp only [CollatzResearch.WordTrace]
  refine ⟨234119251920157323496306379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156079501280104882330870919 234119251920157323496306379)
  ·
    refine ⟨351178877880235985244459569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234119251920157323496306379 351178877880235985244459569)
    ·
      refine ⟨263384158410176988933344677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351178877880235985244459569 263384158410176988933344677)
      ·
        refine ⟨49384529701908185425002127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263384158410176988933344677 49384529701908185425002127)
        ·
          refine ⟨74076794552862278137503191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49384529701908185425002127 74076794552862278137503191)
          ·
            refine ⟨111115191829293417206254787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74076794552862278137503191 111115191829293417206254787)
            ·
              refine ⟨166672787743940125809382181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111115191829293417206254787 166672787743940125809382181)
              ·
                refine ⟨31251147701988773589259159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166672787743940125809382181 31251147701988773589259159)
                ·
                  refine ⟨46876721552983160383888739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31251147701988773589259159 46876721552983160383888739)
                  ·
                    refine ⟨70315082329474740575833109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46876721552983160383888739 70315082329474740575833109)
                    ·
                      refine ⟨3296019484194128464492177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70315082329474740575833109 3296019484194128464492177)
                      ·
                        rfl

theorem cell23_6418975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_6418975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418975 prefixEnd_6418975 := by exact prefixLift 6418975
  have htrace : WordTrace (prefixWord ++ tailWord_6418975) baseStart_6418975 baseEnd_6418975 := by
    simpa [prefixWord, tailWord_6418975, baseEnd_6418975] using wordTrace_append hprefix tailTrace_6418975
  have hstable : (prefixWord ++ tailWord_6418975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418975).length < 2 ^ (prefixWord ++ tailWord_6418975).sum := by decide
  have hdescent : baseEnd_6418975 < baseStart_6418975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418992 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 4]
def baseStart_6418992 : Nat := 118140960795 + 6418992 * 2 ^ 59
def prefixEnd_6418992 : Nat := 4983230072969 + 3 ^ 40 * 6418992 * 2
def baseEnd_6418992 : Nat := 3296028213365254897979599

theorem tailTrace_6418992 : CollatzResearch.WordTrace tailWord_6418992 prefixEnd_6418992 3296028213365254897979599 := by
  unfold tailWord_6418992
  simp only [CollatzResearch.WordTrace]
  refine ⟨117059935980547867699837615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156079914640730490266450153 117059935980547867699837615)
  ·
    refine ⟨175589903970821801549756423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117059935980547867699837615 175589903970821801549756423)
    ·
      refine ⟨263384855956232702324634635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175589903970821801549756423 263384855956232702324634635)
      ·
        refine ⟨395077283934349053486951953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263384855956232702324634635 395077283934349053486951953)
        ·
          refine ⟨296307962950761790115213965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395077283934349053486951953 296307962950761790115213965)
          ·
            refine ⟨111115486106535671293205237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296307962950761790115213965 111115486106535671293205237)
            ·
              refine ⟨10417076822487719183737991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111115486106535671293205237 10417076822487719183737991)
              ·
                refine ⟨15625615233731578775606987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10417076822487719183737991 15625615233731578775606987)
                ·
                  refine ⟨23438422850597368163410481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15625615233731578775606987 23438422850597368163410481)
                  ·
                    refine ⟨17578817137948026122557861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23438422850597368163410481 17578817137948026122557861)
                    ·
                      refine ⟨3296028213365254897979599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17578817137948026122557861 3296028213365254897979599)
                      ·
                        rfl

theorem cell23_6418992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 4].length) (baseStart_6418992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418992 prefixEnd_6418992 := by exact prefixLift 6418992
  have htrace : WordTrace (prefixWord ++ tailWord_6418992) baseStart_6418992 baseEnd_6418992 := by
    simpa [prefixWord, tailWord_6418992, baseEnd_6418992] using wordTrace_append hprefix tailTrace_6418992
  have hstable : (prefixWord ++ tailWord_6418992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418992).length < 2 ^ (prefixWord ++ tailWord_6418992).sum := by decide
  have hdescent : baseEnd_6418992 < baseStart_6418992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6418999 : List Nat := [1, 1, 3, 1, 2, 3, 4, 2, 1, 2, 3]
def baseStart_6418999 : Nat := 118140960795 + 6418999 * 2 ^ 59
def prefixEnd_6418999 : Nat := 4983230072969 + 3 ^ 40 * 6418999 * 2
def baseEnd_6418999 : Nat := 3296031807729836370592067

theorem tailTrace_6418999 : CollatzResearch.WordTrace tailWord_6418999 prefixEnd_6418999 3296031807729836370592067 := by
  unfold tailWord_6418999
  simp only [CollatzResearch.WordTrace]
  refine ⟨234120127272070375595180051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156080084848046917063453367 234120127272070375595180051)
  ·
    refine ⟨351180190908105563392770077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234120127272070375595180051 351180190908105563392770077)
    ·
      refine ⟨131692571590539586272288779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351180190908105563392770077 131692571590539586272288779)
      ·
        refine ⟨197538857385809379408433169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131692571590539586272288779 197538857385809379408433169)
        ·
          refine ⟨148154143039357034556324877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197538857385809379408433169 148154143039357034556324877)
          ·
            refine ⟨55557803639758887958621829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148154143039357034556324877 55557803639758887958621829)
            ·
              refine ⟨10417088182454791492241593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55557803639758887958621829 10417088182454791492241593)
              ·
                refine ⟨7812816136841093619181195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10417088182454791492241593 7812816136841093619181195)
                ·
                  refine ⟨11719224205261640428771793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7812816136841093619181195 11719224205261640428771793)
                  ·
                    refine ⟨8789418153946230321578845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11719224205261640428771793 8789418153946230321578845)
                    ·
                      refine ⟨3296031807729836370592067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8789418153946230321578845 3296031807729836370592067)
                      ·
                        rfl

theorem cell23_6418999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 1, 2, 3].length) (baseStart_6418999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6418999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6418999 prefixEnd_6418999 := by exact prefixLift 6418999
  have htrace : WordTrace (prefixWord ++ tailWord_6418999) baseStart_6418999 baseEnd_6418999 := by
    simpa [prefixWord, tailWord_6418999, baseEnd_6418999] using wordTrace_append hprefix tailTrace_6418999
  have hstable : (prefixWord ++ tailWord_6418999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6418999).length < 2 ^ (prefixWord ++ tailWord_6418999).sum := by decide
  have hdescent : baseEnd_6418999 < baseStart_6418999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6418999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419002 : List Nat := [3, 1, 1, 1, 3, 3, 4, 7]
def baseStart_6419002 : Nat := 118140960795 + 6419002 * 2 ^ 59
def prefixEnd_6419002 : Nat := 4983230072969 + 3 ^ 40 * 6419002 * 2
def baseEnd_6419002 : Nat := 122075309191548142920539

theorem tailTrace_6419002 : CollatzResearch.WordTrace tailWord_6419002 prefixEnd_6419002 122075309191548142920539 := by
  unfold tailWord_6419002
  simp only [CollatzResearch.WordTrace]
  refine ⟨58530059172764876776884815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156080157794039671405026173 58530059172764876776884815)
  ·
    refine ⟨87795088759147315165327223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58530059172764876776884815 87795088759147315165327223)
    ·
      refine ⟨131692633138720972747990835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87795088759147315165327223 131692633138720972747990835)
      ·
        refine ⟨197538949708081459121986253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131692633138720972747990835 197538949708081459121986253)
        ·
          refine ⟨74077106140530547170744845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197538949708081459121986253 74077106140530547170744845)
          ·
            refine ⟨27778914802698955189029317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74077106140530547170744845 27778914802698955189029317)
            ·
              refine ⟨5208546525506054097942997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27778914802698955189029317 5208546525506054097942997)
              ·
                refine ⟨122075309191548142920539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5208546525506054097942997 122075309191548142920539)
                ·
                  rfl

theorem cell23_6419002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 4, 7].length) (baseStart_6419002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419002 prefixEnd_6419002 := by exact prefixLift 6419002
  have htrace : WordTrace (prefixWord ++ tailWord_6419002) baseStart_6419002 baseEnd_6419002 := by
    simpa [prefixWord, tailWord_6419002, baseEnd_6419002] using wordTrace_append hprefix tailTrace_6419002
  have hstable : (prefixWord ++ tailWord_6419002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419002).length < 2 ^ (prefixWord ++ tailWord_6419002).sum := by decide
  have hdescent : baseEnd_6419002 < baseStart_6419002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419013 : List Nat := [1, 3, 1, 1, 1, 5, 3, 3, 1, 2, 2]
def baseStart_6419013 : Nat := 118140960795 + 6419013 * 2 ^ 59
def prefixEnd_6419013 : Nat := 4983230072969 + 3 ^ 40 * 6419013 * 2
def baseEnd_6419013 : Nat := 3296038996458999315817003

theorem tailTrace_6419013 : CollatzResearch.WordTrace tailWord_6419013 prefixEnd_6419013 3296038996458999315817003 := by
  unfold tailWord_6419013
  simp only [CollatzResearch.WordTrace]
  refine ⟨234120637894019655986189693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156080425262679770657459795 234120637894019655986189693)
  ·
    refine ⟨87795239210257370994821135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234120637894019655986189693 87795239210257370994821135)
    ·
      refine ⟨131692858815386056492231703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87795239210257370994821135 131692858815386056492231703)
      ·
        refine ⟨197539288223079084738347555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131692858815386056492231703 197539288223079084738347555)
        ·
          refine ⟨296308932334618627107521333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197539288223079084738347555 296308932334618627107521333)
          ·
            refine ⟨27778962406370496291330125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 296308932334618627107521333 27778962406370496291330125)
            ·
              refine ⟨10417110902388936109248797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27778962406370496291330125 10417110902388936109248797)
              ·
                refine ⟨3906416588395851040968299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10417110902388936109248797 3906416588395851040968299)
                ·
                  refine ⟨5859624882593776561452449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3906416588395851040968299 5859624882593776561452449)
                  ·
                    refine ⟨4394718661945332421089337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5859624882593776561452449 4394718661945332421089337)
                    ·
                      refine ⟨3296038996458999315817003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4394718661945332421089337 3296038996458999315817003)
                      ·
                        rfl

theorem cell23_6419013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 1, 2, 2].length) (baseStart_6419013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419013 prefixEnd_6419013 := by exact prefixLift 6419013
  have htrace : WordTrace (prefixWord ++ tailWord_6419013) baseStart_6419013 baseEnd_6419013 := by
    simpa [prefixWord, tailWord_6419013, baseEnd_6419013] using wordTrace_append hprefix tailTrace_6419013
  have hstable : (prefixWord ++ tailWord_6419013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419013).length < 2 ^ (prefixWord ++ tailWord_6419013).sum := by decide
  have hdescent : baseEnd_6419013 < baseStart_6419013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419029 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 4, 1, 3]
def baseStart_6419029 : Nat := 118140960795 + 6419029 * 2 ^ 59
def prefixEnd_6419029 : Nat := 4983230072969 + 3 ^ 40 * 6419029 * 2
def baseEnd_6419029 : Nat := 3296047212149471253216929

theorem tailTrace_6419029 : CollatzResearch.WordTrace tailWord_6419029 prefixEnd_6419029 3296047212149471253216929 := by
  unfold tailWord_6419029
  simp only [CollatzResearch.WordTrace]
  refine ⟨234121221461961690718772141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156080814307974460479181427 234121221461961690718772141)
  ·
    refine ⟨87795458048235634019539553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234121221461961690718772141 87795458048235634019539553)
    ·
      refine ⟨65846593536176725514654665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87795458048235634019539553 65846593536176725514654665)
      ·
        refine ⟨49384945152132544135990999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65846593536176725514654665 49384945152132544135990999)
        ·
          refine ⟨74077417728198816203986499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49384945152132544135990999 74077417728198816203986499)
          ·
            refine ⟨111116126592298224305979749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74077417728198816203986499 111116126592298224305979749)
            ·
              refine ⟨20834273736055917057371203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111116126592298224305979749 20834273736055917057371203)
              ·
                refine ⟨31251410604083875586056805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20834273736055917057371203 31251410604083875586056805)
                ·
                  refine ⟨5859639488265726672385651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31251410604083875586056805 5859639488265726672385651)
                  ·
                    refine ⟨8789459232398590008578477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5859639488265726672385651 8789459232398590008578477)
                    ·
                      refine ⟨3296047212149471253216929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8789459232398590008578477 3296047212149471253216929)
                      ·
                        rfl

theorem cell23_6419029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 4, 1, 3].length) (baseStart_6419029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419029 prefixEnd_6419029 := by exact prefixLift 6419029
  have htrace : WordTrace (prefixWord ++ tailWord_6419029) baseStart_6419029 baseEnd_6419029 := by
    simpa [prefixWord, tailWord_6419029, baseEnd_6419029] using wordTrace_append hprefix tailTrace_6419029
  have hstable : (prefixWord ++ tailWord_6419029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419029).length < 2 ^ (prefixWord ++ tailWord_6419029).sum := by decide
  have hdescent : baseEnd_6419029 < baseStart_6419029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419056 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 3, 3, 2]
def baseStart_6419056 : Nat := 118140960795 + 6419056 * 2 ^ 59
def prefixEnd_6419056 : Nat := 4983230072969 + 3 ^ 40 * 6419056 * 2
def baseEnd_6419056 : Nat := 3296061076127142647579305

theorem tailTrace_6419056 : CollatzResearch.WordTrace tailWord_6419056 prefixEnd_6419056 3296061076127142647579305 := by
  unfold tailWord_6419056
  simp only [CollatzResearch.WordTrace]
  refine ⟨117061103116431937165002511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156081470821909249553336681 117061103116431937165002511)
  ·
    refine ⟨175591654674647905747503767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117061103116431937165002511 175591654674647905747503767)
    ·
      refine ⟨263387482011971858621255651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175591654674647905747503767 263387482011971858621255651)
      ·
        refine ⟨395081223017957787931883477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263387482011971858621255651 395081223017957787931883477)
        ·
          refine ⟨9259716164483385654653519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 395081223017957787931883477 9259716164483385654653519)
          ·
            refine ⟨13889574246725078481980279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9259716164483385654653519 13889574246725078481980279)
            ·
              refine ⟨20834361370087617722970419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13889574246725078481980279 20834361370087617722970419)
              ·
                refine ⟨31251542055131426584455629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20834361370087617722970419 31251542055131426584455629)
                ·
                  refine ⟨11719328270674284969170861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31251542055131426584455629 11719328270674284969170861)
                  ·
                    refine ⟨4394748101502856863439073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11719328270674284969170861 4394748101502856863439073)
                    ·
                      refine ⟨3296061076127142647579305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4394748101502856863439073 3296061076127142647579305)
                      ·
                        rfl

theorem cell23_6419056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 3, 3, 2].length) (baseStart_6419056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419056 prefixEnd_6419056 := by exact prefixLift 6419056
  have htrace : WordTrace (prefixWord ++ tailWord_6419056) baseStart_6419056 baseEnd_6419056 := by
    simpa [prefixWord, tailWord_6419056, baseEnd_6419056] using wordTrace_append hprefix tailTrace_6419056
  have hstable : (prefixWord ++ tailWord_6419056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419056).length < 2 ^ (prefixWord ++ tailWord_6419056).sum := by decide
  have hdescent : baseEnd_6419056 < baseStart_6419056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419072 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 5]
def baseStart_6419072 : Nat := 118140960795 + 6419072 * 2 ^ 59
def prefixEnd_6419072 : Nat := 4983230072969 + 3 ^ 40 * 6419072 * 2
def baseEnd_6419072 : Nat := 3296069291817614584979231

theorem tailTrace_6419072 : CollatzResearch.WordTrace tailWord_6419072 prefixEnd_6419072 3296069291817614584979231 := by
  unfold tailWord_6419072
  simp only [CollatzResearch.WordTrace]
  refine ⟨117061394900402954531293735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156081859867203939375058313 117061394900402954531293735)
  ·
    refine ⟨175592092350604431796940603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117061394900402954531293735 175592092350604431796940603)
    ·
      refine ⟨263388138525906647695410905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175592092350604431796940603 263388138525906647695410905)
      ·
        refine ⟨197541103894429985771558179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263388138525906647695410905 197541103894429985771558179)
        ·
          refine ⟨296311655841644978657337269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197541103894429985771558179 296311655841644978657337269)
          ·
            refine ⟨27779217735154216749125369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 296311655841644978657337269 27779217735154216749125369)
            ·
              refine ⟨20834413301365662561844027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27779217735154216749125369 20834413301365662561844027)
              ·
                refine ⟨31251619952048493842766041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20834413301365662561844027 31251619952048493842766041)
                ·
                  refine ⟨23438714964036370382074531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31251619952048493842766041 23438714964036370382074531)
                  ·
                    refine ⟨35158072446054555573111797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23438714964036370382074531 35158072446054555573111797)
                    ·
                      refine ⟨3296069291817614584979231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35158072446054555573111797 3296069291817614584979231)
                      ·
                        rfl

theorem cell23_6419072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 5].length) (baseStart_6419072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419072 prefixEnd_6419072 := by exact prefixLift 6419072
  have htrace : WordTrace (prefixWord ++ tailWord_6419072) baseStart_6419072 baseEnd_6419072 := by
    simpa [prefixWord, tailWord_6419072, baseEnd_6419072] using wordTrace_append hprefix tailTrace_6419072
  have hstable : (prefixWord ++ tailWord_6419072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419072).length < 2 ^ (prefixWord ++ tailWord_6419072).sum := by decide
  have hdescent : baseEnd_6419072 < baseStart_6419072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419073 : List Nat := [1, 2, 4, 2, 1, 1, 5, 1, 1, 3, 2]
def baseStart_6419073 : Nat := 118140960795 + 6419073 * 2 ^ 59
def prefixEnd_6419073 : Nat := 4983230072969 + 3 ^ 40 * 6419073 * 2
def baseEnd_6419073 : Nat := 3296069805298269081066727

theorem tailTrace_6419073 : CollatzResearch.WordTrace tailWord_6419073 prefixEnd_6419073 3296069805298269081066727 := by
  unfold tailWord_6419073
  simp only [CollatzResearch.WordTrace]
  refine ⟨234122826273802286233373873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156081884182534857488915915 234122826273802286233373873)
  ·
    refine ⟨175592119705351714675030405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234122826273802286233373873 175592119705351714675030405)
    ·
      refine ⟨32923522444753446501568201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175592119705351714675030405 32923522444753446501568201)
      ·
        refine ⟨24692641833565084876176151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32923522444753446501568201 24692641833565084876176151)
        ·
          refine ⟨37038962750347627314264227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24692641833565084876176151 37038962750347627314264227)
          ·
            refine ⟨55558444125521440971396341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37038962750347627314264227 55558444125521440971396341)
            ·
              refine ⟨5208604136767635091068407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55558444125521440971396341 5208604136767635091068407)
              ·
                refine ⟨7812906205151452636602611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5208604136767635091068407 7812906205151452636602611)
                ·
                  refine ⟨11719359307727178954903917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7812906205151452636602611 11719359307727178954903917)
                  ·
                    refine ⟨4394759740397692108088969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11719359307727178954903917 4394759740397692108088969)
                    ·
                      refine ⟨3296069805298269081066727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4394759740397692108088969 3296069805298269081066727)
                      ·
                        rfl

theorem cell23_6419073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_6419073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419073 prefixEnd_6419073 := by exact prefixLift 6419073
  have htrace : WordTrace (prefixWord ++ tailWord_6419073) baseStart_6419073 baseEnd_6419073 := by
    simpa [prefixWord, tailWord_6419073, baseEnd_6419073] using wordTrace_append hprefix tailTrace_6419073
  have hstable : (prefixWord ++ tailWord_6419073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419073).length < 2 ^ (prefixWord ++ tailWord_6419073).sum := by decide
  have hdescent : baseEnd_6419073 < baseStart_6419073 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419179 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 3]
def baseStart_6419179 : Nat := 118140960795 + 6419179 * 2 ^ 59
def prefixEnd_6419179 : Nat := 4983230072969 + 3 ^ 40 * 6419179 * 2
def baseEnd_6419179 : Nat := 3296124234247645666341239

theorem tailTrace_6419179 : CollatzResearch.WordTrace tailWord_6419179 prefixEnd_6419179 3296124234247645666341239 := by
  unfold tailWord_6419179
  simp only [CollatzResearch.WordTrace]
  refine ⟨234126692411418266336732591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156084461607612177557821727 234126692411418266336732591)
  ·
    refine ⟨351190038617127399505098887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234126692411418266336732591 351190038617127399505098887)
    ·
      refine ⟨526785057925691099257648331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351190038617127399505098887 526785057925691099257648331)
      ·
        refine ⟨790177586888536648886472497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526785057925691099257648331 790177586888536648886472497)
        ·
          refine ⟨592633190166402486664854373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 790177586888536648886472497 592633190166402486664854373)
          ·
            refine ⟨111118723156200466249660195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 592633190166402486664854373 111118723156200466249660195)
            ·
              refine ⟨166678084734300699374490293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111118723156200466249660195 166678084734300699374490293)
              ·
                refine ⟨15626070443840690566358465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166678084734300699374490293 15626070443840690566358465)
                ·
                  refine ⟨11719552832880517924768849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15626070443840690566358465 11719552832880517924768849)
                  ·
                    refine ⟨8789664624660388443576637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11719552832880517924768849 8789664624660388443576637)
                    ·
                      refine ⟨3296124234247645666341239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8789664624660388443576637 3296124234247645666341239)
                      ·
                        rfl

theorem cell23_6419179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 3].length) (baseStart_6419179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419179 prefixEnd_6419179 := by exact prefixLift 6419179
  have htrace : WordTrace (prefixWord ++ tailWord_6419179) baseStart_6419179 baseEnd_6419179 := by
    simpa [prefixWord, tailWord_6419179, baseEnd_6419179] using wordTrace_append hprefix tailTrace_6419179
  have hstable : (prefixWord ++ tailWord_6419179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419179).length < 2 ^ (prefixWord ++ tailWord_6419179).sum := by decide
  have hdescent : baseEnd_6419179 < baseStart_6419179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419196 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 2, 2, 3]
def baseStart_6419196 : Nat := 118140960795 + 6419196 * 2 ^ 59
def prefixEnd_6419196 : Nat := 4983230072969 + 3 ^ 40 * 6419196 * 2
def baseEnd_6419196 : Nat := 3296132963418772099828661

theorem tailTrace_6419196 : CollatzResearch.WordTrace tailWord_6419196 prefixEnd_6419196 3296132963418772099828661 := by
  unfold tailWord_6419196
  simp only [CollatzResearch.WordTrace]
  refine ⟨117063656226178339120050721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156084874968237785493400961 117063656226178339120050721)
  ·
    refine ⟨87797742169633754340038041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117063656226178339120050721 87797742169633754340038041)
    ·
      refine ⟨65848306627225315755028531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87797742169633754340038041 65848306627225315755028531)
      ·
        refine ⟨98772459940837973632542797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65848306627225315755028531 98772459940837973632542797)
        ·
          refine ⟨37039672477814240112203549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98772459940837973632542797 37039672477814240112203549)
          ·
            refine ⟨13889877179180340042076331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37039672477814240112203549 13889877179180340042076331)
            ·
              refine ⟨20834815768770510063114497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13889877179180340042076331 20834815768770510063114497)
              ·
                refine ⟨15626111826577882547335873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20834815768770510063114497 15626111826577882547335873)
                ·
                  refine ⟨11719583869933411910501905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15626111826577882547335873 11719583869933411910501905)
                  ·
                    refine ⟨8789687902450058932876429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11719583869933411910501905 8789687902450058932876429)
                    ·
                      refine ⟨3296132963418772099828661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8789687902450058932876429 3296132963418772099828661)
                      ·
                        rfl

theorem cell23_6419196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_6419196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419196 prefixEnd_6419196 := by exact prefixLift 6419196
  have htrace : WordTrace (prefixWord ++ tailWord_6419196) baseStart_6419196 baseEnd_6419196 := by
    simpa [prefixWord, tailWord_6419196, baseEnd_6419196] using wordTrace_append hprefix tailTrace_6419196
  have hstable : (prefixWord ++ tailWord_6419196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419196).length < 2 ^ (prefixWord ++ tailWord_6419196).sum := by decide
  have hdescent : baseEnd_6419196 < baseStart_6419196 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419212 : List Nat := [2, 2, 1, 2, 2, 1, 1, 1, 2, 9]
def baseStart_6419212 : Nat := 118140960795 + 6419212 * 2 ^ 59
def prefixEnd_6419212 : Nat := 4983230072969 + 3 ^ 40 * 6419212 * 2
def baseEnd_6419212 : Nat := 1098713726369748012409529

theorem tailTrace_6419212 : CollatzResearch.WordTrace tailWord_6419212 prefixEnd_6419212 1098713726369748012409529 := by
  unfold tailWord_6419212
  simp only [CollatzResearch.WordTrace]
  refine ⟨117063948010149356486341945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156085264013532475315122593 117063948010149356486341945)
  ·
    refine ⟨87797961007612017364756459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117063948010149356486341945 87797961007612017364756459)
    ·
      refine ⟨131696941511418026047134689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87797961007612017364756459 131696941511418026047134689)
      ·
        refine ⟨98772706133563519535351017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131696941511418026047134689 98772706133563519535351017)
        ·
          refine ⟨74079529600172639651513263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98772706133563519535351017 74079529600172639651513263)
          ·
            refine ⟨111119294400258959477269895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74079529600172639651513263 111119294400258959477269895)
            ·
              refine ⟨166678941600388439215904843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111119294400258959477269895 166678941600388439215904843)
              ·
                refine ⟨250018412400582658823857265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166678941600388439215904843 250018412400582658823857265)
                ·
                  refine ⟨187513809300436994117892949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250018412400582658823857265 187513809300436994117892949)
                  ·
                    refine ⟨1098713726369748012409529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 187513809300436994117892949 1098713726369748012409529)
                    ·
                      rfl

theorem cell23_6419212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 1, 2, 9].length) (baseStart_6419212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419212 prefixEnd_6419212 := by exact prefixLift 6419212
  have htrace : WordTrace (prefixWord ++ tailWord_6419212) baseStart_6419212 baseEnd_6419212 := by
    simpa [prefixWord, tailWord_6419212, baseEnd_6419212] using wordTrace_append hprefix tailTrace_6419212
  have hstable : (prefixWord ++ tailWord_6419212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419212).length < 2 ^ (prefixWord ++ tailWord_6419212).sum := by decide
  have hdescent : baseEnd_6419212 < baseStart_6419212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419226 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3]
def baseStart_6419226 : Nat := 118140960795 + 6419226 * 2 ^ 59
def prefixEnd_6419226 : Nat := 4983230072969 + 3 ^ 40 * 6419226 * 2
def baseEnd_6419226 : Nat := 3296148367838406982453523

theorem tailTrace_6419226 : CollatzResearch.WordTrace tailWord_6419226 prefixEnd_6419226 3296148367838406982453523 := by
  unfold tailWord_6419226
  simp only [CollatzResearch.WordTrace]
  refine ⟨58532101660561998340923383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156085604428165328909129021 58532101660561998340923383)
  ·
    refine ⟨87798152490842997511385075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58532101660561998340923383 87798152490842997511385075)
    ·
      refine ⟨131697228736264496267077613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87798152490842997511385075 131697228736264496267077613)
      ·
        refine ⟨49386460776099186100154105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131697228736264496267077613 49386460776099186100154105)
        ·
          refine ⟨37039845582074389575115579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49386460776099186100154105 37039845582074389575115579)
          ·
            refine ⟨55559768373111584362673369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37039845582074389575115579 55559768373111584362673369)
            ·
              refine ⟨41669826279833688272005027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55559768373111584362673369 41669826279833688272005027)
              ·
                refine ⟨62504739419750532408007541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41669826279833688272005027 62504739419750532408007541)
                ·
                  refine ⟨5859819320601612413250707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62504739419750532408007541 5859819320601612413250707)
                  ·
                    refine ⟨8789728980902418619876061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5859819320601612413250707 8789728980902418619876061)
                    ·
                      refine ⟨3296148367838406982453523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8789728980902418619876061 3296148367838406982453523)
                      ·
                        rfl

theorem cell23_6419226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_6419226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419226 prefixEnd_6419226 := by exact prefixLift 6419226
  have htrace : WordTrace (prefixWord ++ tailWord_6419226) baseStart_6419226 baseEnd_6419226 := by
    simpa [prefixWord, tailWord_6419226, baseEnd_6419226] using wordTrace_append hprefix tailTrace_6419226
  have hstable : (prefixWord ++ tailWord_6419226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419226).length < 2 ^ (prefixWord ++ tailWord_6419226).sum := by decide
  have hdescent : baseEnd_6419226 < baseStart_6419226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419253 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 2, 3, 2]
def baseStart_6419253 : Nat := 118140960795 + 6419253 * 2 ^ 59
def prefixEnd_6419253 : Nat := 4983230072969 + 3 ^ 40 * 6419253 * 2
def baseEnd_6419253 : Nat := 3296162231816078376815899

theorem tailTrace_6419253 : CollatzResearch.WordTrace tailWord_6419253 prefixEnd_6419253 3296162231816078376815899 := by
  unfold tailWord_6419253
  simp only [CollatzResearch.WordTrace]
  refine ⟨234129391413150176974926413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156086260942100117983284275 234129391413150176974926413)
  ·
    refine ⟨87798521779931316365597405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234129391413150176974926413 87798521779931316365597405)
    ·
      refine ⟨32924445667474243637099027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87798521779931316365597405 32924445667474243637099027)
      ·
        refine ⟨49386668501211365455648541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32924445667474243637099027 49386668501211365455648541)
        ·
          refine ⟨18520000687954262045868203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49386668501211365455648541 18520000687954262045868203)
          ·
            refine ⟨27780001031931393068802305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18520000687954262045868203 27780001031931393068802305)
            ·
              refine ⟨20835000773948544801601729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27780001031931393068802305 20835000773948544801601729)
              ·
                refine ⟨15626250580461408601201297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20835000773948544801601729 15626250580461408601201297)
                ·
                  refine ⟨11719687935346056450900973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15626250580461408601201297 11719687935346056450900973)
                  ·
                    refine ⟨4394882975754771169087865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11719687935346056450900973 4394882975754771169087865)
                    ·
                      refine ⟨3296162231816078376815899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4394882975754771169087865 3296162231816078376815899)
                      ·
                        rfl

theorem cell23_6419253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_6419253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419253 prefixEnd_6419253 := by exact prefixLift 6419253
  have htrace : WordTrace (prefixWord ++ tailWord_6419253) baseStart_6419253 baseEnd_6419253 := by
    simpa [prefixWord, tailWord_6419253, baseEnd_6419253] using wordTrace_append hprefix tailTrace_6419253
  have hstable : (prefixWord ++ tailWord_6419253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419253).length < 2 ^ (prefixWord ++ tailWord_6419253).sum := by decide
  have hdescent : baseEnd_6419253 < baseStart_6419253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419254 : List Nat := [5, 1, 2, 2, 2, 2, 2, 2, 1, 4]
def baseStart_6419254 : Nat := 118140960795 + 6419254 * 2 ^ 59
def prefixEnd_6419254 : Nat := 4983230072969 + 3 ^ 40 * 6419254 * 2
def baseEnd_6419254 : Nat := 1098720915098910957634465

theorem tailTrace_6419254 : CollatzResearch.WordTrace tailWord_6419254 prefixEnd_6419254 1098720915098910957634465 := by
  unfold tailWord_6419254
  simp only [CollatzResearch.WordTrace]
  refine ⟨14633089242884159634107051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156086285257431036097141877 14633089242884159634107051)
  ·
    refine ⟨21949633864326239451160577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14633089242884159634107051 21949633864326239451160577)
    ·
      refine ⟨16462225398244679588370433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21949633864326239451160577 16462225398244679588370433)
      ·
        refine ⟨12346669048683509691277825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16462225398244679588370433 12346669048683509691277825)
        ·
          refine ⟨9260001786512632268458369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12346669048683509691277825 9260001786512632268458369)
          ·
            refine ⟨6945001339884474201343777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9260001786512632268458369 6945001339884474201343777)
            ·
              refine ⟨5208751004913355651007833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6945001339884474201343777 5208751004913355651007833)
              ·
                refine ⟨3906563253685016738255875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5208751004913355651007833 3906563253685016738255875)
                ·
                  refine ⟨5859844880527525107383813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3906563253685016738255875 5859844880527525107383813)
                  ·
                    refine ⟨1098720915098910957634465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5859844880527525107383813 1098720915098910957634465)
                    ·
                      rfl

theorem cell23_6419254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 2, 1, 4].length) (baseStart_6419254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419254 prefixEnd_6419254 := by exact prefixLift 6419254
  have htrace : WordTrace (prefixWord ++ tailWord_6419254) baseStart_6419254 baseEnd_6419254 := by
    simpa [prefixWord, tailWord_6419254, baseEnd_6419254] using wordTrace_append hprefix tailTrace_6419254
  have hstable : (prefixWord ++ tailWord_6419254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419254).length < 2 ^ (prefixWord ++ tailWord_6419254).sum := by decide
  have hdescent : baseEnd_6419254 < baseStart_6419254 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419276 : List Nat := [2, 2, 1, 3, 3, 2, 2, 1, 1, 6]
def baseStart_6419276 : Nat := 118140960795 + 6419276 * 2 ^ 59
def prefixEnd_6419276 : Nat := 4983230072969 + 3 ^ 40 * 6419276 * 2
def baseEnd_6419276 : Nat := 1098724680623710595609431

theorem tailTrace_6419276 : CollatzResearch.WordTrace tailWord_6419276 prefixEnd_6419276 1098724680623710595609431 := by
  unfold tailWord_6419276
  simp only [CollatzResearch.WordTrace]
  refine ⟨117065115146033425951506841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156086820194711234602009121 117065115146033425951506841)
  ·
    refine ⟨87798836359525069463630131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117065115146033425951506841 87798836359525069463630131)
    ·
      refine ⟨131698254539287604195445197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87798836359525069463630131 131698254539287604195445197)
      ·
        refine ⟨49386845452232851573291949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131698254539287604195445197 49386845452232851573291949)
        ·
          refine ⟨18520067044587319339984481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49386845452232851573291949 18520067044587319339984481)
          ·
            refine ⟨13890050283440489504988361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18520067044587319339984481 13890050283440489504988361)
            ·
              refine ⟨10417537712580367128741271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13890050283440489504988361 10417537712580367128741271)
              ·
                refine ⟨15626306568870550693111907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10417537712580367128741271 15626306568870550693111907)
                ·
                  refine ⟨23439459853305826039667861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15626306568870550693111907 23439459853305826039667861)
                  ·
                    refine ⟨1098724680623710595609431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23439459853305826039667861 1098724680623710595609431)
                    ·
                      rfl

theorem cell23_6419276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_6419276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419276 prefixEnd_6419276 := by exact prefixLift 6419276
  have htrace : WordTrace (prefixWord ++ tailWord_6419276) baseStart_6419276 baseEnd_6419276 := by
    simpa [prefixWord, tailWord_6419276, baseEnd_6419276] using wordTrace_append hprefix tailTrace_6419276
  have hstable : (prefixWord ++ tailWord_6419276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419276).length < 2 ^ (prefixWord ++ tailWord_6419276).sum := by decide
  have hdescent : baseEnd_6419276 < baseStart_6419276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419300 : List Nat := [2, 3, 1, 1, 4, 3, 2, 1, 1, 1, 4]
def baseStart_6419300 : Nat := 118140960795 + 6419300 * 2 ^ 59
def prefixEnd_6419300 : Nat := 4983230072969 + 3 ^ 40 * 6419300 * 2
def baseEnd_6419300 : Nat := 3296186365406839692928183

theorem tailTrace_6419300 : CollatzResearch.WordTrace tailWord_6419300 prefixEnd_6419300 3296186365406839692928183 := by
  unfold tailWord_6419300
  simp only [CollatzResearch.WordTrace]
  refine ⟨117065552821989952000943677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156087403762653269334591569 117065552821989952000943677)
  ·
    refine ⟨43899582308246232000353879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117065552821989952000943677 43899582308246232000353879)
    ·
      refine ⟨65849373462369348000530819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43899582308246232000353879 65849373462369348000530819)
      ·
        refine ⟨98774060193554022000796229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65849373462369348000530819 98774060193554022000796229)
        ·
          refine ⟨18520136286291379125149293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98774060193554022000796229 18520136286291379125149293)
          ·
            refine ⟨6945051107359267171930985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18520136286291379125149293 6945051107359267171930985)
            ·
              refine ⟨5208788330519450378948239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6945051107359267171930985 5208788330519450378948239)
              ·
                refine ⟨7813182495779175568422359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5208788330519450378948239 7813182495779175568422359)
                ·
                  refine ⟨11719773743668763352633539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7813182495779175568422359 11719773743668763352633539)
                  ·
                    refine ⟨17579660615503145028950309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11719773743668763352633539 17579660615503145028950309)
                    ·
                      refine ⟨3296186365406839692928183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17579660615503145028950309 3296186365406839692928183)
                      ·
                        rfl

theorem cell23_6419300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 2, 1, 1, 1, 4].length) (baseStart_6419300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419300 prefixEnd_6419300 := by exact prefixLift 6419300
  have htrace : WordTrace (prefixWord ++ tailWord_6419300) baseStart_6419300 baseEnd_6419300 := by
    simpa [prefixWord, tailWord_6419300, baseEnd_6419300] using wordTrace_append hprefix tailTrace_6419300
  have hstable : (prefixWord ++ tailWord_6419300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419300).length < 2 ^ (prefixWord ++ tailWord_6419300).sum := by decide
  have hdescent : baseEnd_6419300 < baseStart_6419300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419303 : List Nat := [1, 1, 5, 1, 2, 3, 1, 3, 1, 2, 3]
def baseStart_6419303 : Nat := 118140960795 + 6419303 * 2 ^ 59
def prefixEnd_6419303 : Nat := 4983230072969 + 3 ^ 40 * 6419303 * 2
def baseEnd_6419303 : Nat := 3296187905848803181190669

theorem tailTrace_6419303 : CollatzResearch.WordTrace tailWord_6419303 prefixEnd_6419303 3296187905848803181190669 := by
  unfold tailWord_6419303
  simp only [CollatzResearch.WordTrace]
  refine ⟨234131215062969035514246563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156087476708646023676164375 234131215062969035514246563)
  ·
    refine ⟨351196822594453553271369845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234131215062969035514246563 351196822594453553271369845)
    ·
      refine ⟨32924702118230020619190923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 351196822594453553271369845 32924702118230020619190923)
      ·
        refine ⟨49387053177345030928786385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32924702118230020619190923 49387053177345030928786385)
        ·
          refine ⟨37040289883008773196589789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49387053177345030928786385 37040289883008773196589789)
          ·
            refine ⟨13890108706128289948721171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37040289883008773196589789 13890108706128289948721171)
            ·
              refine ⟨20835163059192434923081757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13890108706128289948721171 20835163059192434923081757)
              ·
                refine ⟨7813186147197163096155659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20835163059192434923081757 7813186147197163096155659)
                ·
                  refine ⟨11719779220795744644233489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7813186147197163096155659 11719779220795744644233489)
                  ·
                    refine ⟨8789834415596808483175117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11719779220795744644233489 8789834415596808483175117)
                    ·
                      refine ⟨3296187905848803181190669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8789834415596808483175117 3296187905848803181190669)
                      ·
                        rfl

theorem cell23_6419303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 1, 2, 3].length) (baseStart_6419303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419303 prefixEnd_6419303 := by exact prefixLift 6419303
  have htrace : WordTrace (prefixWord ++ tailWord_6419303) baseStart_6419303 baseEnd_6419303 := by
    simpa [prefixWord, tailWord_6419303, baseEnd_6419303] using wordTrace_append hprefix tailTrace_6419303
  have hstable : (prefixWord ++ tailWord_6419303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419303).length < 2 ^ (prefixWord ++ tailWord_6419303).sum := by decide
  have hdescent : baseEnd_6419303 < baseStart_6419303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419309 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_6419309 : Nat := 118140960795 + 6419309 * 2 ^ 59
def prefixEnd_6419309 : Nat := 4983230072969 + 3 ^ 40 * 6419309 * 2
def baseEnd_6419309 : Nat := 3296190986732730157715641

theorem tailTrace_6419309 : CollatzResearch.WordTrace tailWord_6419309 prefixEnd_6419309 3296190986732730157715641 := by
  unfold tailWord_6419309
  simp only [CollatzResearch.WordTrace]
  refine ⟨234131433900947298538964981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156087622600631532359309987 234131433900947298538964981)
  ·
    refine ⟨21949821928213809238027967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234131433900947298538964981 21949821928213809238027967)
    ·
      refine ⟨32924732892320713857041951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21949821928213809238027967 32924732892320713857041951)
      ·
        refine ⟨49387099338481070785562927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32924732892320713857041951 49387099338481070785562927)
        ·
          refine ⟨74080649007721606178344391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49387099338481070785562927 74080649007721606178344391)
          ·
            refine ⟨111120973511582409267516587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74080649007721606178344391 111120973511582409267516587)
            ·
              refine ⟨166681460267373613901274881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111120973511582409267516587 166681460267373613901274881)
              ·
                refine ⟨125011095200530210425956161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166681460267373613901274881 125011095200530210425956161)
                ·
                  refine ⟨93758321400397657819467121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125011095200530210425956161 93758321400397657819467121)
                  ·
                    refine ⟨70318741050298243364600341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93758321400397657819467121 70318741050298243364600341)
                    ·
                      refine ⟨3296190986732730157715641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70318741050298243364600341 3296190986732730157715641)
                      ·
                        rfl

theorem cell23_6419309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_6419309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419309 prefixEnd_6419309 := by exact prefixLift 6419309
  have htrace : WordTrace (prefixWord ++ tailWord_6419309) baseStart_6419309 baseEnd_6419309 := by
    simpa [prefixWord, tailWord_6419309, baseEnd_6419309] using wordTrace_append hprefix tailTrace_6419309
  have hstable : (prefixWord ++ tailWord_6419309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419309).length < 2 ^ (prefixWord ++ tailWord_6419309).sum := by decide
  have hdescent : baseEnd_6419309 < baseStart_6419309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419317 : List Nat := [1, 3, 4, 1, 1, 2, 2, 4, 1, 2, 2]
def baseStart_6419317 : Nat := 118140960795 + 6419317 * 2 ^ 59
def prefixEnd_6419317 : Nat := 4983230072969 + 3 ^ 40 * 6419317 * 2
def baseEnd_6419317 : Nat := 3296195094577966126415605

theorem tailTrace_6419317 : CollatzResearch.WordTrace tailWord_6419317 prefixEnd_6419317 3296195094577966126415605 := by
  unfold tailWord_6419317
  simp only [CollatzResearch.WordTrace]
  refine ⟨234131725684918315905256205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156087817123278877270170803 234131725684918315905256205)
  ·
    refine ⟨87799397131844368464471077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234131725684918315905256205 87799397131844368464471077)
    ·
      refine ⟨16462386962220819087088327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87799397131844368464471077 16462386962220819087088327)
      ·
        refine ⟨24693580443331228630632491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16462386962220819087088327 24693580443331228630632491)
        ·
          refine ⟨37040370664996842945948737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24693580443331228630632491 37040370664996842945948737)
          ·
            refine ⟨27780277998747632209461553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37040370664996842945948737 27780277998747632209461553)
            ·
              refine ⟨20835208499060724157096165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27780277998747632209461553 20835208499060724157096165)
              ·
                refine ⟨3906601593573885779455531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20835208499060724157096165 3906601593573885779455531)
                ·
                  refine ⟨5859902390360828669183297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3906601593573885779455531 5859902390360828669183297)
                  ·
                    refine ⟨4394926792770621501887473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5859902390360828669183297 4394926792770621501887473)
                    ·
                      refine ⟨3296195094577966126415605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4394926792770621501887473 3296195094577966126415605)
                      ·
                        rfl

theorem cell23_6419317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_6419317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419317 prefixEnd_6419317 := by exact prefixLift 6419317
  have htrace : WordTrace (prefixWord ++ tailWord_6419317) baseStart_6419317 baseEnd_6419317 := by
    simpa [prefixWord, tailWord_6419317, baseEnd_6419317] using wordTrace_append hprefix tailTrace_6419317
  have hstable : (prefixWord ++ tailWord_6419317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419317).length < 2 ^ (prefixWord ++ tailWord_6419317).sum := by decide
  have hdescent : baseEnd_6419317 < baseStart_6419317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419330 : List Nat := [3, 4, 2, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_6419330 : Nat := 118140960795 + 6419330 * 2 ^ 59
def prefixEnd_6419330 : Nat := 4983230072969 + 3 ^ 40 * 6419330 * 2
def baseEnd_6419330 : Nat := 3296201769826474575553045

theorem tailTrace_6419330 : CollatzResearch.WordTrace tailWord_6419330 prefixEnd_6419330 3296201769826474575553045 := by
  unfold tailWord_6419330
  simp only [CollatzResearch.WordTrace]
  refine ⟨58533049958467804781369861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156088133222580812750319629 58533049958467804781369861)
  ·
    refine ⟨10974946867212713396506849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58533049958467804781369861 10974946867212713396506849)
    ·
      refine ⟨8231210150409535047380137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10974946867212713396506849 8231210150409535047380137)
      ·
        refine ⟨6173407612807151285535103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8231210150409535047380137 6173407612807151285535103)
        ·
          refine ⟨9260111419210726928302655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6173407612807151285535103 9260111419210726928302655)
          ·
            refine ⟨13890167128816090392453983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9260111419210726928302655 13890167128816090392453983)
            ·
              refine ⟨20835250693224135588680975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13890167128816090392453983 20835250693224135588680975)
              ·
                refine ⟨31252876039836203383021463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20835250693224135588680975 31252876039836203383021463)
                ·
                  refine ⟨46879314059754305074532195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31252876039836203383021463 46879314059754305074532195)
                  ·
                    refine ⟨70318971089631457611798293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46879314059754305074532195 70318971089631457611798293)
                    ·
                      refine ⟨3296201769826474575553045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70318971089631457611798293 3296201769826474575553045)
                      ·
                        rfl

theorem cell23_6419330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_6419330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419330 prefixEnd_6419330 := by exact prefixLift 6419330
  have htrace : WordTrace (prefixWord ++ tailWord_6419330) baseStart_6419330 baseEnd_6419330 := by
    simpa [prefixWord, tailWord_6419330, baseEnd_6419330] using wordTrace_append hprefix tailTrace_6419330
  have hstable : (prefixWord ++ tailWord_6419330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419330).length < 2 ^ (prefixWord ++ tailWord_6419330).sum := by decide
  have hdescent : baseEnd_6419330 < baseStart_6419330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419333 : List Nat := [1, 3, 1, 1, 3, 5, 1, 1, 1, 3, 3]
def baseStart_6419333 : Nat := 118140960795 + 6419333 * 2 ^ 59
def prefixEnd_6419333 : Nat := 4983230072969 + 3 ^ 40 * 6419333 * 2
def baseEnd_6419333 : Nat := 3296203310268438063815531

theorem tailTrace_6419333 : CollatzResearch.WordTrace tailWord_6419333 prefixEnd_6419333 3296203310268438063815531 := by
  unfold tailWord_6419333
  simp only [CollatzResearch.WordTrace]
  refine ⟨234132309252860350637838653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156088206168573567091892435 234132309252860350637838653)
  ·
    refine ⟨87799615969822631489189495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234132309252860350637838653 87799615969822631489189495)
    ·
      refine ⟨131699423954733947233784243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87799615969822631489189495 131699423954733947233784243)
      ·
        refine ⟨197549135932100920850676365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131699423954733947233784243 197549135932100920850676365)
        ·
          refine ⟨74080925974537845319003637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197549135932100920850676365 74080925974537845319003637)
          ·
            refine ⟨6945086810112922998656591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74080925974537845319003637 6945086810112922998656591)
            ·
              refine ⟨10417630215169384497984887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6945086810112922998656591 10417630215169384497984887)
              ·
                refine ⟨15626445322754076746977331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10417630215169384497984887 15626445322754076746977331)
                ·
                  refine ⟨23439667984131115120465997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15626445322754076746977331 23439667984131115120465997)
                  ·
                    refine ⟨8789875494049168170174749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23439667984131115120465997 8789875494049168170174749)
                    ·
                      refine ⟨3296203310268438063815531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8789875494049168170174749 3296203310268438063815531)
                      ·
                        rfl

theorem cell23_6419333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 1, 1, 3, 3].length) (baseStart_6419333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419333 prefixEnd_6419333 := by exact prefixLift 6419333
  have htrace : WordTrace (prefixWord ++ tailWord_6419333) baseStart_6419333 baseEnd_6419333 := by
    simpa [prefixWord, tailWord_6419333, baseEnd_6419333] using wordTrace_append hprefix tailTrace_6419333
  have hstable : (prefixWord ++ tailWord_6419333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419333).length < 2 ^ (prefixWord ++ tailWord_6419333).sum := by decide
  have hdescent : baseEnd_6419333 < baseStart_6419333 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419339 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 4]
def baseStart_6419339 : Nat := 118140960795 + 6419339 * 2 ^ 59
def prefixEnd_6419339 : Nat := 4983230072969 + 3 ^ 40 * 6419339 * 2
def baseEnd_6419339 : Nat := 3296206391152365040340503

theorem tailTrace_6419339 : CollatzResearch.WordTrace tailWord_6419339 prefixEnd_6419339 3296206391152365040340503 := by
  unfold tailWord_6419339
  simp only [CollatzResearch.WordTrace]
  refine ⟨234132528090838613662557071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156088352060559075775038047 234132528090838613662557071)
  ·
    refine ⟨351198792136257920493835607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234132528090838613662557071 351198792136257920493835607)
    ·
      refine ⟨526798188204386880740753411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351198792136257920493835607 526798188204386880740753411)
      ·
        refine ⟨790197282306580321111130117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526798188204386880740753411 790197282306580321111130117)
        ·
          refine ⟨148161990432483810208336897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 790197282306580321111130117 148161990432483810208336897)
          ·
            refine ⟨111121492824362857656252673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148161990432483810208336897 111121492824362857656252673)
            ·
              refine ⟨83341119618272143242189505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111121492824362857656252673 83341119618272143242189505)
              ·
                refine ⟨62505839713704107431642129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83341119618272143242189505 62505839713704107431642129)
                ·
                  refine ⟨46879379785278080573731597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62505839713704107431642129 46879379785278080573731597)
                  ·
                    refine ⟨17579767419479280215149349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46879379785278080573731597 17579767419479280215149349)
                    ·
                      refine ⟨3296206391152365040340503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17579767419479280215149349 3296206391152365040340503)
                      ·
                        rfl

theorem cell23_6419339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 4].length) (baseStart_6419339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419339 prefixEnd_6419339 := by exact prefixLift 6419339
  have htrace : WordTrace (prefixWord ++ tailWord_6419339) baseStart_6419339 baseEnd_6419339 := by
    simpa [prefixWord, tailWord_6419339, baseEnd_6419339] using wordTrace_append hprefix tailTrace_6419339
  have hstable : (prefixWord ++ tailWord_6419339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419339).length < 2 ^ (prefixWord ++ tailWord_6419339).sum := by decide
  have hdescent : baseEnd_6419339 < baseStart_6419339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419379 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 7]
def baseStart_6419379 : Nat := 118140960795 + 6419379 * 2 ^ 59
def prefixEnd_6419379 : Nat := 4983230072969 + 3 ^ 40 * 6419379 * 2
def baseEnd_6419379 : Nat := 366247436708727209315591

theorem tailTrace_6419379 : CollatzResearch.WordTrace tailWord_6419379 prefixEnd_6419379 366247436708727209315591 := by
  unfold tailWord_6419379
  simp only [CollatzResearch.WordTrace]
  refine ⟨234133987010693700494013191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156089324673795800329342127 234133987010693700494013191)
  ·
    refine ⟨351200980516040550741019787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234133987010693700494013191 351200980516040550741019787)
    ·
      refine ⟨526801470774060826111529681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351200980516040550741019787 526801470774060826111529681)
      ·
        refine ⟨395101103080545619583647261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526801470774060826111529681 395101103080545619583647261)
        ·
          refine ⟨148162913655204607343867723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395101103080545619583647261 148162913655204607343867723)
          ·
            refine ⟨222244370482806911015801585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148162913655204607343867723 222244370482806911015801585)
            ·
              refine ⟨166683277862105183261851189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222244370482806911015801585 166683277862105183261851189)
              ·
                refine ⟨15626557299572360930798549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166683277862105183261851189 15626557299572360930798549)
                ·
                  refine ⟨366247436708727209315591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15626557299572360930798549 366247436708727209315591)
                  ·
                    rfl

theorem cell23_6419379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 7].length) (baseStart_6419379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419379 prefixEnd_6419379 := by exact prefixLift 6419379
  have htrace : WordTrace (prefixWord ++ tailWord_6419379) baseStart_6419379 baseEnd_6419379 := by
    simpa [prefixWord, tailWord_6419379, baseEnd_6419379] using wordTrace_append hprefix tailTrace_6419379
  have hstable : (prefixWord ++ tailWord_6419379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419379).length < 2 ^ (prefixWord ++ tailWord_6419379).sum := by decide
  have hdescent : baseEnd_6419379 < baseStart_6419379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419463 : List Nat := [1, 1, 4, 3, 1, 1, 1, 2, 1, 6, 2]
def baseStart_6419463 : Nat := 118140960795 + 6419463 * 2 ^ 59
def prefixEnd_6419463 : Nat := 4983230072969 + 3 ^ 40 * 6419463 * 2
def baseEnd_6419463 : Nat := 3296270062753522555189933

theorem tailTrace_6419463 : CollatzResearch.WordTrace tailWord_6419463 prefixEnd_6419463 3296270062753522555189933 := by
  unfold tailWord_6419463
  simp only [CollatzResearch.WordTrace]
  refine ⟨234137050742389382840071043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156091367161592921893380695 234137050742389382840071043)
  ·
    refine ⟨351205576113584074260106565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234137050742389382840071043 351205576113584074260106565)
    ·
      refine ⟨65851045521297013923769981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 351205576113584074260106565 65851045521297013923769981)
      ·
        refine ⟨24694142070486380221413743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65851045521297013923769981 24694142070486380221413743)
        ·
          refine ⟨37041213105729570332120615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24694142070486380221413743 37041213105729570332120615)
          ·
            refine ⟨55561819658594355498180923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37041213105729570332120615 55561819658594355498180923)
            ·
              refine ⟨83342729487891533247271385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55561819658594355498180923 83342729487891533247271385)
              ·
                refine ⟨62507047115918649935453539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83342729487891533247271385 62507047115918649935453539)
                ·
                  refine ⟨93760570673877974903180309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62507047115918649935453539 93760570673877974903180309)
                  ·
                    refine ⟨4395026750338030073586577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93760570673877974903180309 4395026750338030073586577)
                    ·
                      refine ⟨3296270062753522555189933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4395026750338030073586577 3296270062753522555189933)
                      ·
                        rfl

theorem cell23_6419463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_6419463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419463 prefixEnd_6419463 := by exact prefixLift 6419463
  have htrace : WordTrace (prefixWord ++ tailWord_6419463) baseStart_6419463 baseEnd_6419463 := by
    simpa [prefixWord, tailWord_6419463, baseEnd_6419463] using wordTrace_append hprefix tailTrace_6419463
  have hstable : (prefixWord ++ tailWord_6419463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419463).length < 2 ^ (prefixWord ++ tailWord_6419463).sum := by decide
  have hdescent : baseEnd_6419463 < baseStart_6419463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419490 : List Nat := [3, 3, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_6419490 : Nat := 118140960795 + 6419490 * 2 ^ 59
def prefixEnd_6419490 : Nat := 4983230072969 + 3 ^ 40 * 6419490 * 2
def baseEnd_6419490 : Nat := 1098761308910397983184103

theorem tailTrace_6419490 : CollatzResearch.WordTrace tailWord_6419490 prefixEnd_6419490 1098761308910397983184103 := by
  unfold tailWord_6419490
  simp only [CollatzResearch.WordTrace]
  refine ⟨58534508878322891612825981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156092023675527710967535949 58534508878322891612825981)
  ·
    refine ⟨21950440829371084354809743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58534508878322891612825981 21950440829371084354809743)
    ·
      refine ⟨32925661244056626532214615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21950440829371084354809743 32925661244056626532214615)
      ·
        refine ⟨49388491866084939798321923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32925661244056626532214615 49388491866084939798321923)
        ·
          refine ⟨74082737799127409697482885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49388491866084939798321923 74082737799127409697482885)
          ·
            refine ⟨13890513337336389318278041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74082737799127409697482885 13890513337336389318278041)
            ·
              refine ⟨10417885003002291988708531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13890513337336389318278041 10417885003002291988708531)
              ·
                refine ⟨15626827504503437983062797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10417885003002291988708531 15626827504503437983062797)
                ·
                  refine ⟨5860060314188789243648549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15626827504503437983062797 5860060314188789243648549)
                  ·
                    refine ⟨1098761308910397983184103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5860060314188789243648549 1098761308910397983184103)
                    ·
                      rfl

theorem cell23_6419490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_6419490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419490 prefixEnd_6419490 := by exact prefixLift 6419490
  have htrace : WordTrace (prefixWord ++ tailWord_6419490) baseStart_6419490 baseEnd_6419490 := by
    simpa [prefixWord, tailWord_6419490, baseEnd_6419490] using wordTrace_append hprefix tailTrace_6419490
  have hstable : (prefixWord ++ tailWord_6419490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419490).length < 2 ^ (prefixWord ++ tailWord_6419490).sum := by decide
  have hdescent : baseEnd_6419490 < baseStart_6419490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419506 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6]
def baseStart_6419506 : Nat := 118140960795 + 6419506 * 2 ^ 59
def prefixEnd_6419506 : Nat := 4983230072969 + 3 ^ 40 * 6419506 * 2
def baseEnd_6419506 : Nat := 3296292142421665886952235

theorem tailTrace_6419506 : CollatzResearch.WordTrace tailWord_6419506 prefixEnd_6419506 3296292142421665886952235 := by
  unfold tailWord_6419506
  simp only [CollatzResearch.WordTrace]
  refine ⟨58534654770308400295971593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156092412720822400789257581 58534654770308400295971593)
  ·
    refine ⟨43900991077731300221978695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58534654770308400295971593 43900991077731300221978695)
    ·
      refine ⟨65851486616596950332968043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43900991077731300221978695 65851486616596950332968043)
      ·
        refine ⟨98777229924895425499452065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65851486616596950332968043 98777229924895425499452065)
        ·
          refine ⟨74082922443671569124589049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98777229924895425499452065 74082922443671569124589049)
          ·
            refine ⟨55562191832753676843441787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74082922443671569124589049 55562191832753676843441787)
            ·
              refine ⟨83343287749130515265162681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55562191832753676843441787 83343287749130515265162681)
              ·
                refine ⟨62507465811847886448872011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83343287749130515265162681 62507465811847886448872011)
                ·
                  refine ⟨93761198717771829673308017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62507465811847886448872011 93761198717771829673308017)
                  ·
                    refine ⟨70320899038328872254981013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93761198717771829673308017 70320899038328872254981013)
                    ·
                      refine ⟨3296292142421665886952235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70320899038328872254981013 3296292142421665886952235)
                      ·
                        rfl

theorem cell23_6419506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_6419506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419506 prefixEnd_6419506 := by exact prefixLift 6419506
  have htrace : WordTrace (prefixWord ++ tailWord_6419506) baseStart_6419506 baseEnd_6419506 := by
    simpa [prefixWord, tailWord_6419506, baseEnd_6419506] using wordTrace_append hprefix tailTrace_6419506
  have hstable : (prefixWord ++ tailWord_6419506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419506).length < 2 ^ (prefixWord ++ tailWord_6419506).sum := by decide
  have hdescent : baseEnd_6419506 < baseStart_6419506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419523 : List Nat := [1, 1, 1, 3, 1, 2, 3, 3, 1, 5, 2]
def baseStart_6419523 : Nat := 118140960795 + 6419523 * 2 ^ 59
def prefixEnd_6419523 : Nat := 4983230072969 + 3 ^ 40 * 6419523 * 2
def baseEnd_6419523 : Nat := 3296300871592792320439657

theorem tailTrace_6419523 : CollatzResearch.WordTrace tailWord_6419523 prefixEnd_6419523 3296300871592792320439657 := by
  unfold tailWord_6419523
  simp only [CollatzResearch.WordTrace]
  refine ⟨234139239122172013087255223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156092826081448008724836815 234139239122172013087255223)
  ·
    refine ⟨351208858683258019630882835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234139239122172013087255223 351208858683258019630882835)
    ·
      refine ⟨526813288024887029446324253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351208858683258019630882835 526813288024887029446324253)
      ·
        refine ⟨197554983009332636042371595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 526813288024887029446324253 197554983009332636042371595)
        ·
          refine ⟨296332474513998954063557393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197554983009332636042371595 296332474513998954063557393)
          ·
            refine ⟨222249355885499215547668045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296332474513998954063557393 222249355885499215547668045)
            ·
              refine ⟨83343508457062205830375517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222249355885499215547668045 83343508457062205830375517)
              ·
                refine ⟨31253815671398327186390819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83343508457062205830375517 31253815671398327186390819)
                ·
                  refine ⟨46880723507097490779586229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31253815671398327186390819 46880723507097490779586229)
                  ·
                    refine ⟨4395067828790389760586209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46880723507097490779586229 4395067828790389760586209)
                    ·
                      refine ⟨3296300871592792320439657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4395067828790389760586209 3296300871592792320439657)
                      ·
                        rfl

theorem cell23_6419523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 5, 2].length) (baseStart_6419523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419523 prefixEnd_6419523 := by exact prefixLift 6419523
  have htrace : WordTrace (prefixWord ++ tailWord_6419523) baseStart_6419523 baseEnd_6419523 := by
    simpa [prefixWord, tailWord_6419523, baseEnd_6419523] using wordTrace_append hprefix tailTrace_6419523
  have hstable : (prefixWord ++ tailWord_6419523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419523).length < 2 ^ (prefixWord ++ tailWord_6419523).sum := by decide
  have hdescent : baseEnd_6419523 < baseStart_6419523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419540 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 4, 3, 2]
def baseStart_6419540 : Nat := 118140960795 + 6419540 * 2 ^ 59
def prefixEnd_6419540 : Nat := 4983230072969 + 3 ^ 40 * 6419540 * 2
def baseEnd_6419540 : Nat := 3296309600763918753927079

theorem tailTrace_6419540 : CollatzResearch.WordTrace tailWord_6419540 prefixEnd_6419540 3296309600763918753927079 := by
  unfold tailWord_6419540
  simp only [CollatzResearch.WordTrace]
  refine ⟨117069929581555212495312037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156093239442073616660416049 117069929581555212495312037)
  ·
    refine ⟨21950611796541602342871007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117069929581555212495312037 21950611796541602342871007)
    ·
      refine ⟨32925917694812403514306511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21950611796541602342871007 32925917694812403514306511)
      ·
        refine ⟨49388876542218605271459767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32925917694812403514306511 49388876542218605271459767)
        ·
          refine ⟨74083314813327907907189651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49388876542218605271459767 74083314813327907907189651)
          ·
            refine ⟨111124972219991861860784477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74083314813327907907189651 111124972219991861860784477)
            ·
              refine ⟨41671864582496948197794179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111124972219991861860784477 41671864582496948197794179)
              ·
                refine ⟨62507796873745422296691269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41671864582496948197794179 62507796873745422296691269)
                ·
                  refine ⟨11720211913827266680629613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62507796873745422296691269 11720211913827266680629613)
                  ·
                    refine ⟨4395079467685225005236105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11720211913827266680629613 4395079467685225005236105)
                    ·
                      refine ⟨3296309600763918753927079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4395079467685225005236105 3296309600763918753927079)
                      ·
                        rfl

theorem cell23_6419540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_6419540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419540 prefixEnd_6419540 := by exact prefixLift 6419540
  have htrace : WordTrace (prefixWord ++ tailWord_6419540) baseStart_6419540 baseEnd_6419540 := by
    simpa [prefixWord, tailWord_6419540, baseEnd_6419540] using wordTrace_append hprefix tailTrace_6419540
  have hstable : (prefixWord ++ tailWord_6419540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419540).length < 2 ^ (prefixWord ++ tailWord_6419540).sum := by decide
  have hdescent : baseEnd_6419540 < baseStart_6419540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419546 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 5, 6]
def baseStart_6419546 : Nat := 118140960795 + 6419546 * 2 ^ 59
def prefixEnd_6419546 : Nat := 4983230072969 + 3 ^ 40 * 6419546 * 2
def baseEnd_6419546 : Nat := 1098770893882615243484017

theorem tailTrace_6419546 : CollatzResearch.WordTrace tailWord_6419546 prefixEnd_6419546 1098770893882615243484017 := by
  unfold tailWord_6419546
  simp only [CollatzResearch.WordTrace]
  refine ⟨58535019500272172003835623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156093385334059125343561661 58535019500272172003835623)
  ·
    refine ⟨87802529250408258005753435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58535019500272172003835623 87802529250408258005753435)
    ·
      refine ⟨131703793875612387008630153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87802529250408258005753435 131703793875612387008630153)
      ·
        refine ⟨98777845406709290256472615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131703793875612387008630153 98777845406709290256472615)
        ·
          refine ⟨148166768110063935384708923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98777845406709290256472615 148166768110063935384708923)
          ·
            refine ⟨222250152165095903077063385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148166768110063935384708923 222250152165095903077063385)
            ·
              refine ⟨166687614123821927307797539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222250152165095903077063385 166687614123821927307797539)
              ·
                refine ⟨250031421185732890961696309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166687614123821927307797539 250031421185732890961696309)
                ·
                  refine ⟨23440445736162458527659029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250031421185732890961696309 23440445736162458527659029)
                  ·
                    refine ⟨1098770893882615243484017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23440445736162458527659029 1098770893882615243484017)
                    ·
                      rfl

theorem cell23_6419546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 5, 6].length) (baseStart_6419546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419546 prefixEnd_6419546 := by exact prefixLift 6419546
  have htrace : WordTrace (prefixWord ++ tailWord_6419546) baseStart_6419546 baseEnd_6419546 := by
    simpa [prefixWord, tailWord_6419546, baseEnd_6419546] using wordTrace_append hprefix tailTrace_6419546
  have hstable : (prefixWord ++ tailWord_6419546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419546).length < 2 ^ (prefixWord ++ tailWord_6419546).sum := by decide
  have hdescent : baseEnd_6419546 < baseStart_6419546 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419576 : List Nat := [2, 1, 2, 1, 1, 1, 6, 9]
def baseStart_6419576 : Nat := 118140960795 + 6419576 * 2 ^ 59
def prefixEnd_6419576 : Nat := 4983230072969 + 3 ^ 40 * 6419576 * 2
def baseEnd_6419576 : Nat := 122086225409906689373219

theorem tailTrace_6419576 : CollatzResearch.WordTrace tailWord_6419576 prefixEnd_6419576 122086225409906689373219 := by
  unfold tailWord_6419576
  simp only [CollatzResearch.WordTrace]
  refine ⟨117070586095490001569467291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156094114793986668759289721 117070586095490001569467291)
  ·
    refine ⟨175605879143235002354200937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117070586095490001569467291 175605879143235002354200937)
    ·
      refine ⟨131704409357426251765650703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175605879143235002354200937 131704409357426251765650703)
      ·
        refine ⟨197556614036139377648476055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131704409357426251765650703 197556614036139377648476055)
        ·
          refine ⟨296334921054209066472714083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197556614036139377648476055 296334921054209066472714083)
          ·
            refine ⟨444502381581313599709071125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296334921054209066472714083 444502381581313599709071125)
            ·
              refine ⟨20836049136624074986362709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 444502381581313599709071125 20836049136624074986362709)
              ·
                refine ⟨122086225409906689373219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20836049136624074986362709 122086225409906689373219)
                ·
                  rfl

theorem cell23_6419576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 6, 9].length) (baseStart_6419576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419576 prefixEnd_6419576 := by exact prefixLift 6419576
  have htrace : WordTrace (prefixWord ++ tailWord_6419576) baseStart_6419576 baseEnd_6419576 := by
    simpa [prefixWord, tailWord_6419576, baseEnd_6419576] using wordTrace_append hprefix tailTrace_6419576
  have hstable : (prefixWord ++ tailWord_6419576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419576).length < 2 ^ (prefixWord ++ tailWord_6419576).sum := by decide
  have hdescent : baseEnd_6419576 < baseStart_6419576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419610 : List Nat := [3, 1, 1, 5, 1, 3, 1, 8]
def baseStart_6419610 : Nat := 118140960795 + 6419610 * 2 ^ 59
def prefixEnd_6419610 : Nat := 4983230072969 + 3 ^ 40 * 6419610 * 2
def baseEnd_6419610 : Nat := 122086872015175314075991

theorem tailTrace_6419610 : CollatzResearch.WordTrace tailWord_6419610 prefixEnd_6419610 122086872015175314075991 := by
  unfold tailWord_6419610
  simp only [CollatzResearch.WordTrace]
  refine ⟨58535603068214206736418071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156094941515237884630448189 58535603068214206736418071)
  ·
    refine ⟨87803404602321310104627107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58535603068214206736418071 87803404602321310104627107)
    ·
      refine ⟨131705106903481965156940661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87803404602321310104627107 131705106903481965156940661)
      ·
        refine ⟨12347353772201434233463187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131705106903481965156940661 12347353772201434233463187)
        ·
          refine ⟨18521030658302151350194781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12347353772201434233463187 18521030658302151350194781)
          ·
            refine ⟨6945386496863306756323043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18521030658302151350194781 6945386496863306756323043)
            ·
              refine ⟨10418079745294960134484565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6945386496863306756323043 10418079745294960134484565)
              ·
                refine ⟨122086872015175314075991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10418079745294960134484565 122086872015175314075991)
                ·
                  rfl

theorem cell23_6419610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 1, 8].length) (baseStart_6419610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419610 prefixEnd_6419610 := by exact prefixLift 6419610
  have htrace : WordTrace (prefixWord ++ tailWord_6419610) baseStart_6419610 baseEnd_6419610 := by
    simpa [prefixWord, tailWord_6419610, baseEnd_6419610] using wordTrace_append hprefix tailTrace_6419610
  have hstable : (prefixWord ++ tailWord_6419610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419610).length < 2 ^ (prefixWord ++ tailWord_6419610).sum := by decide
  have hdescent : baseEnd_6419610 < baseStart_6419610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419620 : List Nat := [2, 3, 1, 2, 3, 1, 1, 3, 1, 3, 3]
def baseStart_6419620 : Nat := 118140960795 + 6419620 * 2 ^ 59
def prefixEnd_6419620 : Nat := 4983230072969 + 3 ^ 40 * 6419620 * 2
def baseEnd_6419620 : Nat := 3296350679216278440926711

theorem tailTrace_6419620 : CollatzResearch.WordTrace tailWord_6419620 prefixEnd_6419620 3296350679216278440926711 := by
  unfold tailWord_6419620
  simp only [CollatzResearch.WordTrace]
  refine ⟨117071388501410299326768157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156095184668547065769024209 117071388501410299326768157)
  ·
    refine ⟨43901770688028862247538059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117071388501410299326768157 43901770688028862247538059)
    ·
      refine ⟨65852656032043293371307089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43901770688028862247538059 65852656032043293371307089)
      ·
        refine ⟨49389492024032470028480317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65852656032043293371307089 49389492024032470028480317)
        ·
          refine ⟨18521059509012176260680119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49389492024032470028480317 18521059509012176260680119)
          ·
            refine ⟨27781589263518264391020179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18521059509012176260680119 27781589263518264391020179)
            ·
              refine ⟨41672383895277396586530269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27781589263518264391020179 41672383895277396586530269)
              ·
                refine ⟨15627143960729023719948851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41672383895277396586530269 15627143960729023719948851)
                ·
                  refine ⟨23440715941093535579923277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15627143960729023719948851 23440715941093535579923277)
                  ·
                    refine ⟨8790268477910075842471229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23440715941093535579923277 8790268477910075842471229)
                    ·
                      refine ⟨3296350679216278440926711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8790268477910075842471229 3296350679216278440926711)
                      ·
                        rfl

theorem cell23_6419620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_6419620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419620 prefixEnd_6419620 := by exact prefixLift 6419620
  have htrace : WordTrace (prefixWord ++ tailWord_6419620) baseStart_6419620 baseEnd_6419620 := by
    simpa [prefixWord, tailWord_6419620, baseEnd_6419620] using wordTrace_append hprefix tailTrace_6419620
  have hstable : (prefixWord ++ tailWord_6419620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419620).length < 2 ^ (prefixWord ++ tailWord_6419620).sum := by decide
  have hdescent : baseEnd_6419620 < baseStart_6419620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419638 : List Nat := [5, 1, 3, 2, 1, 2, 2, 1, 1, 1, 4]
def baseStart_6419638 : Nat := 118140960795 + 6419638 * 2 ^ 59
def prefixEnd_6419638 : Nat := 4983230072969 + 3 ^ 40 * 6419638 * 2
def baseEnd_6419638 : Nat := 3296359921868059370501629

theorem tailTrace_6419638 : CollatzResearch.WordTrace tailWord_6419638 prefixEnd_6419638 3296359921868059370501629 := by
  unfold tailWord_6419638
  simp only [CollatzResearch.WordTrace]
  refine ⟨14633964594797211732980723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156095622344503591818461045 14633964594797211732980723)
  ·
    refine ⟨21950946892195817599471085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14633964594797211732980723 21950946892195817599471085)
    ·
      refine ⟨8231605084573431599801657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21950946892195817599471085 8231605084573431599801657)
      ·
        refine ⟨6173703813430073699851243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8231605084573431599801657 6173703813430073699851243)
        ·
          refine ⟨9260555720145110549776865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6173703813430073699851243 9260555720145110549776865)
          ·
            refine ⟨6945416790108832912332649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9260555720145110549776865 6945416790108832912332649)
            ·
              refine ⟨5209062592581624684249487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6945416790108832912332649 5209062592581624684249487)
              ·
                refine ⟨7813593888872437026374231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5209062592581624684249487 7813593888872437026374231)
                ·
                  refine ⟨11720390833308655539561347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7813593888872437026374231 11720390833308655539561347)
                  ·
                    refine ⟨17580586249962983309342021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11720390833308655539561347 17580586249962983309342021)
                    ·
                      refine ⟨3296359921868059370501629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17580586249962983309342021 3296359921868059370501629)
                      ·
                        rfl

theorem cell23_6419638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_6419638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419638 prefixEnd_6419638 := by exact prefixLift 6419638
  have htrace : WordTrace (prefixWord ++ tailWord_6419638) baseStart_6419638 baseEnd_6419638 := by
    simpa [prefixWord, tailWord_6419638, baseEnd_6419638] using wordTrace_append hprefix tailTrace_6419638
  have hstable : (prefixWord ++ tailWord_6419638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419638).length < 2 ^ (prefixWord ++ tailWord_6419638).sum := by decide
  have hdescent : baseEnd_6419638 < baseStart_6419638 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419663 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 3]
def baseStart_6419663 : Nat := 118140960795 + 6419663 * 2 ^ 59
def prefixEnd_6419663 : Nat := 4983230072969 + 3 ^ 40 * 6419663 * 2
def baseEnd_6419663 : Nat := 3296372758884421772689013

theorem tailTrace_6419663 : CollatzResearch.WordTrace tailWord_6419663 prefixEnd_6419663 3296372758884421772689013 := by
  unfold tailWord_6419663
  simp only [CollatzResearch.WordTrace]
  refine ⟨234144345341664816997351643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156096230227776544664901095 234144345341664816997351643)
  ·
    refine ⟨351216518012497225496027465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234144345341664816997351643 351216518012497225496027465)
    ·
      refine ⟨263412388509372919122020599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351216518012497225496027465 263412388509372919122020599)
      ·
        refine ⟨395118582764059378683030899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263412388509372919122020599 395118582764059378683030899)
        ·
          refine ⟨592677874146089068024546349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395118582764059378683030899 592677874146089068024546349)
          ·
            refine ⟨222254202804783400509204881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 592677874146089068024546349 222254202804783400509204881)
            ·
              refine ⟨166690652103587550381903661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222254202804783400509204881 166690652103587550381903661)
              ·
                refine ⟨62508994538845331393213873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166690652103587550381903661 62508994538845331393213873)
                ·
                  refine ⟨46881745904133998544910405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62508994538845331393213873 46881745904133998544910405)
                  ·
                    refine ⟨8790327357025124727170701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46881745904133998544910405 8790327357025124727170701)
                    ·
                      refine ⟨3296372758884421772689013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8790327357025124727170701 3296372758884421772689013)
                      ·
                        rfl

theorem cell23_6419663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 3].length) (baseStart_6419663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419663 prefixEnd_6419663 := by exact prefixLift 6419663
  have htrace : WordTrace (prefixWord ++ tailWord_6419663) baseStart_6419663 baseEnd_6419663 := by
    simpa [prefixWord, tailWord_6419663, baseEnd_6419663] using wordTrace_append hprefix tailTrace_6419663
  have hstable : (prefixWord ++ tailWord_6419663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419663).length < 2 ^ (prefixWord ++ tailWord_6419663).sum := by decide
  have hdescent : baseEnd_6419663 < baseStart_6419663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419717 : List Nat := [1, 3, 1, 1, 2, 1, 7, 2, 5]
def baseStart_6419717 : Nat := 118140960795 + 6419717 * 2 ^ 59
def prefixEnd_6419717 : Nat := 4983230072969 + 3 ^ 40 * 6419717 * 2
def baseEnd_6419717 : Nat := 366266720759973840157085

theorem tailTrace_6419717 : CollatzResearch.WordTrace tailWord_6419717 prefixEnd_6419717 366266720759973840157085 := by
  unfold tailWord_6419717
  simp only [CollatzResearch.WordTrace]
  refine ⟨234146314883469184219817405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156097543255646122813211603 234146314883469184219817405)
  ·
    refine ⟨87804868081300944082431527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234146314883469184219817405 87804868081300944082431527)
    ·
      refine ⟨131707302121951416123647291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87804868081300944082431527 131707302121951416123647291)
      ·
        refine ⟨197560953182927124185470937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131707302121951416123647291 197560953182927124185470937)
        ·
          refine ⟨148170714887195343139103203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197560953182927124185470937 148170714887195343139103203)
          ·
            refine ⟨222256072330793014708654805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148170714887195343139103203 222256072330793014708654805)
            ·
              refine ⟨5209126695252961282234097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 222256072330793014708654805 5209126695252961282234097)
              ·
                refine ⟨3906845021439720961675573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5209126695252961282234097 3906845021439720961675573)
                ·
                  refine ⟨366266720759973840157085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3906845021439720961675573 366266720759973840157085)
                  ·
                    rfl

theorem cell23_6419717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 5].length) (baseStart_6419717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419717 prefixEnd_6419717 := by exact prefixLift 6419717
  have htrace : WordTrace (prefixWord ++ tailWord_6419717) baseStart_6419717 baseEnd_6419717 := by
    simpa [prefixWord, tailWord_6419717, baseEnd_6419717] using wordTrace_append hprefix tailTrace_6419717
  have hstable : (prefixWord ++ tailWord_6419717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419717).length < 2 ^ (prefixWord ++ tailWord_6419717).sum := by decide
  have hdescent : baseEnd_6419717 < baseStart_6419717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419723 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 7]
def baseStart_6419723 : Nat := 118140960795 + 6419723 * 2 ^ 59
def prefixEnd_6419723 : Nat := 4983230072969 + 3 ^ 40 * 6419723 * 2
def baseEnd_6419723 : Nat := 3296403567723691537938737

theorem tailTrace_6419723 : CollatzResearch.WordTrace tailWord_6419723 prefixEnd_6419723 3296403567723691537938737 := by
  unfold tailWord_6419723
  simp only [CollatzResearch.WordTrace]
  refine ⟨234146533721447447244535823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156097689147631631496357215 234146533721447447244535823)
  ·
    refine ⟨351219800582171170866803735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234146533721447447244535823 351219800582171170866803735)
    ·
      refine ⟨526829700873256756300205603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351219800582171170866803735 526829700873256756300205603)
      ·
        refine ⟨790244551309885134450308405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526829700873256756300205603 790244551309885134450308405)
        ·
          refine ⟨74085426685301731354716413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 790244551309885134450308405 74085426685301731354716413)
          ·
            refine ⟨27782035006988149258018655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74085426685301731354716413 27782035006988149258018655)
            ·
              refine ⟨41673052510482223887027983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27782035006988149258018655 41673052510482223887027983)
              ·
                refine ⟨62509578765723335830541975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41673052510482223887027983 62509578765723335830541975)
                ·
                  refine ⟨93764368148585003745812963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62509578765723335830541975 93764368148585003745812963)
                  ·
                    refine ⟨140646552222877505618719445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93764368148585003745812963 140646552222877505618719445)
                    ·
                      refine ⟨3296403567723691537938737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140646552222877505618719445 3296403567723691537938737)
                      ·
                        rfl

theorem cell23_6419723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 7].length) (baseStart_6419723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419723 prefixEnd_6419723 := by exact prefixLift 6419723
  have htrace : WordTrace (prefixWord ++ tailWord_6419723) baseStart_6419723 baseEnd_6419723 := by
    simpa [prefixWord, tailWord_6419723, baseEnd_6419723] using wordTrace_append hprefix tailTrace_6419723
  have hstable : (prefixWord ++ tailWord_6419723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419723).length < 2 ^ (prefixWord ++ tailWord_6419723).sum := by decide
  have hdescent : baseEnd_6419723 < baseStart_6419723 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419757 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_6419757 : Nat := 118140960795 + 6419757 * 2 ^ 59
def prefixEnd_6419757 : Nat := 4983230072969 + 3 ^ 40 * 6419757 * 2
def baseEnd_6419757 : Nat := 3296421026065944404913581

theorem tailTrace_6419757 : CollatzResearch.WordTrace tailWord_6419757 prefixEnd_6419757 3296421026065944404913581 := by
  unfold tailWord_6419757
  simp only [CollatzResearch.WordTrace]
  refine ⟨234147773803324271051273525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156098515868882847367515683 234147773803324271051273525)
  ·
    refine ⟨21951353794061650411056893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234147773803324271051273525 21951353794061650411056893)
    ·
      refine ⟨8231757672773118904146335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21951353794061650411056893 8231757672773118904146335)
      ·
        refine ⟨12347636509159678356219503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8231757672773118904146335 12347636509159678356219503)
        ·
          refine ⟨18521454763739517534329255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12347636509159678356219503 18521454763739517534329255)
          ·
            refine ⟨27782182145609276301493883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18521454763739517534329255 27782182145609276301493883)
            ·
              refine ⟨41673273218413914452240825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27782182145609276301493883 41673273218413914452240825)
              ·
                refine ⟨31254954913810435839180619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41673273218413914452240825 31254954913810435839180619)
                ·
                  refine ⟨46882432370715653758770929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31254954913810435839180619 46882432370715653758770929)
                  ·
                    refine ⟨35161824278036740319078197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46882432370715653758770929 35161824278036740319078197)
                    ·
                      refine ⟨3296421026065944404913581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35161824278036740319078197 3296421026065944404913581)
                      ·
                        rfl

theorem cell23_6419757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_6419757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419757 prefixEnd_6419757 := by exact prefixLift 6419757
  have htrace : WordTrace (prefixWord ++ tailWord_6419757) baseStart_6419757 baseEnd_6419757 := by
    simpa [prefixWord, tailWord_6419757, baseEnd_6419757] using wordTrace_append hprefix tailTrace_6419757
  have hstable : (prefixWord ++ tailWord_6419757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419757).length < 2 ^ (prefixWord ++ tailWord_6419757).sum := by decide
  have hdescent : baseEnd_6419757 < baseStart_6419757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419790 : List Nat := [4, 1, 1, 1, 1, 1, 3, 5, 6]
def baseStart_6419790 : Nat := 118140960795 + 6419790 * 2 ^ 59
def prefixEnd_6419790 : Nat := 4983230072969 + 3 ^ 40 * 6419790 * 2
def baseEnd_6419790 : Nat := 366270885658615863977881

theorem tailTrace_6419790 : CollatzResearch.WordTrace tailWord_6419790 prefixEnd_6419790 366270885658615863977881 := by
  unfold tailWord_6419790
  simp only [CollatzResearch.WordTrace]
  refine ⟨29268622176525589710903103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156099318274803145124816549 29268622176525589710903103)
  ·
    refine ⟨43902933264788384566354655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29268622176525589710903103 43902933264788384566354655)
    ·
      refine ⟨65854399897182576849531983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43902933264788384566354655 65854399897182576849531983)
      ·
        refine ⟨98781599845773865274297975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65854399897182576849531983 98781599845773865274297975)
        ·
          refine ⟨148172399768660797911446963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98781599845773865274297975 148172399768660797911446963)
          ·
            refine ⟨222258599652991196867170445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148172399768660797911446963 222258599652991196867170445)
            ·
              refine ⟨83346974869871698825188917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222258599652991196867170445 83346974869871698825188917)
              ·
                refine ⟨7813778894050471764861461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83346974869871698825188917 7813778894050471764861461)
                ·
                  refine ⟨366270885658615863977881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7813778894050471764861461 366270885658615863977881)
                  ·
                    rfl

theorem cell23_6419790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_6419790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419790 prefixEnd_6419790 := by exact prefixLift 6419790
  have htrace : WordTrace (prefixWord ++ tailWord_6419790) baseStart_6419790 baseEnd_6419790 := by
    simpa [prefixWord, tailWord_6419790, baseEnd_6419790] using wordTrace_append hprefix tailTrace_6419790
  have hstable : (prefixWord ++ tailWord_6419790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419790).length < 2 ^ (prefixWord ++ tailWord_6419790).sum := by decide
  have hdescent : baseEnd_6419790 < baseStart_6419790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419840 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 4]
def baseStart_6419840 : Nat := 118140960795 + 6419840 * 2 ^ 59
def prefixEnd_6419840 : Nat := 4983230072969 + 3 ^ 40 * 6419840 * 2
def baseEnd_6419840 : Nat := 3296463644960267580175699

theorem tailTrace_6419840 : CollatzResearch.WordTrace tailWord_6419840 prefixEnd_6419840 3296463644960267580175699 := by
  unfold tailWord_6419840
  simp only [CollatzResearch.WordTrace]
  refine ⟨117075400531011788113272487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156100534041349050817696649 117075400531011788113272487)
  ·
    refine ⟨175613100796517682169908731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117075400531011788113272487 175613100796517682169908731)
    ·
      refine ⟨263419651194776523254863097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175613100796517682169908731 263419651194776523254863097)
      ·
        refine ⟨197564738396082392441147323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263419651194776523254863097 197564738396082392441147323)
        ·
          refine ⟨296347107594123588661720985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197564738396082392441147323 296347107594123588661720985)
          ·
            refine ⟨222260330695592691496290739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296347107594123588661720985 222260330695592691496290739)
            ·
              refine ⟨333390496043389037244436109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222260330695592691496290739 333390496043389037244436109)
              ·
                refine ⟨125021436016270888966663541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 333390496043389037244436109 125021436016270888966663541)
                ·
                  refine ⟨11720759626525395840624707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125021436016270888966663541 11720759626525395840624707)
                  ·
                    refine ⟨17581139439788093760937061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11720759626525395840624707 17581139439788093760937061)
                    ·
                      refine ⟨3296463644960267580175699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17581139439788093760937061 3296463644960267580175699)
                      ·
                        rfl

theorem cell23_6419840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 4].length) (baseStart_6419840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419840 prefixEnd_6419840 := by exact prefixLift 6419840
  have htrace : WordTrace (prefixWord ++ tailWord_6419840) baseStart_6419840 baseEnd_6419840 := by
    simpa [prefixWord, tailWord_6419840, baseEnd_6419840] using wordTrace_append hprefix tailTrace_6419840
  have hstable : (prefixWord ++ tailWord_6419840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419840).length < 2 ^ (prefixWord ++ tailWord_6419840).sum := by decide
  have hdescent : baseEnd_6419840 < baseStart_6419840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419874 : List Nat := [3, 3, 1, 2, 1, 2, 2, 3, 1, 1, 4]
def baseStart_6419874 : Nat := 118140960795 + 6419874 * 2 ^ 59
def prefixEnd_6419874 : Nat := 4983230072969 + 3 ^ 40 * 6419874 * 2
def baseEnd_6419874 : Nat := 3296481103302520447150543

theorem tailTrace_6419874 : CollatzResearch.WordTrace tailWord_6419874 prefixEnd_6419874 3296481103302520447150543 := by
  unfold tailWord_6419874
  simp only [CollatzResearch.WordTrace]
  refine ⟨58538010285975100008320669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156101360762600266688855117 58538010285975100008320669)
  ·
    refine ⟨21951753857240662503120251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58538010285975100008320669 21951753857240662503120251)
    ·
      refine ⟨32927630785860993754680377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21951753857240662503120251 32927630785860993754680377)
      ·
        refine ⟨24695723089395745316010283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32927630785860993754680377 24695723089395745316010283)
        ·
          refine ⟨37043584634093617974015425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24695723089395745316010283 37043584634093617974015425)
          ·
            refine ⟨27782688475570213480511569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37043584634093617974015425 27782688475570213480511569)
            ·
              refine ⟨20837016356677660110383677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27782688475570213480511569 20837016356677660110383677)
              ·
                refine ⟨7813881133754122541393879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20837016356677660110383677 7813881133754122541393879)
                ·
                  refine ⟨11720821700631183812090819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7813881133754122541393879 11720821700631183812090819)
                  ·
                    refine ⟨17581232550946775718136229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11720821700631183812090819 17581232550946775718136229)
                    ·
                      refine ⟨3296481103302520447150543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17581232550946775718136229 3296481103302520447150543)
                      ·
                        rfl

theorem cell23_6419874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_6419874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419874 prefixEnd_6419874 := by exact prefixLift 6419874
  have htrace : WordTrace (prefixWord ++ tailWord_6419874) baseStart_6419874 baseEnd_6419874 := by
    simpa [prefixWord, tailWord_6419874, baseEnd_6419874] using wordTrace_append hprefix tailTrace_6419874
  have hstable : (prefixWord ++ tailWord_6419874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419874).length < 2 ^ (prefixWord ++ tailWord_6419874).sum := by decide
  have hdescent : baseEnd_6419874 < baseStart_6419874 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419885 : List Nat := [1, 5, 2, 2, 1, 2, 3, 2, 1, 1, 3]
def baseStart_6419885 : Nat := 118140960795 + 6419885 * 2 ^ 59
def prefixEnd_6419885 : Nat := 4983230072969 + 3 ^ 40 * 6419885 * 2
def baseEnd_6419885 : Nat := 3296486751589719904112993

theorem tailTrace_6419885 : CollatzResearch.WordTrace tailWord_6419885 prefixEnd_6419885 3296486751589719904112993 := by
  unfold tailWord_6419885
  simp only [CollatzResearch.WordTrace]
  refine ⟨234152442346860548911933109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156101628231240365941288739 234152442346860548911933109)
  ·
    refine ⟨21951791470018176460493729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234152442346860548911933109 21951791470018176460493729)
    ·
      refine ⟨16463843602513632345370297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21951791470018176460493729 16463843602513632345370297)
      ·
        refine ⟨12347882701885224259027723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16463843602513632345370297 12347882701885224259027723)
        ·
          refine ⟨18521824052827836388541585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12347882701885224259027723 18521824052827836388541585)
          ·
            refine ⟨13891368039620877291406189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18521824052827836388541585 13891368039620877291406189)
            ·
              refine ⟨5209263014857828984277321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13891368039620877291406189 5209263014857828984277321)
              ·
                refine ⟨3906947261143371738207991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5209263014857828984277321 3906947261143371738207991)
                ·
                  refine ⟨5860420891715057607311987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3906947261143371738207991 5860420891715057607311987)
                  ·
                    refine ⟨8790631337572586410967981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5860420891715057607311987 8790631337572586410967981)
                    ·
                      refine ⟨3296486751589719904112993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8790631337572586410967981 3296486751589719904112993)
                      ·
                        rfl

theorem cell23_6419885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_6419885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419885 prefixEnd_6419885 := by exact prefixLift 6419885
  have htrace : WordTrace (prefixWord ++ tailWord_6419885) baseStart_6419885 baseEnd_6419885 := by
    simpa [prefixWord, tailWord_6419885, baseEnd_6419885] using wordTrace_append hprefix tailTrace_6419885
  have hstable : (prefixWord ++ tailWord_6419885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419885).length < 2 ^ (prefixWord ++ tailWord_6419885).sum := by decide
  have hdescent : baseEnd_6419885 < baseStart_6419885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419891 : List Nat := [1, 1, 1, 2, 3, 1, 1, 8, 1, 2, 2]
def baseStart_6419891 : Nat := 118140960795 + 6419891 * 2 ^ 59
def prefixEnd_6419891 : Nat := 4983230072969 + 3 ^ 40 * 6419891 * 2
def baseEnd_6419891 : Nat := 3296489832473646880637965

theorem tailTrace_6419891 : CollatzResearch.WordTrace tailWord_6419891 prefixEnd_6419891 3296489832473646880637965 := by
  unfold tailWord_6419891
  simp only [CollatzResearch.WordTrace]
  refine ⟨234152661184838811936651527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156101774123225874624434351 234152661184838811936651527)
  ·
    refine ⟨351228991777258217904977291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234152661184838811936651527 351228991777258217904977291)
    ·
      refine ⟨526843487665887326857465937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351228991777258217904977291 526843487665887326857465937)
      ·
        refine ⟨395132615749415495143099453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526843487665887326857465937 395132615749415495143099453)
        ·
          refine ⟨148174730906030810678662295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395132615749415495143099453 148174730906030810678662295)
          ·
            refine ⟨222262096359046216017993443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148174730906030810678662295 222262096359046216017993443)
            ·
              refine ⟨333393144538569324026990165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222262096359046216017993443 333393144538569324026990165)
              ·
                refine ⟨3906950912561359265941291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 333393144538569324026990165 3906950912561359265941291)
                ·
                  refine ⟨5860426368842038898911937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3906950912561359265941291 5860426368842038898911937)
                  ·
                    refine ⟨4395319776631529174183953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5860426368842038898911937 4395319776631529174183953)
                    ·
                      refine ⟨3296489832473646880637965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4395319776631529174183953 3296489832473646880637965)
                      ·
                        rfl

theorem cell23_6419891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 1, 2, 2].length) (baseStart_6419891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419891 prefixEnd_6419891 := by exact prefixLift 6419891
  have htrace : WordTrace (prefixWord ++ tailWord_6419891) baseStart_6419891 baseEnd_6419891 := by
    simpa [prefixWord, tailWord_6419891, baseEnd_6419891] using wordTrace_append hprefix tailTrace_6419891
  have hstable : (prefixWord ++ tailWord_6419891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419891).length < 2 ^ (prefixWord ++ tailWord_6419891).sum := by decide
  have hdescent : baseEnd_6419891 < baseStart_6419891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419897 : List Nat := [1, 2, 1, 4, 4, 1, 2, 8]
def baseStart_6419897 : Nat := 118140960795 + 6419897 * 2 ^ 59
def prefixEnd_6419897 : Nat := 4983230072969 + 3 ^ 40 * 6419897 * 2
def baseEnd_6419897 : Nat := 122092330124354587302331

theorem tailTrace_6419897 : CollatzResearch.WordTrace tailWord_6419897 prefixEnd_6419897 122092330124354587302331 := by
  unfold tailWord_6419897
  simp only [CollatzResearch.WordTrace]
  refine ⟨234152880022817074961369945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156101920015211383307579963 234152880022817074961369945)
  ·
    refine ⟨175614660017112806221027459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234152880022817074961369945 175614660017112806221027459)
    ·
      refine ⟨263421990025669209331541189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175614660017112806221027459 263421990025669209331541189)
      ·
        refine ⟨49391623129812976749663973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263421990025669209331541189 49391623129812976749663973)
        ·
          refine ⟨9260929336839933140561995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49391623129812976749663973 9260929336839933140561995)
          ·
            refine ⟨13891394005259899710842993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9260929336839933140561995 13891394005259899710842993)
            ·
              refine ⟨10418545503944924783132245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13891394005259899710842993 10418545503944924783132245)
              ·
                refine ⟨122092330124354587302331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10418545503944924783132245 122092330124354587302331)
                ·
                  rfl

theorem cell23_6419897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 2, 8].length) (baseStart_6419897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419897 prefixEnd_6419897 := by exact prefixLift 6419897
  have htrace : WordTrace (prefixWord ++ tailWord_6419897) baseStart_6419897 baseEnd_6419897 := by
    simpa [prefixWord, tailWord_6419897, baseEnd_6419897] using wordTrace_append hprefix tailTrace_6419897
  have hstable : (prefixWord ++ tailWord_6419897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419897).length < 2 ^ (prefixWord ++ tailWord_6419897).sum := by decide
  have hdescent : baseEnd_6419897 < baseStart_6419897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419940 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 3, 8]
def baseStart_6419940 : Nat := 118140960795 + 6419940 * 2 ^ 59
def prefixEnd_6419940 : Nat := 4983230072969 + 3 ^ 40 * 6419940 * 2
def baseEnd_6419940 : Nat := 1098838331008572396308413

theorem tailTrace_6419940 : CollatzResearch.WordTrace tailWord_6419940 prefixEnd_6419940 1098838331008572396308413 := by
  unfold tailWord_6419940
  simp only [CollatzResearch.WordTrace]
  refine ⟨117077224180830646652592637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156102965574440862203456849 117077224180830646652592637)
  ·
    refine ⟨43903959067811492494722239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117077224180830646652592637 43903959067811492494722239)
    ·
      refine ⟨65855938601717238742083359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43903959067811492494722239 65855938601717238742083359)
      ·
        refine ⟨98783907902575858113125039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65855938601717238742083359 98783907902575858113125039)
        ·
          refine ⟨148175861853863787169687559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98783907902575858113125039 148175861853863787169687559)
          ·
            refine ⟨222263792780795680754531339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148175861853863787169687559 222263792780795680754531339)
            ·
              refine ⟨333395689171193521131797009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222263792780795680754531339 333395689171193521131797009)
              ·
                refine ⟨250046766878395140848847757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333395689171193521131797009 250046766878395140848847757)
                ·
                  refine ⟨93767537579398177818317909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250046766878395140848847757 93767537579398177818317909)
                  ·
                    refine ⟨1098838331008572396308413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93767537579398177818317909 1098838331008572396308413)
                    ·
                      rfl

theorem cell23_6419940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_6419940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419940 prefixEnd_6419940 := by exact prefixLift 6419940
  have htrace : WordTrace (prefixWord ++ tailWord_6419940) baseStart_6419940 baseEnd_6419940 := by
    simpa [prefixWord, tailWord_6419940, baseEnd_6419940] using wordTrace_append hprefix tailTrace_6419940
  have hstable : (prefixWord ++ tailWord_6419940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419940).length < 2 ^ (prefixWord ++ tailWord_6419940).sum := by decide
  have hdescent : baseEnd_6419940 < baseStart_6419940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419941 : List Nat := [1, 3, 1, 5, 1, 1, 1, 4, 2, 1, 3]
def baseStart_6419941 : Nat := 118140960795 + 6419941 * 2 ^ 59
def prefixEnd_6419941 : Nat := 4983230072969 + 3 ^ 40 * 6419941 * 2
def baseEnd_6419941 : Nat := 3296515506506371685012735

theorem tailTrace_6419941 : CollatzResearch.WordTrace tailWord_6419941 prefixEnd_6419941 3296515506506371685012735 := by
  unfold tailWord_6419941
  simp only [CollatzResearch.WordTrace]
  refine ⟨234154484834657670475971677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156102989889771780317314451 234154484834657670475971677)
  ·
    refine ⟨87807931812996626428489379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234154484834657670475971677 87807931812996626428489379)
    ·
      refine ⟨131711897719494939642734069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87807931812996626428489379 131711897719494939642734069)
      ·
        refine ⟨12347990411202650591506319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131711897719494939642734069 12347990411202650591506319)
        ·
          refine ⟨18521985616803975887259479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12347990411202650591506319 18521985616803975887259479)
          ·
            refine ⟨27782978425205963830889219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18521985616803975887259479 27782978425205963830889219)
            ·
              refine ⟨41674467637808945746333829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27782978425205963830889219 41674467637808945746333829)
              ·
                refine ⟨7813962682089177327437593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41674467637808945746333829 7813962682089177327437593)
                ·
                  refine ⟨5860472011566882995578195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7813962682089177327437593 5860472011566882995578195)
                  ·
                    refine ⟨8790708017350324493367293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5860472011566882995578195 8790708017350324493367293)
                    ·
                      refine ⟨3296515506506371685012735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8790708017350324493367293 3296515506506371685012735)
                      ·
                        rfl

theorem cell23_6419941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_6419941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419941 prefixEnd_6419941 := by exact prefixLift 6419941
  have htrace : WordTrace (prefixWord ++ tailWord_6419941) baseStart_6419941 baseEnd_6419941 := by
    simpa [prefixWord, tailWord_6419941, baseEnd_6419941] using wordTrace_append hprefix tailTrace_6419941
  have hstable : (prefixWord ++ tailWord_6419941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419941).length < 2 ^ (prefixWord ++ tailWord_6419941).sum := by decide
  have hdescent : baseEnd_6419941 < baseStart_6419941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6419964 : List Nat := [2, 2, 2, 1, 2, 1, 3, 3, 1, 4, 2]
def baseStart_6419964 : Nat := 118140960795 + 6419964 * 2 ^ 59
def prefixEnd_6419964 : Nat := 4983230072969 + 3 ^ 40 * 6419964 * 2
def baseEnd_6419964 : Nat := 3296527316561425095025129

theorem tailTrace_6419964 : CollatzResearch.WordTrace tailWord_6419964 prefixEnd_6419964 3296527316561425095025129 := by
  unfold tailWord_6419964
  simp only [CollatzResearch.WordTrace]
  refine ⟨117077661856787172702029473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156103549142382896936039297 117077661856787172702029473)
  ·
    refine ⟨87808246392590379526522105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117077661856787172702029473 87808246392590379526522105)
    ·
      refine ⟨65856184794442784644891579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87808246392590379526522105 65856184794442784644891579)
      ·
        refine ⟨98784277191664176967337369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65856184794442784644891579 98784277191664176967337369)
        ·
          refine ⟨74088207893748132725503027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98784277191664176967337369 74088207893748132725503027)
          ·
            refine ⟨111132311840622199088254541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74088207893748132725503027 111132311840622199088254541)
            ·
              refine ⟨41674616940233324658095453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111132311840622199088254541 41674616940233324658095453)
              ·
                refine ⟨15627981352587496746785795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41674616940233324658095453 15627981352587496746785795)
                ·
                  refine ⟨23441972028881245120178693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15627981352587496746785795 23441972028881245120178693)
                  ·
                    refine ⟨4395369755415233460033505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23441972028881245120178693 4395369755415233460033505)
                    ·
                      refine ⟨3296527316561425095025129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4395369755415233460033505 3296527316561425095025129)
                      ·
                        rfl

theorem cell23_6419964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 3, 1, 4, 2].length) (baseStart_6419964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6419964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6419964 prefixEnd_6419964 := by exact prefixLift 6419964
  have htrace : WordTrace (prefixWord ++ tailWord_6419964) baseStart_6419964 baseEnd_6419964 := by
    simpa [prefixWord, tailWord_6419964, baseEnd_6419964] using wordTrace_append hprefix tailTrace_6419964
  have hstable : (prefixWord ++ tailWord_6419964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6419964).length < 2 ^ (prefixWord ++ tailWord_6419964).sum := by decide
  have hdescent : baseEnd_6419964 < baseStart_6419964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6419964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420037 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 1, 3, 4]
def baseStart_6420037 : Nat := 118140960795 + 6420037 * 2 ^ 59
def prefixEnd_6420037 : Nat := 4983230072969 + 3 ^ 40 * 6420037 * 2
def baseEnd_6420037 : Nat := 3296564800649203309412293

theorem tailTrace_6420037 : CollatzResearch.WordTrace tailWord_6420037 prefixEnd_6420037 3296564800649203309412293 := by
  unfold tailWord_6420037
  simp only [CollatzResearch.WordTrace]
  refine ⟨234157986242309878871466365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156105324161539919247644243 234157986242309878871466365)
  ·
    refine ⟨87809244840866204576799887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234157986242309878871466365 87809244840866204576799887)
    ·
      refine ⟨131713867261299306865199831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87809244840866204576799887 131713867261299306865199831)
      ·
        refine ⟨197570800891948960297799747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131713867261299306865199831 197570800891948960297799747)
        ·
          refine ⟨296356201337923440446699621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197570800891948960297799747 296356201337923440446699621)
          ·
            refine ⟨55566787750860645083756179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 296356201337923440446699621 55566787750860645083756179)
            ·
              refine ⟨83350181626290967625634269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55566787750860645083756179 83350181626290967625634269)
              ·
                refine ⟨31256318109859112859612851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83350181626290967625634269 31256318109859112859612851)
                ·
                  refine ⟨46884477164788669289419277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31256318109859112859612851 46884477164788669289419277)
                  ·
                    refine ⟨17581678936795750983532229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46884477164788669289419277 17581678936795750983532229)
                    ·
                      refine ⟨3296564800649203309412293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17581678936795750983532229 3296564800649203309412293)
                      ·
                        rfl

theorem cell23_6420037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 1, 3, 4].length) (baseStart_6420037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420037 prefixEnd_6420037 := by exact prefixLift 6420037
  have htrace : WordTrace (prefixWord ++ tailWord_6420037) baseStart_6420037 baseEnd_6420037 := by
    simpa [prefixWord, tailWord_6420037, baseEnd_6420037] using wordTrace_append hprefix tailTrace_6420037
  have hstable : (prefixWord ++ tailWord_6420037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420037).length < 2 ^ (prefixWord ++ tailWord_6420037).sum := by decide
  have hdescent : baseEnd_6420037 < baseStart_6420037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420117 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 2, 4, 5]
def baseStart_6420117 : Nat := 118140960795 + 6420117 * 2 ^ 59
def prefixEnd_6420117 : Nat := 4983230072969 + 3 ^ 40 * 6420117 * 2
def baseEnd_6420117 : Nat := 3296605879101562996411925

theorem tailTrace_6420117 : CollatzResearch.WordTrace tailWord_6420117 prefixEnd_6420117 3296605879101562996411925 := by
  unfold tailWord_6420117
  simp only [CollatzResearch.WordTrace]
  refine ⟨234160904082020052534378605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156107269388013368356252403 234160904082020052534378605)
  ·
    refine ⟨87810339030757519700391977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234160904082020052534378605 87810339030757519700391977)
    ·
      refine ⟨65857754273068139775293983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87810339030757519700391977 65857754273068139775293983)
      ·
        refine ⟨98786631409602209662940975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65857754273068139775293983 98786631409602209662940975)
        ·
          refine ⟨148179947114403314494411463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98786631409602209662940975 148179947114403314494411463)
          ·
            refine ⟨222269920671604971741617195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148179947114403314494411463 222269920671604971741617195)
            ·
              refine ⟨333404881007407457612425793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222269920671604971741617195 333404881007407457612425793)
              ·
                refine ⟨250053660755555593209319345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333404881007407457612425793 250053660755555593209319345)
                ·
                  refine ⟨187540245566666694906989509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250053660755555593209319345 187540245566666694906989509)
                  ·
                    refine ⟨35163796043750005295060533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187540245566666694906989509 35163796043750005295060533)
                    ·
                      refine ⟨3296605879101562996411925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35163796043750005295060533 3296605879101562996411925)
                      ·
                        rfl

theorem cell23_6420117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 4, 5].length) (baseStart_6420117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420117 prefixEnd_6420117 := by exact prefixLift 6420117
  have htrace : WordTrace (prefixWord ++ tailWord_6420117) baseStart_6420117 baseEnd_6420117 := by
    simpa [prefixWord, tailWord_6420117, baseEnd_6420117] using wordTrace_append hprefix tailTrace_6420117
  have hstable : (prefixWord ++ tailWord_6420117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420117).length < 2 ^ (prefixWord ++ tailWord_6420117).sum := by decide
  have hdescent : baseEnd_6420117 < baseStart_6420117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420141 : List Nat := [1, 5, 2, 1, 1, 1, 2, 4, 1, 5]
def baseStart_6420141 : Nat := 118140960795 + 6420141 * 2 ^ 59
def prefixEnd_6420141 : Nat := 4983230072969 + 3 ^ 40 * 6420141 * 2
def baseEnd_6420141 : Nat := 1098872734212423634170605

theorem tailTrace_6420141 : CollatzResearch.WordTrace tailWord_6420141 prefixEnd_6420141 1098872734212423634170605 := by
  unfold tailWord_6420141
  simp only [CollatzResearch.WordTrace]
  refine ⟨234161779433933104633252277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156107852955955403088834851 234161779433933104633252277)
  ·
    refine ⟨21952666821931228559367401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234161779433933104633252277 21952666821931228559367401)
    ·
      refine ⟨16464500116448421419525551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21952666821931228559367401 16464500116448421419525551)
      ·
        refine ⟨24696750174672632129288327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16464500116448421419525551 24696750174672632129288327)
        ·
          refine ⟨37045125262008948193932491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24696750174672632129288327 37045125262008948193932491)
          ·
            refine ⟨55567687893013422290898737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37045125262008948193932491 55567687893013422290898737)
            ·
              refine ⟨41675765919760066718174053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55567687893013422290898737 41675765919760066718174053)
              ·
                refine ⟨7814206109955012509657635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41675765919760066718174053 7814206109955012509657635)
                ·
                  refine ⟨11721309164932518764486453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7814206109955012509657635 11721309164932518764486453)
                  ·
                    refine ⟨1098872734212423634170605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11721309164932518764486453 1098872734212423634170605)
                    ·
                      rfl

theorem cell23_6420141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_6420141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420141 prefixEnd_6420141 := by exact prefixLift 6420141
  have htrace : WordTrace (prefixWord ++ tailWord_6420141) baseStart_6420141 baseEnd_6420141 := by
    simpa [prefixWord, tailWord_6420141, baseEnd_6420141] using wordTrace_append hprefix tailTrace_6420141
  have hstable : (prefixWord ++ tailWord_6420141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420141).length < 2 ^ (prefixWord ++ tailWord_6420141).sum := by decide
  have hdescent : baseEnd_6420141 < baseStart_6420141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420142 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_6420142 : Nat := 118140960795 + 6420142 * 2 ^ 59
def prefixEnd_6420142 : Nat := 4983230072969 + 3 ^ 40 * 6420142 * 2
def baseEnd_6420142 : Nat := 3296618716117925398599311

theorem tailTrace_6420142 : CollatzResearch.WordTrace tailWord_6420142 prefixEnd_6420142 3296618716117925398599311 := by
  unfold tailWord_6420142
  simp only [CollatzResearch.WordTrace]
  refine ⟨29270226988366185225504835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156107877271286321202692453 29270226988366185225504835)
  ·
    refine ⟨43905340482549277838257253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29270226988366185225504835 43905340482549277838257253)
    ·
      refine ⟨8232251340477989594673235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43905340482549277838257253 8232251340477989594673235)
      ·
        refine ⟨12348377010716984392009853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8232251340477989594673235 12348377010716984392009853)
        ·
          refine ⟨4630641379018869147003695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12348377010716984392009853 4630641379018869147003695)
          ·
            refine ⟨6945962068528303720505543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4630641379018869147003695 6945962068528303720505543)
            ·
              refine ⟨10418943102792455580758315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6945962068528303720505543 10418943102792455580758315)
              ·
                refine ⟨15628414654188683371137473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10418943102792455580758315 15628414654188683371137473)
                ·
                  refine ⟨11721310990641512528353105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15628414654188683371137473 11721310990641512528353105)
                  ·
                    refine ⟨8790983242981134396264829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11721310990641512528353105 8790983242981134396264829)
                    ·
                      refine ⟨3296618716117925398599311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8790983242981134396264829 3296618716117925398599311)
                      ·
                        rfl

theorem cell23_6420142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_6420142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420142 prefixEnd_6420142 := by exact prefixLift 6420142
  have htrace : WordTrace (prefixWord ++ tailWord_6420142) baseStart_6420142 baseEnd_6420142 := by
    simpa [prefixWord, tailWord_6420142, baseEnd_6420142] using wordTrace_append hprefix tailTrace_6420142
  have hstable : (prefixWord ++ tailWord_6420142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420142).length < 2 ^ (prefixWord ++ tailWord_6420142).sum := by decide
  have hdescent : baseEnd_6420142 < baseStart_6420142 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420144 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 4]
def baseStart_6420144 : Nat := 118140960795 + 6420144 * 2 ^ 59
def prefixEnd_6420144 : Nat := 4983230072969 + 3 ^ 40 * 6420144 * 2
def baseEnd_6420144 : Nat := 3296619743079234390774301

theorem tailTrace_6420144 : CollatzResearch.WordTrace tailWord_6420144 prefixEnd_6420144 3296619743079234390774301 := by
  unfold tailWord_6420144
  simp only [CollatzResearch.WordTrace]
  refine ⟨117080944426461118072805743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156107925901948157430407657 117080944426461118072805743)
  ·
    refine ⟨175621416639691677109208615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117080944426461118072805743 175621416639691677109208615)
    ·
      refine ⟨263432124959537515663812923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175621416639691677109208615 263432124959537515663812923)
      ·
        refine ⟨395148187439306273495719385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263432124959537515663812923 395148187439306273495719385)
        ·
          refine ⟨296361140579479705121789539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395148187439306273495719385 296361140579479705121789539)
          ·
            refine ⟨444541710869219557682684309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296361140579479705121789539 444541710869219557682684309)
            ·
              refine ⟨20837892696994666766375827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 444541710869219557682684309 20837892696994666766375827)
              ·
                refine ⟨31256839045492000149563741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20837892696994666766375827 31256839045492000149563741)
                ·
                  refine ⟨11721314642059500056086403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31256839045492000149563741 11721314642059500056086403)
                  ·
                    refine ⟨17581971963089250084129605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11721314642059500056086403 17581971963089250084129605)
                    ·
                      refine ⟨3296619743079234390774301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17581971963089250084129605 3296619743079234390774301)
                      ·
                        rfl

theorem cell23_6420144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 4].length) (baseStart_6420144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420144 prefixEnd_6420144 := by exact prefixLift 6420144
  have htrace : WordTrace (prefixWord ++ tailWord_6420144) baseStart_6420144 baseEnd_6420144 := by
    simpa [prefixWord, tailWord_6420144, baseEnd_6420144] using wordTrace_append hprefix tailTrace_6420144
  have hstable : (prefixWord ++ tailWord_6420144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420144).length < 2 ^ (prefixWord ++ tailWord_6420144).sum := by decide
  have hdescent : baseEnd_6420144 < baseStart_6420144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420154 : List Nat := [3, 1, 1, 1, 2, 4, 2, 2, 1, 6]
def baseStart_6420154 : Nat := 118140960795 + 6420154 * 2 ^ 59
def prefixEnd_6420154 : Nat := 4983230072969 + 3 ^ 40 * 6420154 * 2
def baseEnd_6420154 : Nat := 1098874959295259783883085

theorem tailTrace_6420154 : CollatzResearch.WordTrace tailWord_6420154 prefixEnd_6420154 1098874959295259783883085 := by
  unfold tailWord_6420154
  simp only [CollatzResearch.WordTrace]
  refine ⟨58540563395721501963368879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156108169055257338568983677 58540563395721501963368879)
  ·
    refine ⟨87810845093582252945053319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58540563395721501963368879 87810845093582252945053319)
    ·
      refine ⟨131716267640373379417579979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87810845093582252945053319 131716267640373379417579979)
      ·
        refine ⟨197574401460560069126369969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131716267640373379417579979 197574401460560069126369969)
        ·
          refine ⟨148180801095420051844777477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197574401460560069126369969 148180801095420051844777477)
          ·
            refine ⟨27783900205391259720895777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148180801095420051844777477 27783900205391259720895777)
            ·
              refine ⟨20837925154043444790671833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27783900205391259720895777 20837925154043444790671833)
              ·
                refine ⟨15628443865532583593003875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20837925154043444790671833 15628443865532583593003875)
                ·
                  refine ⟨23442665798298875389505813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15628443865532583593003875 23442665798298875389505813)
                  ·
                    refine ⟨1098874959295259783883085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23442665798298875389505813 1098874959295259783883085)
                    ·
                      rfl

theorem cell23_6420154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 2, 2, 1, 6].length) (baseStart_6420154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420154 prefixEnd_6420154 := by exact prefixLift 6420154
  have htrace : WordTrace (prefixWord ++ tailWord_6420154) baseStart_6420154 baseEnd_6420154 := by
    simpa [prefixWord, tailWord_6420154, baseEnd_6420154] using wordTrace_append hprefix tailTrace_6420154
  have hstable : (prefixWord ++ tailWord_6420154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420154).length < 2 ^ (prefixWord ++ tailWord_6420154).sum := by decide
  have hdescent : baseEnd_6420154 < baseStart_6420154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420158 : List Nat := [4, 2, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_6420158 : Nat := 118140960795 + 6420158 * 2 ^ 59
def prefixEnd_6420158 : Nat := 4983230072969 + 3 ^ 40 * 6420158 * 2
def baseEnd_6420158 : Nat := 1098875643936132445333079

theorem tailTrace_6420158 : CollatzResearch.WordTrace tailWord_6420158 prefixEnd_6420158 1098875643936132445333079 := by
  unfold tailWord_6420158
  simp only [CollatzResearch.WordTrace]
  refine ⟨29270299934358939567077641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156108266316581011024414085 29270299934358939567077641)
  ·
    refine ⟨21952724950769204675308231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29270299934358939567077641 21952724950769204675308231)
    ·
      refine ⟨32929087426153807012962347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21952724950769204675308231 32929087426153807012962347)
      ·
        refine ⟨49393631139230710519443521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32929087426153807012962347 49393631139230710519443521)
        ·
          refine ⟨37045223354423032889582641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49393631139230710519443521 37045223354423032889582641)
          ·
            refine ⟨27783917515817274667186981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37045223354423032889582641 27783917515817274667186981)
            ·
              refine ⟨5209484534215739000097559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27783917515817274667186981 5209484534215739000097559)
              ·
                refine ⟨7814226801323608500146339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5209484534215739000097559 7814226801323608500146339)
                ·
                  refine ⟨11721340201985412750219509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7814226801323608500146339 11721340201985412750219509)
                  ·
                    refine ⟨1098875643936132445333079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11721340201985412750219509 1098875643936132445333079)
                    ·
                      rfl

theorem cell23_6420158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_6420158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420158 prefixEnd_6420158 := by exact prefixLift 6420158
  have htrace : WordTrace (prefixWord ++ tailWord_6420158) baseStart_6420158 baseEnd_6420158 := by
    simpa [prefixWord, tailWord_6420158, baseEnd_6420158] using wordTrace_append hprefix tailTrace_6420158
  have hstable : (prefixWord ++ tailWord_6420158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420158).length < 2 ^ (prefixWord ++ tailWord_6420158).sum := by decide
  have hdescent : baseEnd_6420158 < baseStart_6420158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420162 : List Nat := [3, 5, 1, 2, 1, 2, 1, 2, 6]
def baseStart_6420162 : Nat := 118140960795 + 6420162 * 2 ^ 59
def prefixEnd_6420162 : Nat := 4983230072969 + 3 ^ 40 * 6420162 * 2
def baseEnd_6420162 : Nat := 366292109525668368927691

theorem tailTrace_6420162 : CollatzResearch.WordTrace tailWord_6420162 prefixEnd_6420162 366292109525668368927691 := by
  unfold tailWord_6420162
  simp only [CollatzResearch.WordTrace]
  refine ⟨58540636341714256304941685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156108363577904683479844493 58540636341714256304941685)
  ·
    refine ⟨5488184657035711528588283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58540636341714256304941685 5488184657035711528588283)
    ·
      refine ⟨8232276985553567292882425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5488184657035711528588283 8232276985553567292882425)
      ·
        refine ⟨6174207739165175469661819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8232276985553567292882425 6174207739165175469661819)
        ·
          refine ⟨9261311608747763204492729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6174207739165175469661819 9261311608747763204492729)
          ·
            refine ⟨6945983706560822403369547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9261311608747763204492729 6945983706560822403369547)
            ·
              refine ⟨10418975559841233605054321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6945983706560822403369547 10418975559841233605054321)
              ·
                refine ⟨7814231669880925203790741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10418975559841233605054321 7814231669880925203790741)
                ·
                  refine ⟨366292109525668368927691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7814231669880925203790741 366292109525668368927691)
                  ·
                    rfl

theorem cell23_6420162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_6420162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420162 prefixEnd_6420162 := by exact prefixLift 6420162
  have htrace : WordTrace (prefixWord ++ tailWord_6420162) baseStart_6420162 baseEnd_6420162 := by
    simpa [prefixWord, tailWord_6420162, baseEnd_6420162] using wordTrace_append hprefix tailTrace_6420162
  have hstable : (prefixWord ++ tailWord_6420162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420162).length < 2 ^ (prefixWord ++ tailWord_6420162).sum := by decide
  have hdescent : baseEnd_6420162 < baseStart_6420162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420167 : List Nat := [1, 1, 4, 1, 1, 1, 14]
def baseStart_6420167 : Nat := 118140960795 + 6420167 * 2 ^ 59
def prefixEnd_6420167 : Nat := 4983230072969 + 3 ^ 40 * 6420167 * 2
def baseEnd_6420167 : Nat := 40699154976966516059095

theorem tailTrace_6420167 : CollatzResearch.WordTrace tailWord_6420167 prefixEnd_6420167 40699154976966516059095 := by
  unfold tailWord_6420167
  simp only [CollatzResearch.WordTrace]
  refine ⟨234162727731838911073698755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156108485154559274049132503 234162727731838911073698755)
  ·
    refine ⟨351244091597758366610548133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234162727731838911073698755 351244091597758366610548133)
    ·
      refine ⟨65858267174579693739477775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 351244091597758366610548133 65858267174579693739477775)
      ·
        refine ⟨98787400761869540609216663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65858267174579693739477775 98787400761869540609216663)
        ·
          refine ⟨148181101142804310913824995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98787400761869540609216663 148181101142804310913824995)
          ·
            refine ⟨222271651714206466370737493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148181101142804310913824995 222271651714206466370737493)
            ·
              refine ⟨40699154976966516059095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 222271651714206466370737493 40699154976966516059095)
              ·
                rfl

theorem cell23_6420167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 14].length) (baseStart_6420167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420167 prefixEnd_6420167 := by exact prefixLift 6420167
  have htrace : WordTrace (prefixWord ++ tailWord_6420167) baseStart_6420167 baseEnd_6420167 := by
    simpa [prefixWord, tailWord_6420167, baseEnd_6420167] using wordTrace_append hprefix tailTrace_6420167
  have hstable : (prefixWord ++ tailWord_6420167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420167).length < 2 ^ (prefixWord ++ tailWord_6420167).sum := by decide
  have hdescent : baseEnd_6420167 < baseStart_6420167 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420174 : List Nat := [4, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6]
def baseStart_6420174 : Nat := 118140960795 + 6420174 * 2 ^ 59
def prefixEnd_6420174 : Nat := 4983230072969 + 3 ^ 40 * 6420174 * 2
def baseEnd_6420174 : Nat := 3296635147498869273399163

theorem tailTrace_6420174 : CollatzResearch.WordTrace tailWord_6420174 prefixEnd_6420174 3296635147498869273399163 := by
  unfold tailWord_6420174
  simp only [CollatzResearch.WordTrace]
  refine ⟨29270372880351693908650447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156108655361875700846135717 29270372880351693908650447)
  ·
    refine ⟨43905559320527540862975671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29270372880351693908650447 43905559320527540862975671)
    ·
      refine ⟨65858338980791311294463507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43905559320527540862975671 65858338980791311294463507)
      ·
        refine ⟨98787508471186966941695261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65858338980791311294463507 98787508471186966941695261)
        ·
          refine ⟨37045315676695112603135723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98787508471186966941695261 37045315676695112603135723)
          ·
            refine ⟨55567973515042668904703585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37045315676695112603135723 55567973515042668904703585)
            ·
              refine ⟨41675980136282001678527689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55567973515042668904703585 41675980136282001678527689)
              ·
                refine ⟨31256985102211501258895767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41675980136282001678527689 31256985102211501258895767)
                ·
                  refine ⟨46885477653317251888343651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31256985102211501258895767 46885477653317251888343651)
                  ·
                    refine ⟨70328216479975877832515477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46885477653317251888343651 70328216479975877832515477)
                    ·
                      refine ⟨3296635147498869273399163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70328216479975877832515477 3296635147498869273399163)
                      ·
                        rfl

theorem cell23_6420174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6].length) (baseStart_6420174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420174 prefixEnd_6420174 := by exact prefixLift 6420174
  have htrace : WordTrace (prefixWord ++ tailWord_6420174) baseStart_6420174 baseEnd_6420174 := by
    simpa [prefixWord, tailWord_6420174, baseEnd_6420174] using wordTrace_append hprefix tailTrace_6420174
  have hstable : (prefixWord ++ tailWord_6420174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420174).length < 2 ^ (prefixWord ++ tailWord_6420174).sum := by decide
  have hdescent : baseEnd_6420174 < baseStart_6420174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420211 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 4, 1, 3]
def baseStart_6420211 : Nat := 118140960795 + 6420211 * 2 ^ 59
def prefixEnd_6420211 : Nat := 4983230072969 + 3 ^ 40 * 6420211 * 2
def baseEnd_6420211 : Nat := 3296654146283085628636493

theorem tailTrace_6420211 : CollatzResearch.WordTrace tailWord_6420211 prefixEnd_6420211 3296654146283085628636493 := by
  unfold tailWord_6420211
  simp only [CollatzResearch.WordTrace]
  refine ⟨234164332543679506588300487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156109555029119671058866991 234164332543679506588300487)
  ·
    refine ⟨351246498815519259882450731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234164332543679506588300487 351246498815519259882450731)
    ·
      refine ⟨526869748223278889823676097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351246498815519259882450731 526869748223278889823676097)
      ·
        refine ⟨395152311167459167367757073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526869748223278889823676097 395152311167459167367757073)
        ·
          refine ⟨296364233375594375525817805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395152311167459167367757073 296364233375594375525817805)
          ·
            refine ⟨111136587515847890822181677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296364233375594375525817805 111136587515847890822181677)
            ·
              refine ⟨41676220318442959058318129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111136587515847890822181677 41676220318442959058318129)
              ·
                refine ⟨31257165238832219293738597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41676220318442959058318129 31257165238832219293738597)
                ·
                  refine ⟨5860718482281041117575987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31257165238832219293738597 5860718482281041117575987)
                  ·
                    refine ⟨8791077723421561676363981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5860718482281041117575987 8791077723421561676363981)
                    ·
                      refine ⟨3296654146283085628636493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8791077723421561676363981 3296654146283085628636493)
                      ·
                        rfl

theorem cell23_6420211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 4, 1, 3].length) (baseStart_6420211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420211 prefixEnd_6420211 := by exact prefixLift 6420211
  have htrace : WordTrace (prefixWord ++ tailWord_6420211) baseStart_6420211 baseEnd_6420211 := by
    simpa [prefixWord, tailWord_6420211, baseEnd_6420211] using wordTrace_append hprefix tailTrace_6420211
  have hstable : (prefixWord ++ tailWord_6420211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420211).length < 2 ^ (prefixWord ++ tailWord_6420211).sum := by decide
  have hdescent : baseEnd_6420211 < baseStart_6420211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420228 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 4, 1, 3]
def baseStart_6420228 : Nat := 118140960795 + 6420228 * 2 ^ 59
def prefixEnd_6420228 : Nat := 4983230072969 + 3 ^ 40 * 6420228 * 2
def baseEnd_6420228 : Nat := 3296662875454212062123915

theorem tailTrace_6420228 : CollatzResearch.WordTrace tailWord_6420228 prefixEnd_6420228 3296662875454212062123915 := by
  unfold tailWord_6420228
  simp only [CollatzResearch.WordTrace]
  refine ⟨117082476292308959245834669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156109968389745278994446225 117082476292308959245834669)
  ·
    refine ⟨43905928609615859717188001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117082476292308959245834669 43905928609615859717188001)
    ·
      refine ⟨32929446457211894787891001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43905928609615859717188001 32929446457211894787891001)
      ·
        refine ⟨24697084842908921090918251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32929446457211894787891001 24697084842908921090918251)
        ·
          refine ⟨37045627264363381636377377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24697084842908921090918251 37045627264363381636377377)
          ·
            refine ⟨27784220448272536227283033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37045627264363381636377377 27784220448272536227283033)
            ·
              refine ⟨20838165336204402170462275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27784220448272536227283033 20838165336204402170462275)
              ·
                refine ⟨31257248004306603255693413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20838165336204402170462275 31257248004306603255693413)
                ·
                  refine ⟨5860734000807488110442515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31257248004306603255693413 5860734000807488110442515)
                  ·
                    refine ⟨8791101001211232165663773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5860734000807488110442515 8791101001211232165663773)
                    ·
                      refine ⟨3296662875454212062123915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8791101001211232165663773 3296662875454212062123915)
                      ·
                        rfl

theorem cell23_6420228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_6420228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420228 prefixEnd_6420228 := by exact prefixLift 6420228
  have htrace : WordTrace (prefixWord ++ tailWord_6420228) baseStart_6420228 baseEnd_6420228 := by
    simpa [prefixWord, tailWord_6420228, baseEnd_6420228] using wordTrace_append hprefix tailTrace_6420228
  have hstable : (prefixWord ++ tailWord_6420228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420228).length < 2 ^ (prefixWord ++ tailWord_6420228).sum := by decide
  have hdescent : baseEnd_6420228 < baseStart_6420228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420245 : List Nat := [1, 3, 2, 1, 2, 3, 4, 1, 2, 1, 3]
def baseStart_6420245 : Nat := 118140960795 + 6420245 * 2 ^ 59
def prefixEnd_6420245 : Nat := 4983230072969 + 3 ^ 40 * 6420245 * 2
def baseEnd_6420245 : Nat := 3296671604625338495611337

theorem tailTrace_6420245 : CollatzResearch.WordTrace tailWord_6420245 prefixEnd_6420245 3296671604625338495611337 := by
  unfold tailWord_6420245
  simp only [CollatzResearch.WordTrace]
  refine ⟨234165572625556330395038189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156110381750370886930025459 234165572625556330395038189)
  ·
    refine ⟨87812089734583623898139321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234165572625556330395038189 87812089734583623898139321)
    ·
      refine ⟨65859067300937717923604491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87812089734583623898139321 65859067300937717923604491)
      ·
        refine ⟨98788600951406576885406737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65859067300937717923604491 98788600951406576885406737)
        ·
          refine ⟨74091450713554932664055053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98788600951406576885406737 74091450713554932664055053)
          ·
            refine ⟨27784294017583099749020645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74091450713554932664055053 27784294017583099749020645)
            ·
              refine ⟨5209555128296831202941371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27784294017583099749020645 5209555128296831202941371)
              ·
                refine ⟨7814332692445246804412057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5209555128296831202941371 7814332692445246804412057)
                ·
                  refine ⟨5860749519333935103309043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7814332692445246804412057 5860749519333935103309043)
                  ·
                    refine ⟨8791124279000902654963565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5860749519333935103309043 8791124279000902654963565)
                    ·
                      refine ⟨3296671604625338495611337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8791124279000902654963565 3296671604625338495611337)
                      ·
                        rfl

theorem cell23_6420245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 2, 1, 3].length) (baseStart_6420245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420245 prefixEnd_6420245 := by exact prefixLift 6420245
  have htrace : WordTrace (prefixWord ++ tailWord_6420245) baseStart_6420245 baseEnd_6420245 := by
    simpa [prefixWord, tailWord_6420245, baseEnd_6420245] using wordTrace_append hprefix tailTrace_6420245
  have hstable : (prefixWord ++ tailWord_6420245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420245).length < 2 ^ (prefixWord ++ tailWord_6420245).sum := by decide
  have hdescent : baseEnd_6420245 < baseStart_6420245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420268 : List Nat := [2, 2, 1, 1, 1, 6, 1, 2, 1, 4, 2]
def baseStart_6420268 : Nat := 118140960795 + 6420268 * 2 ^ 59
def prefixEnd_6420268 : Nat := 4983230072969 + 3 ^ 40 * 6420268 * 2
def baseEnd_6420268 : Nat := 3296683414680391905623731

theorem tailTrace_6420268 : CollatzResearch.WordTrace tailWord_6420268 prefixEnd_6420268 3296683414680391905623731 := by
  unfold tailWord_6420268
  simp only [CollatzResearch.WordTrace]
  refine ⟨117083205752236502661562729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156110941002982003548750305 117083205752236502661562729)
  ·
    refine ⟨87812404314177376996172047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117083205752236502661562729 87812404314177376996172047)
    ·
      refine ⟨131718606471266065494258071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87812404314177376996172047 131718606471266065494258071)
      ·
        refine ⟨197577909706899098241387107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131718606471266065494258071 197577909706899098241387107)
        ·
          refine ⟨296366864560348647362080661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197577909706899098241387107 296366864560348647362080661)
          ·
            refine ⟨13892196776266342845097531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 296366864560348647362080661 13892196776266342845097531)
            ·
              refine ⟨20838295164399514267646297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13892196776266342845097531 20838295164399514267646297)
              ·
                refine ⟨15628721373299635700734723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20838295164399514267646297 15628721373299635700734723)
                ·
                  refine ⟨23443082059949453551102085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15628721373299635700734723 23443082059949453551102085)
                  ·
                    refine ⟨4395577886240522540831641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23443082059949453551102085 4395577886240522540831641)
                    ·
                      refine ⟨3296683414680391905623731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4395577886240522540831641 3296683414680391905623731)
                      ·
                        rfl

theorem cell23_6420268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 4, 2].length) (baseStart_6420268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420268 prefixEnd_6420268 := by exact prefixLift 6420268
  have htrace : WordTrace (prefixWord ++ tailWord_6420268) baseStart_6420268 baseEnd_6420268 := by
    simpa [prefixWord, tailWord_6420268, baseEnd_6420268] using wordTrace_append hprefix tailTrace_6420268
  have hstable : (prefixWord ++ tailWord_6420268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420268).length < 2 ^ (prefixWord ++ tailWord_6420268).sum := by decide
  have hdescent : baseEnd_6420268 < baseStart_6420268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420284 : List Nat := [2, 2, 2, 2, 1, 1, 2, 1, 1, 2, 7]
def baseStart_6420284 : Nat := 118140960795 + 6420284 * 2 ^ 59
def prefixEnd_6420284 : Nat := 4983230072969 + 3 ^ 40 * 6420284 * 2
def baseEnd_6420284 : Nat := 3296691630370863843023657

theorem tailTrace_6420284 : CollatzResearch.WordTrace tailWord_6420284 prefixEnd_6420284 3296691630370863843023657 := by
  unfold tailWord_6420284
  simp only [CollatzResearch.WordTrace]
  refine ⟨117083497536207520027853953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156111330048276693370471937 117083497536207520027853953)
  ·
    refine ⟨87812623152155640020890465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117083497536207520027853953 87812623152155640020890465)
    ·
      refine ⟨65859467364116730015667849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87812623152155640020890465 65859467364116730015667849)
      ·
        refine ⟨49394600523087547511750887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65859467364116730015667849 49394600523087547511750887)
        ·
          refine ⟨74091900784631321267626331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49394600523087547511750887 74091900784631321267626331)
          ·
            refine ⟨111137851176946981901439497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74091900784631321267626331 111137851176946981901439497)
            ·
              refine ⟨83353388382710236426079623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111137851176946981901439497 83353388382710236426079623)
              ·
                refine ⟨125030082574065354639119435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83353388382710236426079623 125030082574065354639119435)
                ·
                  refine ⟨187545123861098031958679153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125030082574065354639119435 187545123861098031958679153)
                  ·
                    refine ⟨140658842895823523969009365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 187545123861098031958679153 140658842895823523969009365)
                    ·
                      refine ⟨3296691630370863843023657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140658842895823523969009365 3296691630370863843023657)
                      ·
                        rfl

theorem cell23_6420284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 1, 2, 7].length) (baseStart_6420284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420284 prefixEnd_6420284 := by exact prefixLift 6420284
  have htrace : WordTrace (prefixWord ++ tailWord_6420284) baseStart_6420284 baseEnd_6420284 := by
    simpa [prefixWord, tailWord_6420284, baseEnd_6420284] using wordTrace_append hprefix tailTrace_6420284
  have hstable : (prefixWord ++ tailWord_6420284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420284).length < 2 ^ (prefixWord ++ tailWord_6420284).sum := by decide
  have hdescent : baseEnd_6420284 < baseStart_6420284 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420304 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 1, 7]
def baseStart_6420304 : Nat := 118140960795 + 6420304 * 2 ^ 59
def prefixEnd_6420304 : Nat := 4983230072969 + 3 ^ 40 * 6420304 * 2
def baseEnd_6420304 : Nat := 1098900633327984588257855

theorem tailTrace_6420304 : CollatzResearch.WordTrace tailWord_6420304 prefixEnd_6420304 1098900633327984588257855 := by
  unfold tailWord_6420304
  simp only [CollatzResearch.WordTrace]
  refine ⟨117083862266171291735717983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156111816354895055647623977 117083862266171291735717983)
  ·
    refine ⟨175625793399256937603576975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117083862266171291735717983 175625793399256937603576975)
    ·
      refine ⟨263438690098885406405365463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175625793399256937603576975 263438690098885406405365463)
      ·
        refine ⟨395158035148328109608048195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263438690098885406405365463 395158035148328109608048195)
        ·
          refine ⟨592737052722492164412072293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395158035148328109608048195 592737052722492164412072293)
          ·
            refine ⟨111138197385467280827263555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 592737052722492164412072293 111138197385467280827263555)
            ·
              refine ⟨166707296078200921240895333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111138197385467280827263555 166707296078200921240895333)
              ·
                refine ⟨31257618014662672732667875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166707296078200921240895333 31257618014662672732667875)
                ·
                  refine ⟨46886427021994009099001813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31257618014662672732667875 46886427021994009099001813)
                  ·
                    refine ⟨1098900633327984588257855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46886427021994009099001813 1098900633327984588257855)
                    ·
                      rfl

theorem cell23_6420304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 1, 7].length) (baseStart_6420304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420304 prefixEnd_6420304 := by exact prefixLift 6420304
  have htrace : WordTrace (prefixWord ++ tailWord_6420304) baseStart_6420304 baseEnd_6420304 := by
    simpa [prefixWord, tailWord_6420304, baseEnd_6420304] using wordTrace_append hprefix tailTrace_6420304
  have hstable : (prefixWord ++ tailWord_6420304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420304).length < 2 ^ (prefixWord ++ tailWord_6420304).sum := by decide
  have hdescent : baseEnd_6420304 < baseStart_6420304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420361 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 3, 4, 3]
def baseStart_6420361 : Nat := 118140960795 + 6420361 * 2 ^ 59
def prefixEnd_6420361 : Nat := 4983230072969 + 3 ^ 40 * 6420361 * 2
def baseEnd_6420361 : Nat := 3296731168381260041760803

theorem tailTrace_6420361 : CollatzResearch.WordTrace tailWord_6420361 prefixEnd_6420361 3296731168381260041760803 := by
  unfold tailWord_6420361
  simp only [CollatzResearch.WordTrace]
  refine ⟨234169803493136082206260937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156113202328757388137507291 234169803493136082206260937)
  ·
    refine ⟨175627352619852061654695703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234169803493136082206260937 175627352619852061654695703)
    ·
      refine ⟨263441028929778092482043555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175627352619852061654695703 263441028929778092482043555)
      ·
        refine ⟨395161543394667138723065333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263441028929778092482043555 395161543394667138723065333)
        ·
          refine ⟨37046394693250044255287375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 395161543394667138723065333 37046394693250044255287375)
          ·
            refine ⟨55569592039875066382931063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37046394693250044255287375 55569592039875066382931063)
            ·
              refine ⟨83354388059812599574396595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55569592039875066382931063 83354388059812599574396595)
              ·
                refine ⟨125031582089718899361594893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83354388059812599574396595 125031582089718899361594893)
                ·
                  refine ⟨46886843283644587260598085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125031582089718899361594893 46886843283644587260598085)
                  ·
                    refine ⟨8791283115683360111362141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46886843283644587260598085 8791283115683360111362141)
                    ·
                      refine ⟨3296731168381260041760803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8791283115683360111362141 3296731168381260041760803)
                      ·
                        rfl

theorem cell23_6420361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 4, 3].length) (baseStart_6420361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420361 prefixEnd_6420361 := by exact prefixLift 6420361
  have htrace : WordTrace (prefixWord ++ tailWord_6420361) baseStart_6420361 baseEnd_6420361 := by
    simpa [prefixWord, tailWord_6420361, baseEnd_6420361] using wordTrace_append hprefix tailTrace_6420361
  have hstable : (prefixWord ++ tailWord_6420361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420361).length < 2 ^ (prefixWord ++ tailWord_6420361).sum := by decide
  have hdescent : baseEnd_6420361 < baseStart_6420361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420378 : List Nat := [3, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3]
def baseStart_6420378 : Nat := 118140960795 + 6420378 * 2 ^ 59
def prefixEnd_6420378 : Nat := 4983230072969 + 3 ^ 40 * 6420378 * 2
def baseEnd_6420378 : Nat := 3296739897552386475248225

theorem tailTrace_6420378 : CollatzResearch.WordTrace tailWord_6420378 prefixEnd_6420378 3296739897552386475248225 := by
  unfold tailWord_6420378
  simp only [CollatzResearch.WordTrace]
  refine ⟨58542605883518623527407447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156113615689382996073086525 58542605883518623527407447)
  ·
    refine ⟨87813908825277935291111171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58542605883518623527407447 87813908825277935291111171)
    ·
      refine ⟨131720863237916902936666757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87813908825277935291111171 131720863237916902936666757)
      ·
        refine ⟨24697661857109419300625017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131720863237916902936666757 24697661857109419300625017)
        ·
          refine ⟨18523246392832064475468763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24697661857109419300625017 18523246392832064475468763)
          ·
            refine ⟨27784869589248096713203145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18523246392832064475468763 27784869589248096713203145)
            ·
              refine ⟨20838652191936072534902359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27784869589248096713203145 20838652191936072534902359)
              ·
                refine ⟨31257978287904108802353539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20838652191936072534902359 31257978287904108802353539)
                ·
                  refine ⟨46886967431856163203530309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31257978287904108802353539 46886967431856163203530309)
                  ·
                    refine ⟨8791306393473030600661933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46886967431856163203530309 8791306393473030600661933)
                    ·
                      refine ⟨3296739897552386475248225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8791306393473030600661933 3296739897552386475248225)
                      ·
                        rfl

theorem cell23_6420378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_6420378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420378 prefixEnd_6420378 := by exact prefixLift 6420378
  have htrace : WordTrace (prefixWord ++ tailWord_6420378) baseStart_6420378 baseEnd_6420378 := by
    simpa [prefixWord, tailWord_6420378, baseEnd_6420378] using wordTrace_append hprefix tailTrace_6420378
  have hstable : (prefixWord ++ tailWord_6420378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420378).length < 2 ^ (prefixWord ++ tailWord_6420378).sum := by decide
  have hdescent : baseEnd_6420378 < baseStart_6420378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420381 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 8]
def baseStart_6420381 : Nat := 118140960795 + 6420381 * 2 ^ 59
def prefixEnd_6420381 : Nat := 4983230072969 + 3 ^ 40 * 6420381 * 2
def baseEnd_6420381 : Nat := 366304604221594440390079

theorem tailTrace_6420381 : CollatzResearch.WordTrace tailWord_6420381 prefixEnd_6420381 366304604221594440390079 := by
  unfold tailWord_6420381
  simp only [CollatzResearch.WordTrace]
  refine ⟨234170532953063625621988997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156113688635375750414659331 234170532953063625621988997)
  ·
    refine ⟨43906974928699429804122937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234170532953063625621988997 43906974928699429804122937)
    ·
      refine ⟨32930231196524572353092203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43906974928699429804122937 32930231196524572353092203)
      ·
        refine ⟨49395346794786858529638305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32930231196524572353092203 49395346794786858529638305)
        ·
          refine ⟨37046510096090143897228729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49395346794786858529638305 37046510096090143897228729)
          ·
            refine ⟨27784882572067607922921547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37046510096090143897228729 27784882572067607922921547)
            ·
              refine ⟨41677323858101411884382321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27784882572067607922921547 41677323858101411884382321)
              ·
                refine ⟨31257992893576058913286741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41677323858101411884382321 31257992893576058913286741)
                ·
                  refine ⟨366304604221594440390079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31257992893576058913286741 366304604221594440390079)
                  ·
                    rfl

theorem cell23_6420381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 8].length) (baseStart_6420381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420381 prefixEnd_6420381 := by exact prefixLift 6420381
  have htrace : WordTrace (prefixWord ++ tailWord_6420381) baseStart_6420381 baseEnd_6420381 := by
    simpa [prefixWord, tailWord_6420381, baseEnd_6420381] using wordTrace_append hprefix tailTrace_6420381
  have hstable : (prefixWord ++ tailWord_6420381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420381).length < 2 ^ (prefixWord ++ tailWord_6420381).sum := by decide
  have hdescent : baseEnd_6420381 < baseStart_6420381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420392 : List Nat := [2, 1, 6, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_6420392 : Nat := 118140960795 + 6420392 * 2 ^ 59
def prefixEnd_6420392 : Nat := 4983230072969 + 3 ^ 40 * 6420392 * 2
def baseEnd_6420392 : Nat := 3296747086281549420473161

theorem tailTrace_6420392 : CollatzResearch.WordTrace tailWord_6420392 prefixEnd_6420392 3296747086281549420473161 := by
  unfold tailWord_6420392
  simp only [CollatzResearch.WordTrace]
  refine ⟨117085467078011887250319715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156113956104015849667092953 117085467078011887250319715)
  ·
    refine ⟨175628200617017830875479573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117085467078011887250319715 175628200617017830875479573)
    ·
      refine ⟨8232571903922710822288105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 175628200617017830875479573 8232571903922710822288105)
      ·
        refine ⟨6174428927942033116716079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8232571903922710822288105 6174428927942033116716079)
        ·
          refine ⟨9261643391913049675074119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6174428927942033116716079 9261643391913049675074119)
          ·
            refine ⟨13892465087869574512611179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9261643391913049675074119 13892465087869574512611179)
            ·
              refine ⟨20838697631804361768916769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13892465087869574512611179 20838697631804361768916769)
              ·
                refine ⟨15629023223853271326687577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20838697631804361768916769 15629023223853271326687577)
                ·
                  refine ⟨11721767417889953495015683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15629023223853271326687577 11721767417889953495015683)
                  ·
                    refine ⟨17582651126834930242523525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11721767417889953495015683 17582651126834930242523525)
                    ·
                      refine ⟨3296747086281549420473161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17582651126834930242523525 3296747086281549420473161)
                      ·
                        rfl

theorem cell23_6420392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_6420392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420392 prefixEnd_6420392 := by exact prefixLift 6420392
  have htrace : WordTrace (prefixWord ++ tailWord_6420392) baseStart_6420392 baseEnd_6420392 := by
    simpa [prefixWord, tailWord_6420392, baseEnd_6420392] using wordTrace_append hprefix tailTrace_6420392
  have hstable : (prefixWord ++ tailWord_6420392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420392).length < 2 ^ (prefixWord ++ tailWord_6420392).sum := by decide
  have hdescent : baseEnd_6420392 < baseStart_6420392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420428 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 3, 5]
def baseStart_6420428 : Nat := 118140960795 + 6420428 * 2 ^ 59
def prefixEnd_6420428 : Nat := 4983230072969 + 3 ^ 40 * 6420428 * 2
def baseEnd_6420428 : Nat := 1098921857195037093207665

theorem tailTrace_6420428 : CollatzResearch.WordTrace tailWord_6420428 prefixEnd_6420428 1098921857195037093207665 := by
  unfold tailWord_6420428
  simp only [CollatzResearch.WordTrace]
  refine ⟨117086123591946676324474969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156114831455928901765966625 117086123591946676324474969)
  ·
    refine ⟨87814592693960007243356227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117086123591946676324474969 87814592693960007243356227)
    ·
      refine ⟨131721889040940010865034341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87814592693960007243356227 131721889040940010865034341)
      ·
        refine ⟨24697854195176252037193939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131721889040940010865034341 24697854195176252037193939)
        ·
          refine ⟨37046781292764378055790909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24697854195176252037193939 37046781292764378055790909)
          ·
            refine ⟨13892542984786641770921591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37046781292764378055790909 13892542984786641770921591)
            ·
              refine ⟨20838814477179962656382387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13892542984786641770921591 20838814477179962656382387)
              ·
                refine ⟨31258221715769943984573581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20838814477179962656382387 31258221715769943984573581)
                ·
                  refine ⟨11721833143413728994215093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31258221715769943984573581 11721833143413728994215093)
                  ·
                    refine ⟨1098921857195037093207665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11721833143413728994215093 1098921857195037093207665)
                    ·
                      rfl

theorem cell23_6420428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_6420428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420428 prefixEnd_6420428 := by exact prefixLift 6420428
  have htrace : WordTrace (prefixWord ++ tailWord_6420428) baseStart_6420428 baseEnd_6420428 := by
    simpa [prefixWord, tailWord_6420428, baseEnd_6420428] using wordTrace_append hprefix tailTrace_6420428
  have hstable : (prefixWord ++ tailWord_6420428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420428).length < 2 ^ (prefixWord ++ tailWord_6420428).sum := by decide
  have hdescent : baseEnd_6420428 < baseStart_6420428 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420448 : List Nat := [2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 4]
def baseStart_6420448 : Nat := 118140960795 + 6420448 * 2 ^ 59
def prefixEnd_6420448 : Nat := 4983230072969 + 3 ^ 40 * 6420448 * 2
def baseEnd_6420448 : Nat := 3296775841198201201372903

theorem tailTrace_6420448 : CollatzResearch.WordTrace tailWord_6420448 prefixEnd_6420448 3296775841198201201372903 := by
  unfold tailWord_6420448
  simp only [CollatzResearch.WordTrace]
  refine ⟨117086488321910448032338999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156115317762547264043118665 117086488321910448032338999)
  ·
    refine ⟨175629732482865672048508499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117086488321910448032338999 175629732482865672048508499)
    ·
      refine ⟨263444598724298508072762749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175629732482865672048508499 263444598724298508072762749)
      ·
        refine ⟨98791724521611940527286031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263444598724298508072762749 98791724521611940527286031)
        ·
          refine ⟨148187586782417910790929047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98791724521611940527286031 148187586782417910790929047)
          ·
            refine ⟨222281380173626866186393571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148187586782417910790929047 222281380173626866186393571)
            ·
              refine ⟨333422070260440299279590357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222281380173626866186393571 333422070260440299279590357)
              ·
                refine ⟨7814579771729069514365399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 333422070260440299279590357 7814579771729069514365399)
                ·
                  refine ⟨11721869657593604271548099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7814579771729069514365399 11721869657593604271548099)
                  ·
                    refine ⟨17582804486390406407322149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11721869657593604271548099 17582804486390406407322149)
                    ·
                      refine ⟨3296775841198201201372903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17582804486390406407322149 3296775841198201201372903)
                      ·
                        rfl

theorem cell23_6420448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_6420448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420448 prefixEnd_6420448 := by exact prefixLift 6420448
  have htrace : WordTrace (prefixWord ++ tailWord_6420448) baseStart_6420448 baseEnd_6420448 := by
    simpa [prefixWord, tailWord_6420448, baseEnd_6420448] using wordTrace_append hprefix tailTrace_6420448
  have hstable : (prefixWord ++ tailWord_6420448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420448).length < 2 ^ (prefixWord ++ tailWord_6420448).sum := by decide
  have hdescent : baseEnd_6420448 < baseStart_6420448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420488 : List Nat := [2, 1, 3, 2, 1, 2, 5, 7]
def baseStart_6420488 : Nat := 118140960795 + 6420488 * 2 ^ 59
def prefixEnd_6420488 : Nat := 4983230072969 + 3 ^ 40 * 6420488 * 2
def baseEnd_6420488 : Nat := 122103569645347446106397

theorem tailTrace_6420488 : CollatzResearch.WordTrace tailWord_6420488 prefixEnd_6420488 122103569645347446106397 := by
  unfold tailWord_6420488
  simp only [CollatzResearch.WordTrace]
  refine ⟨117087217781837991448067059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156116290375783988597422745 117087217781837991448067059)
  ·
    refine ⟨175630826672756987172100589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117087217781837991448067059 175630826672756987172100589)
    ·
      refine ⟨65861560002283870189537721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175630826672756987172100589 65861560002283870189537721)
      ·
        refine ⟨49396170001712902642153291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65861560002283870189537721 49396170001712902642153291)
        ·
          refine ⟨74094255002569353963229937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49396170001712902642153291 74094255002569353963229937)
          ·
            refine ⟨55570691251927015472422453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74094255002569353963229937 55570691251927015472422453)
            ·
              refine ⟨5209752304868157700539605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55570691251927015472422453 5209752304868157700539605)
              ·
                refine ⟨122103569645347446106397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5209752304868157700539605 122103569645347446106397)
                ·
                  rfl

theorem cell23_6420488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 5, 7].length) (baseStart_6420488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420488 prefixEnd_6420488 := by exact prefixLift 6420488
  have htrace : WordTrace (prefixWord ++ tailWord_6420488) baseStart_6420488 baseEnd_6420488 := by
    simpa [prefixWord, tailWord_6420488, baseEnd_6420488] using wordTrace_append hprefix tailTrace_6420488
  have hstable : (prefixWord ++ tailWord_6420488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420488).length < 2 ^ (prefixWord ++ tailWord_6420488).sum := by decide
  have hdescent : baseEnd_6420488 < baseStart_6420488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420515 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 4, 1, 3]
def baseStart_6420515 : Nat := 118140960795 + 6420515 * 2 ^ 59
def prefixEnd_6420515 : Nat := 4983230072969 + 3 ^ 40 * 6420515 * 2
def baseEnd_6420515 : Nat := 3296810244402052439235095

theorem tailTrace_6420515 : CollatzResearch.WordTrace tailWord_6420515 prefixEnd_6420515 3296810244402052439235095 := by
  unfold tailWord_6420515
  simp only [CollatzResearch.WordTrace]
  refine ⟨234175420334578166507366999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156116946889718777671577999 234175420334578166507366999)
  ·
    refine ⟨351263130501867249761050499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234175420334578166507366999 351263130501867249761050499)
    ·
      refine ⟨526894695752800874641575749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351263130501867249761050499 526894695752800874641575749)
      ·
        refine ⟨98792755453650163995295453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 526894695752800874641575749 98792755453650163995295453)
        ·
          refine ⟨37047283295118811498235795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98792755453650163995295453 37047283295118811498235795)
          ·
            refine ⟨55570924942678217247353693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37047283295118811498235795 55570924942678217247353693)
            ·
              refine ⟨20839096853504331467757635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55570924942678217247353693 20839096853504331467757635)
              ·
                refine ⟨31258645280256497201636453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20839096853504331467757635 31258645280256497201636453)
                ·
                  refine ⟨5860995990048093225306835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31258645280256497201636453 5860995990048093225306835)
                  ·
                    refine ⟨8791493985072139837960253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5860995990048093225306835 8791493985072139837960253)
                    ·
                      refine ⟨3296810244402052439235095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8791493985072139837960253 3296810244402052439235095)
                      ·
                        rfl

theorem cell23_6420515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 4, 1, 3].length) (baseStart_6420515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420515 prefixEnd_6420515 := by exact prefixLift 6420515
  have htrace : WordTrace (prefixWord ++ tailWord_6420515) baseStart_6420515 baseEnd_6420515 := by
    simpa [prefixWord, tailWord_6420515, baseEnd_6420515] using wordTrace_append hprefix tailTrace_6420515
  have hstable : (prefixWord ++ tailWord_6420515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420515).length < 2 ^ (prefixWord ++ tailWord_6420515).sum := by decide
  have hdescent : baseEnd_6420515 < baseStart_6420515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420558 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_6420558 : Nat := 118140960795 + 6420558 * 2 ^ 59
def prefixEnd_6420558 : Nat := 4983230072969 + 3 ^ 40 * 6420558 * 2
def baseEnd_6420558 : Nat := 3296832324070195770997397

theorem tailTrace_6420558 : CollatzResearch.WordTrace tailWord_6420558 prefixEnd_6420558 3296832324070195770997397 := by
  unfold tailWord_6420558
  simp only [CollatzResearch.WordTrace]
  refine ⟨29272123584177798106397791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156117992448948256567454885 29272123584177798106397791)
  ·
    refine ⟨43908185376266697159596687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29272123584177798106397791 43908185376266697159596687)
    ·
      refine ⟨65862278064400045739395031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43908185376266697159596687 65862278064400045739395031)
      ·
        refine ⟨98793417096600068609092547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65862278064400045739395031 98793417096600068609092547)
        ·
          refine ⟨148190125644900102913638821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98793417096600068609092547 148190125644900102913638821)
          ·
            refine ⟨27785648558418769296307279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148190125644900102913638821 27785648558418769296307279)
            ·
              refine ⟨41678472837628153944460919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27785648558418769296307279 41678472837628153944460919)
              ·
                refine ⟨62517709256442230916691379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41678472837628153944460919 62517709256442230916691379)
                ·
                  refine ⟨93776563884663346375037069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62517709256442230916691379 93776563884663346375037069)
                  ·
                    refine ⟨35166211456748754890638901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93776563884663346375037069 35166211456748754890638901)
                    ·
                      refine ⟨3296832324070195770997397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35166211456748754890638901 3296832324070195770997397)
                      ·
                        rfl

theorem cell23_6420558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_6420558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420558 prefixEnd_6420558 := by exact prefixLift 6420558
  have htrace : WordTrace (prefixWord ++ tailWord_6420558) baseStart_6420558 baseEnd_6420558 := by
    simpa [prefixWord, tailWord_6420558, baseEnd_6420558] using wordTrace_append hprefix tailTrace_6420558
  have hstable : (prefixWord ++ tailWord_6420558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420558).length < 2 ^ (prefixWord ++ tailWord_6420558).sum := by decide
  have hdescent : baseEnd_6420558 < baseStart_6420558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420589 : List Nat := [1, 5, 1, 1, 2, 1, 3, 3, 2, 2, 2]
def baseStart_6420589 : Nat := 118140960795 + 6420589 * 2 ^ 59
def prefixEnd_6420589 : Nat := 4983230072969 + 3 ^ 40 * 6420589 * 2
def baseEnd_6420589 : Nat := 3296848241970485149709755

theorem tailTrace_6420589 : CollatzResearch.WordTrace tailWord_6420589 prefixEnd_6420589 3296848241970485149709755 := by
  unfold tailWord_6420589
  simp only [CollatzResearch.WordTrace]
  refine ⟨234178119336310077145560821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156118746224206718097040547 234178119336310077145560821)
  ·
    refine ⟨21954198687779069732396327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234178119336310077145560821 21954198687779069732396327)
    ·
      refine ⟨32931298031668604598594491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21954198687779069732396327 32931298031668604598594491)
      ·
        refine ⟨49396947047502906897891737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32931298031668604598594491 49396947047502906897891737)
        ·
          refine ⟨37047710285627180173418803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49396947047502906897891737 37047710285627180173418803)
          ·
            refine ⟨55571565428440770260128205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37047710285627180173418803 55571565428440770260128205)
            ·
              refine ⟨20839337035665288847548077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55571565428440770260128205 20839337035665288847548077)
              ·
                refine ⟨7814751388374483317830529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20839337035665288847548077 7814751388374483317830529)
                ·
                  refine ⟨5861063541280862488372897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7814751388374483317830529 5861063541280862488372897)
                  ·
                    refine ⟨4395797655960646866279673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5861063541280862488372897 4395797655960646866279673)
                    ·
                      refine ⟨3296848241970485149709755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4395797655960646866279673 3296848241970485149709755)
                      ·
                        rfl

theorem cell23_6420589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_6420589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420589 prefixEnd_6420589 := by exact prefixLift 6420589
  have htrace : WordTrace (prefixWord ++ tailWord_6420589) baseStart_6420589 baseEnd_6420589 := by
    simpa [prefixWord, tailWord_6420589, baseEnd_6420589] using wordTrace_append hprefix tailTrace_6420589
  have hstable : (prefixWord ++ tailWord_6420589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420589).length < 2 ^ (prefixWord ++ tailWord_6420589).sum := by decide
  have hdescent : baseEnd_6420589 < baseStart_6420589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420665 : List Nat := [1, 2, 1, 4, 1, 2, 3, 1, 1, 4, 3]
def baseStart_6420665 : Nat := 118140960795 + 6420665 * 2 ^ 59
def prefixEnd_6420665 : Nat := 4983230072969 + 3 ^ 40 * 6420665 * 2
def baseEnd_6420665 : Nat := 3296887266500226852359405

theorem tailTrace_6420665 : CollatzResearch.WordTrace tailWord_6420665 prefixEnd_6420665 3296887266500226852359405 := by
  unfold tailWord_6420665
  simp only [CollatzResearch.WordTrace]
  refine ⟨234180891284034742125327449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156120594189356494750218299 234180891284034742125327449)
  ·
    refine ⟨175635668463026056593995587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234180891284034742125327449 175635668463026056593995587)
    ·
      refine ⟨263453502694539084890993381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175635668463026056593995587 263453502694539084890993381)
      ·
        refine ⟨49397531755226078417061259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263453502694539084890993381 49397531755226078417061259)
        ·
          refine ⟨74096297632839117625591889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49397531755226078417061259 74096297632839117625591889)
          ·
            refine ⟨55572223224629338219193917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74096297632839117625591889 55572223224629338219193917)
            ·
              refine ⟨20839583709236001832197719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55572223224629338219193917 20839583709236001832197719)
              ·
                refine ⟨31259375563854002748296579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20839583709236001832197719 31259375563854002748296579)
                ·
                  refine ⟨46889063345781004122444869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31259375563854002748296579 46889063345781004122444869)
                  ·
                    refine ⟨8791699377333938272958413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46889063345781004122444869 8791699377333938272958413)
                    ·
                      refine ⟨3296887266500226852359405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8791699377333938272958413 3296887266500226852359405)
                      ·
                        rfl

theorem cell23_6420665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 4, 3].length) (baseStart_6420665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420665 prefixEnd_6420665 := by exact prefixLift 6420665
  have htrace : WordTrace (prefixWord ++ tailWord_6420665) baseStart_6420665 baseEnd_6420665 := by
    simpa [prefixWord, tailWord_6420665, baseEnd_6420665] using wordTrace_append hprefix tailTrace_6420665
  have hstable : (prefixWord ++ tailWord_6420665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420665).length < 2 ^ (prefixWord ++ tailWord_6420665).sum := by decide
  have hdescent : baseEnd_6420665 < baseStart_6420665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420729 : List Nat := [1, 2, 1, 3, 1, 1, 2, 7, 1, 1, 3]
def baseStart_6420729 : Nat := 118140960795 + 6420729 * 2 ^ 59
def prefixEnd_6420729 : Nat := 4983230072969 + 3 ^ 40 * 6420729 * 2
def baseEnd_6420729 : Nat := 3296920129262114601959111

theorem tailTrace_6420729 : CollatzResearch.WordTrace tailWord_6420729 prefixEnd_6420729 3296920129262114601959111 := by
  unfold tailWord_6420729
  simp only [CollatzResearch.WordTrace]
  refine ⟨234183225555802881055657241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156122150370535254037104827 234183225555802881055657241)
  ·
    refine ⟨175637419166852160791742931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234183225555802881055657241 175637419166852160791742931)
    ·
      refine ⟨263456128750278241187614397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175637419166852160791742931 263456128750278241187614397)
      ·
        refine ⟨98796048281354340445355399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263456128750278241187614397 98796048281354340445355399)
        ·
          refine ⟨148194072422031510668033099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98796048281354340445355399 148194072422031510668033099)
          ·
            refine ⟨222291108633047266002049649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148194072422031510668033099 222291108633047266002049649)
            ·
              refine ⟨166718331474785449501537237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222291108633047266002049649 166718331474785449501537237)
              ·
                refine ⟨3907460893940283972692279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 166718331474785449501537237 3907460893940283972692279)
                ·
                  refine ⟨5861191340910425959038419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3907460893940283972692279 5861191340910425959038419)
                  ·
                    refine ⟨8791787011365638938557629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5861191340910425959038419 8791787011365638938557629)
                    ·
                      refine ⟨3296920129262114601959111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8791787011365638938557629 3296920129262114601959111)
                      ·
                        rfl

theorem cell23_6420729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 1, 1, 3].length) (baseStart_6420729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420729 prefixEnd_6420729 := by exact prefixLift 6420729
  have htrace : WordTrace (prefixWord ++ tailWord_6420729) baseStart_6420729 baseEnd_6420729 := by
    simpa [prefixWord, tailWord_6420729, baseEnd_6420729] using wordTrace_append hprefix tailTrace_6420729
  have hstable : (prefixWord ++ tailWord_6420729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420729).length < 2 ^ (prefixWord ++ tailWord_6420729).sum := by decide
  have hdescent : baseEnd_6420729 < baseStart_6420729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420732 : List Nat := [2, 2, 2, 1, 4, 1, 2, 3, 1, 5]
def baseStart_6420732 : Nat := 118140960795 + 6420732 * 2 ^ 59
def prefixEnd_6420732 : Nat := 4983230072969 + 3 ^ 40 * 6420732 * 2
def baseEnd_6420732 : Nat := 1098973889901359363407199

theorem tailTrace_6420732 : CollatzResearch.WordTrace tailWord_6420732 prefixEnd_6420732 1098973889901359363407199 := by
  unfold tailWord_6420732
  simp only [CollatzResearch.WordTrace]
  refine ⟨117091667487396006284008225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156122223316528008378677633 117091667487396006284008225)
  ·
    refine ⟨87818750615547004713006169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117091667487396006284008225 87818750615547004713006169)
    ·
      refine ⟨65864062961660253534754627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87818750615547004713006169 65864062961660253534754627)
      ·
        refine ⟨98796094442490380302131941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65864062961660253534754627 98796094442490380302131941)
        ·
          refine ⟨18524267707966946306649739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98796094442490380302131941 18524267707966946306649739)
          ·
            refine ⟨27786401561950419459974609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18524267707966946306649739 27786401561950419459974609)
            ·
              refine ⟨20839801171462814594980957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27786401561950419459974609 20839801171462814594980957)
              ·
                refine ⟨7814925439298555473117859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20839801171462814594980957 7814925439298555473117859)
                ·
                  refine ⟨11722388158947833209676789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7814925439298555473117859 11722388158947833209676789)
                  ·
                    refine ⟨1098973889901359363407199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11722388158947833209676789 1098973889901359363407199)
                    ·
                      rfl

theorem cell23_6420732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 1, 5].length) (baseStart_6420732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420732 prefixEnd_6420732 := by exact prefixLift 6420732
  have htrace : WordTrace (prefixWord ++ tailWord_6420732) baseStart_6420732 baseEnd_6420732 := by
    simpa [prefixWord, tailWord_6420732, baseEnd_6420732] using wordTrace_append hprefix tailTrace_6420732
  have hstable : (prefixWord ++ tailWord_6420732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420732).length < 2 ^ (prefixWord ++ tailWord_6420732).sum := by decide
  have hdescent : baseEnd_6420732 < baseStart_6420732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420766 : List Nat := [4, 3, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_6420766 : Nat := 118140960795 + 6420766 * 2 ^ 59
def prefixEnd_6420766 : Nat := 4983230072969 + 3 ^ 40 * 6420766 * 2
def baseEnd_6420766 : Nat := 1098979709348776985732147

theorem tailTrace_6420766 : CollatzResearch.WordTrace tailWord_6420766 prefixEnd_6420766 1098979709348776985732147 := by
  unfold tailWord_6420766
  simp only [CollatzResearch.WordTrace]
  refine ⟨29273071882083604546844269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156123050037779224249836101 29273071882083604546844269)
  ·
    refine ⟨10977401955781351705066601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29273071882083604546844269 10977401955781351705066601)
    ·
      refine ⟨8233051466836013778799951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10977401955781351705066601 8233051466836013778799951)
      ·
        refine ⟨12349577200254020668199927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8233051466836013778799951 12349577200254020668199927)
        ·
          refine ⟨18524365800381031002299891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12349577200254020668199927 18524365800381031002299891)
          ·
            refine ⟨27786548700571546503449837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18524365800381031002299891 27786548700571546503449837)
            ·
              refine ⟨10419955762714329938793689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27786548700571546503449837 10419955762714329938793689)
              ·
                refine ⟨7814966822035747454095267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10419955762714329938793689 7814966822035747454095267)
                ·
                  refine ⟨11722450233053621181142901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7814966822035747454095267 11722450233053621181142901)
                  ·
                    refine ⟨1098979709348776985732147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11722450233053621181142901 1098979709348776985732147)
                    ·
                      rfl

theorem cell23_6420766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_6420766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420766 prefixEnd_6420766 := by exact prefixLift 6420766
  have htrace : WordTrace (prefixWord ++ tailWord_6420766) baseStart_6420766 baseEnd_6420766 := by
    simpa [prefixWord, tailWord_6420766, baseEnd_6420766] using wordTrace_append hprefix tailTrace_6420766
  have hstable : (prefixWord ++ tailWord_6420766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420766).length < 2 ^ (prefixWord ++ tailWord_6420766).sum := by decide
  have hdescent : baseEnd_6420766 < baseStart_6420766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420769 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 3, 2, 2]
def baseStart_6420769 : Nat := 118140960795 + 6420769 * 2 ^ 59
def prefixEnd_6420769 : Nat := 4983230072969 + 3 ^ 40 * 6420769 * 2
def baseEnd_6420769 : Nat := 3296940668488294445458927

theorem tailTrace_6420769 : CollatzResearch.WordTrace tailWord_6420769 prefixEnd_6420769 3296940668488294445458927 := by
  unfold tailWord_6420769
  simp only [CollatzResearch.WordTrace]
  refine ⟨234184684475657967887113361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156123122983771978591408907 234184684475657967887113361)
  ·
    refine ⟨175638513356743475915335021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234184684475657967887113361 175638513356743475915335021)
    ·
      refine ⟨65864442508778803468250633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175638513356743475915335021 65864442508778803468250633)
      ·
        refine ⟨49398331881584102601187975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65864442508778803468250633 49398331881584102601187975)
        ·
          refine ⟨74097497822376153901781963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49398331881584102601187975 74097497822376153901781963)
          ·
            refine ⟨111146246733564230852672945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74097497822376153901781963 111146246733564230852672945)
            ·
              refine ⟨83359685050173173139504709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111146246733564230852672945 83359685050173173139504709)
              ·
                refine ⟨15629940946907469963657133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83359685050173173139504709 15629940946907469963657133)
                ·
                  refine ⟨5861227855090301236371425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15629940946907469963657133 5861227855090301236371425)
                  ·
                    refine ⟨4395920891317725927278569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5861227855090301236371425 4395920891317725927278569)
                    ·
                      refine ⟨3296940668488294445458927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4395920891317725927278569 3296940668488294445458927)
                      ·
                        rfl

theorem cell23_6420769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_6420769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420769 prefixEnd_6420769 := by exact prefixLift 6420769
  have htrace : WordTrace (prefixWord ++ tailWord_6420769) baseStart_6420769 baseEnd_6420769 := by
    simpa [prefixWord, tailWord_6420769, baseEnd_6420769] using wordTrace_append hprefix tailTrace_6420769
  have hstable : (prefixWord ++ tailWord_6420769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420769).length < 2 ^ (prefixWord ++ tailWord_6420769).sum := by decide
  have hdescent : baseEnd_6420769 < baseStart_6420769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420786 : List Nat := [3, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4]
def baseStart_6420786 : Nat := 118140960795 + 6420786 * 2 ^ 59
def prefixEnd_6420786 : Nat := 4983230072969 + 3 ^ 40 * 6420786 * 2
def baseEnd_6420786 : Nat := 3296949397659420878946349

theorem tailTrace_6420786 : CollatzResearch.WordTrace tailWord_6420786 prefixEnd_6420786 3296949397659420878946349 := by
  unfold tailWord_6420786
  simp only [CollatzResearch.WordTrace]
  refine ⟨58546326129149094947620553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156123536344397586526988141 58546326129149094947620553)
  ·
    refine ⟨43909744596861821210715415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58546326129149094947620553 43909744596861821210715415)
    ·
      refine ⟨65864616895292731816073123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43909744596861821210715415 65864616895292731816073123)
      ·
        refine ⟨98796925342939097724109685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65864616895292731816073123 98796925342939097724109685)
        ·
          refine ⟨9262211750900540411635283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98796925342939097724109685 9262211750900540411635283)
          ·
            refine ⟨13893317626350810617452925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9262211750900540411635283 13893317626350810617452925)
            ·
              refine ⟨5209994109881553981544847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13893317626350810617452925 5209994109881553981544847)
              ·
                refine ⟨7814991164822330972317271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5209994109881553981544847 7814991164822330972317271)
                ·
                  refine ⟨11722486747233496458475907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7814991164822330972317271 11722486747233496458475907)
                  ·
                    refine ⟨17583730120850244687713861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11722486747233496458475907 17583730120850244687713861)
                    ·
                      refine ⟨3296949397659420878946349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17583730120850244687713861 3296949397659420878946349)
                      ·
                        rfl

theorem cell23_6420786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_6420786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420786 prefixEnd_6420786 := by exact prefixLift 6420786
  have htrace : WordTrace (prefixWord ++ tailWord_6420786) baseStart_6420786 baseEnd_6420786 := by
    simpa [prefixWord, tailWord_6420786, baseEnd_6420786] using wordTrace_append hprefix tailTrace_6420786
  have hstable : (prefixWord ++ tailWord_6420786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420786).length < 2 ^ (prefixWord ++ tailWord_6420786).sum := by decide
  have hdescent : baseEnd_6420786 < baseStart_6420786 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420803 : List Nat := [1, 1, 1, 3, 1, 3, 6, 2, 1, 2, 2]
def baseStart_6420803 : Nat := 118140960795 + 6420803 * 2 ^ 59
def prefixEnd_6420803 : Nat := 4983230072969 + 3 ^ 40 * 6420803 * 2
def baseEnd_6420803 : Nat := 3296958126830547312433771

theorem tailTrace_6420803 : CollatzResearch.WordTrace tailWord_6420803 prefixEnd_6420803 3296958126830547312433771 := by
  unfold tailWord_6420803
  simp only [CollatzResearch.WordTrace]
  refine ⟨234185924557534791693851063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156123949705023194462567375 234185924557534791693851063)
  ·
    refine ⟨351278886836302187540776595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234185924557534791693851063 351278886836302187540776595)
    ·
      refine ⟨526918330254453281311164893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351278886836302187540776595 526918330254453281311164893)
      ·
        refine ⟨197594373845419980491686835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 526918330254453281311164893 197594373845419980491686835)
        ·
          refine ⟨296391560768129970737530253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197594373845419980491686835 296391560768129970737530253)
          ·
            refine ⟨111146835288048739026573845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296391560768129970737530253 111146835288048739026573845)
            ·
              refine ⟨5210007904127284641870649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111146835288048739026573845 5210007904127284641870649)
              ·
                refine ⟨3907505928095463481402987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5210007904127284641870649 3907505928095463481402987)
                ·
                  refine ⟨5861258892143195222104481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3907505928095463481402987 5861258892143195222104481)
                  ·
                    refine ⟨4395944169107396416578361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5861258892143195222104481 4395944169107396416578361)
                    ·
                      refine ⟨3296958126830547312433771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4395944169107396416578361 3296958126830547312433771)
                      ·
                        rfl

theorem cell23_6420803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 1, 2, 2].length) (baseStart_6420803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420803 prefixEnd_6420803 := by exact prefixLift 6420803
  have htrace : WordTrace (prefixWord ++ tailWord_6420803) baseStart_6420803 baseEnd_6420803 := by
    simpa [prefixWord, tailWord_6420803, baseEnd_6420803] using wordTrace_append hprefix tailTrace_6420803
  have hstable : (prefixWord ++ tailWord_6420803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420803).length < 2 ^ (prefixWord ++ tailWord_6420803).sum := by decide
  have hdescent : baseEnd_6420803 < baseStart_6420803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420825 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 4, 3, 4]
def baseStart_6420825 : Nat := 118140960795 + 6420825 * 2 ^ 59
def prefixEnd_6420825 : Nat := 4983230072969 + 3 ^ 40 * 6420825 * 2
def baseEnd_6420825 : Nat := 3296969423404946226358669

theorem tailTrace_6420825 : CollatzResearch.WordTrace tailWord_6420825 prefixEnd_6420825 3296969423404946226358669 := by
  unfold tailWord_6420825
  simp only [CollatzResearch.WordTrace]
  refine ⟨234186726963455089451151929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156124484642303392967434619 234186726963455089451151929)
  ·
    refine ⟨175640045222591317088363947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234186726963455089451151929 175640045222591317088363947)
    ·
      refine ⟨263460067833886975632545921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175640045222591317088363947 263460067833886975632545921)
      ·
        refine ⟨197595050875415231724409441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263460067833886975632545921 197595050875415231724409441)
        ·
          refine ⟨148196288156561423793307081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197595050875415231724409441 148196288156561423793307081)
          ·
            refine ⟨111147216117421067844980311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148196288156561423793307081 111147216117421067844980311)
            ·
              refine ⟨166720824176131601767470467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111147216117421067844980311 166720824176131601767470467)
              ·
                refine ⟨250081236264197402651205701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166720824176131601767470467 250081236264197402651205701)
                ·
                  refine ⟨46890231799537012997101069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 250081236264197402651205701 46890231799537012997101069)
                  ·
                    refine ⟨17583836924826379873912901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46890231799537012997101069 17583836924826379873912901)
                    ·
                      refine ⟨3296969423404946226358669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17583836924826379873912901 3296969423404946226358669)
                      ·
                        rfl

theorem cell23_6420825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 4, 3, 4].length) (baseStart_6420825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420825 prefixEnd_6420825 := by exact prefixLift 6420825
  have htrace : WordTrace (prefixWord ++ tailWord_6420825) baseStart_6420825 baseEnd_6420825 := by
    simpa [prefixWord, tailWord_6420825, baseEnd_6420825] using wordTrace_append hprefix tailTrace_6420825
  have hstable : (prefixWord ++ tailWord_6420825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420825).length < 2 ^ (prefixWord ++ tailWord_6420825).sum := by decide
  have hdescent : baseEnd_6420825 < baseStart_6420825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420835 : List Nat := [1, 1, 1, 5, 2, 1, 1, 2, 1, 8]
def baseStart_6420835 : Nat := 118140960795 + 6420835 * 2 ^ 59
def prefixEnd_6420835 : Nat := 4983230072969 + 3 ^ 40 * 6420835 * 2
def baseEnd_6420835 : Nat := 1098991519403830395744541

theorem tailTrace_6420835 : CollatzResearch.WordTrace tailWord_6420835 prefixEnd_6420835 1098991519403830395744541 := by
  unfold tailWord_6420835
  simp only [CollatzResearch.WordTrace]
  refine ⟨234187091693418861159015959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156124727795612574106010639 234187091693418861159015959)
  ·
    refine ⟨351280637540128291738523939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234187091693418861159015959 351280637540128291738523939)
    ·
      refine ⟨526920956310192437607785909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351280637540128291738523939 526920956310192437607785909)
      ·
        refine ⟨49398839654080541025729929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 526920956310192437607785909 49398839654080541025729929)
        ·
          refine ⟨37049129740560405769297447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49398839654080541025729929 37049129740560405769297447)
          ·
            refine ⟨55573694610840608653946171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37049129740560405769297447 55573694610840608653946171)
            ·
              refine ⟨83360541916260912980919257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55573694610840608653946171 83360541916260912980919257)
              ·
                refine ⟨62520406437195684735689443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83360541916260912980919257 62520406437195684735689443)
                ·
                  refine ⟨93780609655793527103534165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62520406437195684735689443 93780609655793527103534165)
                  ·
                    refine ⟨1098991519403830395744541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93780609655793527103534165 1098991519403830395744541)
                    ·
                      rfl

theorem cell23_6420835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 8].length) (baseStart_6420835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420835 prefixEnd_6420835 := by exact prefixLift 6420835
  have htrace : WordTrace (prefixWord ++ tailWord_6420835) baseStart_6420835 baseEnd_6420835 := by
    simpa [prefixWord, tailWord_6420835, baseEnd_6420835] using wordTrace_append hprefix tailTrace_6420835
  have hstable : (prefixWord ++ tailWord_6420835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420835).length < 2 ^ (prefixWord ++ tailWord_6420835).sum := by decide
  have hdescent : baseEnd_6420835 < baseStart_6420835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420853 : List Nat := [1, 3, 4, 1, 2, 3, 1, 2, 2, 1, 3]
def baseStart_6420853 : Nat := 118140960795 + 6420853 * 2 ^ 59
def prefixEnd_6420853 : Nat := 4983230072969 + 3 ^ 40 * 6420853 * 2
def baseEnd_6420853 : Nat := 3296983800863272116808541

theorem tailTrace_6420853 : CollatzResearch.WordTrace tailWord_6420853 prefixEnd_6420853 3296983800863272116808541 := by
  unfold tailWord_6420853
  simp only [CollatzResearch.WordTrace]
  refine ⟨234187748207353650233171213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156125165471569100155447475 234187748207353650233171213)
  ·
    refine ⟨87820405577757618837439205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234187748207353650233171213 87820405577757618837439205)
    ·
      refine ⟨16466326045829553532019851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87820405577757618837439205 16466326045829553532019851)
      ·
        refine ⟨24699489068744330298029777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16466326045829553532019851 24699489068744330298029777)
        ·
          refine ⟨18524616801558247723522333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24699489068744330298029777 18524616801558247723522333)
          ·
            refine ⟨6946731300584342896320875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18524616801558247723522333 6946731300584342896320875)
            ·
              refine ⟨10420096950876514344481313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6946731300584342896320875 10420096950876514344481313)
              ·
                refine ⟨7815072713157385758360985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10420096950876514344481313 7815072713157385758360985)
                ·
                  refine ⟨5861304534868039318770739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7815072713157385758360985 5861304534868039318770739)
                  ·
                    refine ⟨8791956802302058978156109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5861304534868039318770739 8791956802302058978156109)
                    ·
                      refine ⟨3296983800863272116808541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8791956802302058978156109 3296983800863272116808541)
                      ·
                        rfl

theorem cell23_6420853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 2, 1, 3].length) (baseStart_6420853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420853 prefixEnd_6420853 := by exact prefixLift 6420853
  have htrace : WordTrace (prefixWord ++ tailWord_6420853) baseStart_6420853 baseEnd_6420853 := by
    simpa [prefixWord, tailWord_6420853, baseEnd_6420853] using wordTrace_append hprefix tailTrace_6420853
  have hstable : (prefixWord ++ tailWord_6420853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420853).length < 2 ^ (prefixWord ++ tailWord_6420853).sum := by decide
  have hdescent : baseEnd_6420853 < baseStart_6420853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420872 : List Nat := [2, 1, 3, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_6420872 : Nat := 118140960795 + 6420872 * 2 ^ 59
def prefixEnd_6420872 : Nat := 4983230072969 + 3 ^ 40 * 6420872 * 2
def baseEnd_6420872 : Nat := 3296993556995707542470953

theorem tailTrace_6420872 : CollatzResearch.WordTrace tailWord_6420872 prefixEnd_6420872 3296993556995707542470953 := by
  unfold tailWord_6420872
  simp only [CollatzResearch.WordTrace]
  refine ⟨117094220597142408239056435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156125627462856544318741913 117094220597142408239056435)
  ·
    refine ⟨175641330895713612358584653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117094220597142408239056435 175641330895713612358584653)
    ·
      refine ⟨65865499085892604634469245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175641330895713612358584653 65865499085892604634469245)
      ·
        refine ⟨24699562157209726737925967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65865499085892604634469245 24699562157209726737925967)
        ·
          refine ⟨37049343235814590106888951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24699562157209726737925967 37049343235814590106888951)
          ·
            refine ⟨55574014853721885160333427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37049343235814590106888951 55574014853721885160333427)
            ·
              refine ⟨83361022280582827740500141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55574014853721885160333427 83361022280582827740500141)
              ·
                refine ⟨31260383355218560402687553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83361022280582827740500141 31260383355218560402687553)
                ·
                  refine ⟨23445287516413920302015665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31260383355218560402687553 23445287516413920302015665)
                  ·
                    refine ⟨17583965637310440226511749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23445287516413920302015665 17583965637310440226511749)
                    ·
                      refine ⟨3296993556995707542470953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17583965637310440226511749 3296993556995707542470953)
                      ·
                        rfl

theorem cell23_6420872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_6420872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420872 prefixEnd_6420872 := by exact prefixLift 6420872
  have htrace : WordTrace (prefixWord ++ tailWord_6420872) baseStart_6420872 baseEnd_6420872 := by
    simpa [prefixWord, tailWord_6420872, baseEnd_6420872] using wordTrace_append hprefix tailTrace_6420872
  have hstable : (prefixWord ++ tailWord_6420872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420872).length < 2 ^ (prefixWord ++ tailWord_6420872).sum := by decide
  have hdescent : baseEnd_6420872 < baseStart_6420872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420876 : List Nat := [2, 2, 1, 2, 1, 6, 1, 1, 1, 4, 2]
def baseStart_6420876 : Nat := 118140960795 + 6420876 * 2 ^ 59
def prefixEnd_6420876 : Nat := 4983230072969 + 3 ^ 40 * 6420876 * 2
def baseEnd_6420876 : Nat := 3296995610918325526820935

theorem tailTrace_6420876 : CollatzResearch.WordTrace tailWord_6420876 prefixEnd_6420876 3296995610918325526820935 := by
  unfold tailWord_6420876
  simp only [CollatzResearch.WordTrace]
  refine ⟨117094293543135162580629241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156125724724180216774172321 117094293543135162580629241)
  ·
    refine ⟨87820720157351371935471931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117094293543135162580629241 87820720157351371935471931)
    ·
      refine ⟨131731080236027057903207897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87820720157351371935471931 131731080236027057903207897)
      ·
        refine ⟨98798310177020293427405923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131731080236027057903207897 98798310177020293427405923)
        ·
          refine ⟨148197465265530440141108885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98798310177020293427405923 148197465265530440141108885)
          ·
            refine ⟨6946756184321739381614479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 148197465265530440141108885 6946756184321739381614479)
            ·
              refine ⟨10420134276482609072421719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6946756184321739381614479 10420134276482609072421719)
              ·
                refine ⟨15630201414723913608632579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10420134276482609072421719 15630201414723913608632579)
                ·
                  refine ⟨23445302122085870412948869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15630201414723913608632579 23445302122085870412948869)
                  ·
                    refine ⟨4395994147891100702427913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23445302122085870412948869 4395994147891100702427913)
                    ·
                      refine ⟨3296995610918325526820935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4395994147891100702427913 3296995610918325526820935)
                      ·
                        rfl

theorem cell23_6420876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_6420876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420876 prefixEnd_6420876 := by exact prefixLift 6420876
  have htrace : WordTrace (prefixWord ++ tailWord_6420876) baseStart_6420876 baseEnd_6420876 := by
    simpa [prefixWord, tailWord_6420876, baseEnd_6420876] using wordTrace_append hprefix tailTrace_6420876
  have hstable : (prefixWord ++ tailWord_6420876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420876).length < 2 ^ (prefixWord ++ tailWord_6420876).sum := by decide
  have hdescent : baseEnd_6420876 < baseStart_6420876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420899 : List Nat := [1, 1, 1, 4, 1, 4, 3, 3, 5]
def baseStart_6420899 : Nat := 118140960795 + 6420899 * 2 ^ 59
def prefixEnd_6420899 : Nat := 4983230072969 + 3 ^ 40 * 6420899 * 2
def baseEnd_6420899 : Nat := 366334157885930992981481

theorem tailTrace_6420899 : CollatzResearch.WordTrace tailWord_6420899 prefixEnd_6420899 366334157885930992981481 := by
  unfold tailWord_6420899
  simp only [CollatzResearch.WordTrace]
  refine ⟨234189425965187000089345751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156126283976791333392897167 234189425965187000089345751)
  ·
    refine ⟨351284138947780500134018627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234189425965187000089345751 351284138947780500134018627)
    ·
      refine ⟨526926208421670750201027941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351284138947780500134018627 526926208421670750201027941)
      ·
        refine ⟨98798664079063265662692739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 526926208421670750201027941 98798664079063265662692739)
        ·
          refine ⟨148197996118594898494039109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98798664079063265662692739 148197996118594898494039109)
          ·
            refine ⟨27787124272236543467632333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148197996118594898494039109 27787124272236543467632333)
            ·
              refine ⟨10420171602088703800362125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27787124272236543467632333 10420171602088703800362125)
              ·
                refine ⟨3907564350783263925135797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10420171602088703800362125 3907564350783263925135797)
                ·
                  refine ⟨366334157885930992981481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3907564350783263925135797 366334157885930992981481)
                  ·
                    rfl

theorem cell23_6420899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 5].length) (baseStart_6420899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420899 prefixEnd_6420899 := by exact prefixLift 6420899
  have htrace : WordTrace (prefixWord ++ tailWord_6420899) baseStart_6420899 baseEnd_6420899 := by
    simpa [prefixWord, tailWord_6420899, baseEnd_6420899] using wordTrace_append hprefix tailTrace_6420899
  have hstable : (prefixWord ++ tailWord_6420899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420899).length < 2 ^ (prefixWord ++ tailWord_6420899).sum := by decide
  have hdescent : baseEnd_6420899 < baseStart_6420899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420905 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 7]
def baseStart_6420905 : Nat := 118140960795 + 6420905 * 2 ^ 59
def prefixEnd_6420905 : Nat := 4983230072969 + 3 ^ 40 * 6420905 * 2
def baseEnd_6420905 : Nat := 3297010501857305913358301

theorem tailTrace_6420905 : CollatzResearch.WordTrace tailWord_6420905 prefixEnd_6420905 3297010501857305913358301 := by
  unfold tailWord_6420905
  simp only [CollatzResearch.WordTrace]
  refine ⟨234189644803165263114064169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156126429868776842076042779 234189644803165263114064169)
  ·
    refine ⟨175642233602373947335548127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234189644803165263114064169 175642233602373947335548127)
    ·
      refine ⟨263463350403560921003322191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175642233602373947335548127 263463350403560921003322191)
      ·
        refine ⟨395195025605341381504983287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263463350403560921003322191 395195025605341381504983287)
        ·
          refine ⟨592792538408012072257474931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395195025605341381504983287 592792538408012072257474931)
          ·
            refine ⟨889188807612018108386212397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592792538408012072257474931 889188807612018108386212397)
            ·
              refine ⟨333445802854506790644829649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 889188807612018108386212397 333445802854506790644829649)
              ·
                refine ⟨250084352140880092983622237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333445802854506790644829649 250084352140880092983622237)
                ·
                  refine ⟨93781632052830034868858339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 250084352140880092983622237 93781632052830034868858339)
                  ·
                    refine ⟨140672448079245052303287509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93781632052830034868858339 140672448079245052303287509)
                    ·
                      refine ⟨3297010501857305913358301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140672448079245052303287509 3297010501857305913358301)
                      ·
                        rfl

theorem cell23_6420905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 3, 1, 7].length) (baseStart_6420905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420905 prefixEnd_6420905 := by exact prefixLift 6420905
  have htrace : WordTrace (prefixWord ++ tailWord_6420905) baseStart_6420905 baseEnd_6420905 := by
    simpa [prefixWord, tailWord_6420905, baseEnd_6420905] using wordTrace_append hprefix tailTrace_6420905
  have hstable : (prefixWord ++ tailWord_6420905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420905).length < 2 ^ (prefixWord ++ tailWord_6420905).sum := by decide
  have hdescent : baseEnd_6420905 < baseStart_6420905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420915 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 8]
def baseStart_6420915 : Nat := 118140960795 + 6420915 * 2 ^ 59
def prefixEnd_6420915 : Nat := 4983230072969 + 3 ^ 40 * 6420915 * 2
def baseEnd_6420915 : Nat := 3297015636663850874233255

theorem tailTrace_6420915 : CollatzResearch.WordTrace tailWord_6420915 prefixEnd_6420915 3297015636663850874233255 := by
  unfold tailWord_6420915
  simp only [CollatzResearch.WordTrace]
  refine ⟨234190009533129034821928199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156126673022086023214618799 234190009533129034821928199)
  ·
    refine ⟨351285014299693552232892299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234190009533129034821928199 351285014299693552232892299)
    ·
      refine ⟨526927521449540328349338449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351285014299693552232892299 526927521449540328349338449)
      ·
        refine ⟨395195641087155246262003837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 526927521449540328349338449 395195641087155246262003837)
        ·
          refine ⟨148198365407683217348251439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395195641087155246262003837 148198365407683217348251439)
          ·
            refine ⟨222297548111524826022377159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148198365407683217348251439 222297548111524826022377159)
            ·
              refine ⟨333446322167287239033565739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222297548111524826022377159 333446322167287239033565739)
              ·
                refine ⟨500169483250930858550348609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333446322167287239033565739 500169483250930858550348609)
                ·
                  refine ⟨375127112438198143912761457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 500169483250930858550348609 375127112438198143912761457)
                  ·
                    refine ⟨281345334328648607934571093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 375127112438198143912761457 281345334328648607934571093)
                    ·
                      refine ⟨3297015636663850874233255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 281345334328648607934571093 3297015636663850874233255)
                      ·
                        rfl

theorem cell23_6420915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 8].length) (baseStart_6420915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420915 prefixEnd_6420915 := by exact prefixLift 6420915
  have htrace : WordTrace (prefixWord ++ tailWord_6420915) baseStart_6420915 baseEnd_6420915 := by
    simpa [prefixWord, tailWord_6420915, baseEnd_6420915] using wordTrace_append hprefix tailTrace_6420915
  have hstable : (prefixWord ++ tailWord_6420915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420915).length < 2 ^ (prefixWord ++ tailWord_6420915).sum := by decide
  have hdescent : baseEnd_6420915 < baseStart_6420915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420949 : List Nat := [1, 3, 2, 3, 1, 2, 1, 3, 2, 1, 4]
def baseStart_6420949 : Nat := 118140960795 + 6420949 * 2 ^ 59
def prefixEnd_6420949 : Nat := 4983230072969 + 3 ^ 40 * 6420949 * 2
def baseEnd_6420949 : Nat := 3297033095006103741208099

theorem tailTrace_6420949 : CollatzResearch.WordTrace tailWord_6420949 prefixEnd_6420949 3297033095006103741208099 := by
  unfold tailWord_6420949
  simp only [CollatzResearch.WordTrace]
  refine ⟨234191249615005858628665901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156127499743337239085777267 234191249615005858628665901)
  ·
    refine ⟨87821718605627196985749713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234191249615005858628665901 87821718605627196985749713)
    ·
      refine ⟨65866288954220397739312285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87821718605627196985749713 65866288954220397739312285)
      ·
        refine ⟨24699858357832649152242107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65866288954220397739312285 24699858357832649152242107)
        ·
          refine ⟨37049787536748973728363161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24699858357832649152242107 37049787536748973728363161)
          ·
            refine ⟨27787340652561730296272371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37049787536748973728363161 27787340652561730296272371)
            ·
              refine ⟨41681010978842595444408557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27787340652561730296272371 41681010978842595444408557)
              ·
                refine ⟨15630379117065973291653209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41681010978842595444408557 15630379117065973291653209)
                ·
                  refine ⟨11722784337799479968739907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15630379117065973291653209 11722784337799479968739907)
                  ·
                    refine ⟨17584176506699219953109861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11722784337799479968739907 17584176506699219953109861)
                    ·
                      refine ⟨3297033095006103741208099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17584176506699219953109861 3297033095006103741208099)
                      ·
                        rfl

theorem cell23_6420949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 3, 2, 1, 4].length) (baseStart_6420949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420949 prefixEnd_6420949 := by exact prefixLift 6420949
  have htrace : WordTrace (prefixWord ++ tailWord_6420949) baseStart_6420949 baseEnd_6420949 := by
    simpa [prefixWord, tailWord_6420949, baseEnd_6420949] using wordTrace_append hprefix tailTrace_6420949
  have hstable : (prefixWord ++ tailWord_6420949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420949).length < 2 ^ (prefixWord ++ tailWord_6420949).sum := by decide
  have hdescent : baseEnd_6420949 < baseStart_6420949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6420976 : List Nat := [2, 1, 1, 1, 3, 3, 3, 4, 1, 4]
def baseStart_6420976 : Nat := 118140960795 + 6420976 * 2 ^ 59
def prefixEnd_6420976 : Nat := 4983230072969 + 3 ^ 40 * 6420976 * 2
def baseEnd_6420976 : Nat := 1099015652994591711856825

theorem tailTrace_6420976 : CollatzResearch.WordTrace tailWord_6420976 prefixEnd_6420976 1099015652994591711856825 := by
  unfold tailWord_6420976
  simp only [CollatzResearch.WordTrace]
  refine ⟨117096117192954021119949391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156128156257272028159932521 117096117192954021119949391)
  ·
    refine ⟨175644175789431031679924087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117096117192954021119949391 175644175789431031679924087)
    ·
      refine ⟨263466263684146547519886131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175644175789431031679924087 263466263684146547519886131)
      ·
        refine ⟨395199395526219821279829197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263466263684146547519886131 395199395526219821279829197)
        ·
          refine ⟨148199773322332432979935949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395199395526219821279829197 148199773322332432979935949)
          ·
            refine ⟨55574914995874662367475981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148199773322332432979935949 55574914995874662367475981)
            ·
              refine ⟨20840593123452998387803493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55574914995874662367475981 20840593123452998387803493)
              ·
                refine ⟨3907611210647437197713155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20840593123452998387803493 3907611210647437197713155)
                ·
                  refine ⟨5861416815971155796569733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3907611210647437197713155 5861416815971155796569733)
                  ·
                    refine ⟨1099015652994591711856825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5861416815971155796569733 1099015652994591711856825)
                    ·
                      rfl

theorem cell23_6420976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 4, 1, 4].length) (baseStart_6420976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6420976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6420976 prefixEnd_6420976 := by exact prefixLift 6420976
  have htrace : WordTrace (prefixWord ++ tailWord_6420976) baseStart_6420976 baseEnd_6420976 := by
    simpa [prefixWord, tailWord_6420976, baseEnd_6420976] using wordTrace_append hprefix tailTrace_6420976
  have hstable : (prefixWord ++ tailWord_6420976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6420976).length < 2 ^ (prefixWord ++ tailWord_6420976).sum := by decide
  have hdescent : baseEnd_6420976 < baseStart_6420976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6420976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421026 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 4, 3, 2]
def baseStart_6421026 : Nat := 118140960795 + 6421026 * 2 ^ 59
def prefixEnd_6421026 : Nat := 4983230072969 + 3 ^ 40 * 6421026 * 2
def baseEnd_6421026 : Nat := 3297072633016499939945245

theorem tailTrace_6421026 : CollatzResearch.WordTrace tailWord_6421026 prefixEnd_6421026 3297072633016499939945245 := by
  unfold tailWord_6421026
  simp only [CollatzResearch.WordTrace]
  refine ⟨58548514508931725194804733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156129372023817933852812621 58548514508931725194804733)
  ·
    refine ⟨21955692940849396948051775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58548514508931725194804733 21955692940849396948051775)
    ·
      refine ⟨32933539411274095422077663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21955692940849396948051775 32933539411274095422077663)
      ·
        refine ⟨49400309116911143133116495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32933539411274095422077663 49400309116911143133116495)
        ·
          refine ⟨74100463675366714699674743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49400309116911143133116495 74100463675366714699674743)
          ·
            refine ⟨111150695513050072049512115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74100463675366714699674743 111150695513050072049512115)
            ·
              refine ⟨166726043269575108074268173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111150695513050072049512115 166726043269575108074268173)
              ·
                refine ⟨62522266226090665527850565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166726043269575108074268173 62522266226090665527850565)
                ·
                  refine ⟨11722924917391999786471981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62522266226090665527850565 11722924917391999786471981)
                  ·
                    refine ⟨4396096844021999919926993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11722924917391999786471981 4396096844021999919926993)
                    ·
                      refine ⟨3297072633016499939945245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4396096844021999919926993 3297072633016499939945245)
                      ·
                        rfl

theorem cell23_6421026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_6421026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421026 prefixEnd_6421026 := by exact prefixLift 6421026
  have htrace : WordTrace (prefixWord ++ tailWord_6421026) baseStart_6421026 baseEnd_6421026 := by
    simpa [prefixWord, tailWord_6421026, baseEnd_6421026] using wordTrace_append hprefix tailTrace_6421026
  have hstable : (prefixWord ++ tailWord_6421026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421026).length < 2 ^ (prefixWord ++ tailWord_6421026).sum := by decide
  have hdescent : baseEnd_6421026 < baseStart_6421026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421059 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 3]
def baseStart_6421059 : Nat := 118140960795 + 6421059 * 2 ^ 59
def prefixEnd_6421059 : Nat := 4983230072969 + 3 ^ 40 * 6421059 * 2
def baseEnd_6421059 : Nat := 3297089577878098310832593

theorem tailTrace_6421059 : CollatzResearch.WordTrace tailWord_6421059 prefixEnd_6421059 3297089577878098310832593 := by
  unfold tailWord_6421059
  simp only [CollatzResearch.WordTrace]
  refine ⟨234195261644607347415170231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156130174429738231610113487 234195261644607347415170231)
  ·
    refine ⟨351292892466911021122755347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234195261644607347415170231 351292892466911021122755347)
    ·
      refine ⟨526939338700366531684133021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351292892466911021122755347 526939338700366531684133021)
      ·
        refine ⟨197602252012637449381549883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 526939338700366531684133021 197602252012637449381549883)
        ·
          refine ⟨296403378018956174072324825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197602252012637449381549883 296403378018956174072324825)
          ·
            refine ⟨222302533514217130554243619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296403378018956174072324825 222302533514217130554243619)
            ·
              refine ⟨333453800271325695831365429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222302533514217130554243619 333453800271325695831365429)
              ·
                refine ⟨31261293775436783984190509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 333453800271325695831365429 31261293775436783984190509)
                ·
                  refine ⟨11722985165788793994071441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31261293775436783984190509 11722985165788793994071441)
                  ·
                    refine ⟨8792238874341595495553581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11722985165788793994071441 8792238874341595495553581)
                    ·
                      refine ⟨3297089577878098310832593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8792238874341595495553581 3297089577878098310832593)
                      ·
                        rfl

theorem cell23_6421059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 3].length) (baseStart_6421059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421059 prefixEnd_6421059 := by exact prefixLift 6421059
  have htrace : WordTrace (prefixWord ++ tailWord_6421059) baseStart_6421059 baseEnd_6421059 := by
    simpa [prefixWord, tailWord_6421059, baseEnd_6421059] using wordTrace_append hprefix tailTrace_6421059
  have hstable : (prefixWord ++ tailWord_6421059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421059).length < 2 ^ (prefixWord ++ tailWord_6421059).sum := by decide
  have hdescent : baseEnd_6421059 < baseStart_6421059 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421076 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_6421076 : Nat := 118140960795 + 6421076 * 2 ^ 59
def prefixEnd_6421076 : Nat := 4983230072969 + 3 ^ 40 * 6421076 * 2
def baseEnd_6421076 : Nat := 3297098307049224744320015

theorem tailTrace_6421076 : CollatzResearch.WordTrace tailWord_6421076 prefixEnd_6421076 3297098307049224744320015 := by
  unfold tailWord_6421076
  simp only [CollatzResearch.WordTrace]
  refine ⟨117097940842772879659269541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156130587790363839545692721 117097940842772879659269541)
  ·
    refine ⟨21955863908019914936113039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117097940842772879659269541 21955863908019914936113039)
    ·
      refine ⟨32933795862029872404169559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21955863908019914936113039 32933795862029872404169559)
      ·
        refine ⟨49400693793044808606254339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32933795862029872404169559 49400693793044808606254339)
        ·
          refine ⟨74101040689567212909381509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49400693793044808606254339 74101040689567212909381509)
          ·
            refine ⟨13893945129293852420509033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74101040689567212909381509 13893945129293852420509033)
            ·
              refine ⟨10420458846970389315381775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13893945129293852420509033 10420458846970389315381775)
              ·
                refine ⟨15630688270455583973072663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10420458846970389315381775 15630688270455583973072663)
                ·
                  refine ⟨23446032405683375959608995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15630688270455583973072663 23446032405683375959608995)
                  ·
                    refine ⟨35169048608525063939413493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23446032405683375959608995 35169048608525063939413493)
                    ·
                      refine ⟨3297098307049224744320015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35169048608525063939413493 3297098307049224744320015)
                      ·
                        rfl

theorem cell23_6421076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_6421076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421076 prefixEnd_6421076 := by exact prefixLift 6421076
  have htrace : WordTrace (prefixWord ++ tailWord_6421076) baseStart_6421076 baseEnd_6421076 := by
    simpa [prefixWord, tailWord_6421076, baseEnd_6421076] using wordTrace_append hprefix tailTrace_6421076
  have hstable : (prefixWord ++ tailWord_6421076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421076).length < 2 ^ (prefixWord ++ tailWord_6421076).sum := by decide
  have hdescent : baseEnd_6421076 < baseStart_6421076 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421096 : List Nat := [2, 1, 4, 3, 2, 1, 2, 8]
def baseStart_6421096 : Nat := 118140960795 + 6421096 * 2 ^ 59
def prefixEnd_6421096 : Nat := 4983230072969 + 3 ^ 40 * 6421096 * 2
def baseEnd_6421096 : Nat := 122115132468974617261849

theorem tailTrace_6421096 : CollatzResearch.WordTrace tailWord_6421096 prefixEnd_6421096 122115132468974617261849 := by
  unfold tailWord_6421096
  simp only [CollatzResearch.WordTrace]
  refine ⟨117098305572736651367133571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156131074096982201822844761 117098305572736651367133571)
  ·
    refine ⟨175647458359104977050700357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117098305572736651367133571 175647458359104977050700357)
    ·
      refine ⟨32933898442332183197006317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175647458359104977050700357 32933898442332183197006317)
      ·
        refine ⟨12350211915874568698877369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32933898442332183197006317 12350211915874568698877369)
        ·
          refine ⟨9262658936905926524158027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12350211915874568698877369 9262658936905926524158027)
          ·
            refine ⟨13893988405358889786237041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9262658936905926524158027 13893988405358889786237041)
            ·
              refine ⟨10420491304019167339677781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13893988405358889786237041 10420491304019167339677781)
              ·
                refine ⟨122115132468974617261849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10420491304019167339677781 122115132468974617261849)
                ·
                  rfl

theorem cell23_6421096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 8].length) (baseStart_6421096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421096 prefixEnd_6421096 := by exact prefixLift 6421096
  have htrace : WordTrace (prefixWord ++ tailWord_6421096) baseStart_6421096 baseEnd_6421096 := by
    simpa [prefixWord, tailWord_6421096, baseEnd_6421096] using wordTrace_append hprefix tailTrace_6421096
  have hstable : (prefixWord ++ tailWord_6421096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421096).length < 2 ^ (prefixWord ++ tailWord_6421096).sum := by decide
  have hdescent : baseEnd_6421096 < baseStart_6421096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421140 : List Nat := [2, 4, 2, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_6421140 : Nat := 118140960795 + 6421140 * 2 ^ 59
def prefixEnd_6421140 : Nat := 4983230072969 + 3 ^ 40 * 6421140 * 2
def baseEnd_6421140 : Nat := 3297131169811112493919721

theorem tailTrace_6421140 : CollatzResearch.WordTrace tailWord_6421140 prefixEnd_6421140 3297131169811112493919721 := by
  unfold tailWord_6421140
  simp only [CollatzResearch.WordTrace]
  refine ⟨117099107978656949124434437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156132143971542598832579249 117099107978656949124434437)
  ·
    refine ⟨21956082745998177960831457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117099107978656949124434437 21956082745998177960831457)
    ·
      refine ⟨16467062059498633470623593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21956082745998177960831457 16467062059498633470623593)
      ·
        refine ⟨12350296544623975102967695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16467062059498633470623593 12350296544623975102967695)
        ·
          refine ⟨18525444816935962654451543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12350296544623975102967695 18525444816935962654451543)
          ·
            refine ⟨27788167225403943981677315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18525444816935962654451543 27788167225403943981677315)
            ·
              refine ⟨41682250838105915972515973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27788167225403943981677315 41682250838105915972515973)
              ·
                refine ⟨7815422032144859244846745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41682250838105915972515973 7815422032144859244846745)
                ·
                  refine ⟨5861566524108644433635059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7815422032144859244846745 5861566524108644433635059)
                  ·
                    refine ⟨8792349786162966650452589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5861566524108644433635059 8792349786162966650452589)
                    ·
                      refine ⟨3297131169811112493919721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8792349786162966650452589 3297131169811112493919721)
                      ·
                        rfl

theorem cell23_6421140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_6421140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421140 prefixEnd_6421140 := by exact prefixLift 6421140
  have htrace : WordTrace (prefixWord ++ tailWord_6421140) baseStart_6421140 baseEnd_6421140 := by
    simpa [prefixWord, tailWord_6421140, baseEnd_6421140] using wordTrace_append hprefix tailTrace_6421140
  have hstable : (prefixWord ++ tailWord_6421140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421140).length < 2 ^ (prefixWord ++ tailWord_6421140).sum := by decide
  have hdescent : baseEnd_6421140 < baseStart_6421140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421149 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 1, 3, 5]
def baseStart_6421149 : Nat := 118140960795 + 6421149 * 2 ^ 59
def prefixEnd_6421149 : Nat := 4983230072969 + 3 ^ 40 * 6421149 * 2
def baseEnd_6421149 : Nat := 3297135791137002958707179

theorem tailTrace_6421149 : CollatzResearch.WordTrace tailWord_6421149 prefixEnd_6421149 3297135791137002958707179 := by
  unfold tailWord_6421149
  simp only [CollatzResearch.WordTrace]
  refine ⟨234198544214281292785946501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156132362809520861857297667 234198544214281292785946501)
  ·
    refine ⟨43912227040177742397364969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234198544214281292785946501 43912227040177742397364969)
    ·
      refine ⟨32934170280133306798023727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43912227040177742397364969 32934170280133306798023727)
      ·
        refine ⟨49401255420199960197035591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32934170280133306798023727 49401255420199960197035591)
        ·
          refine ⟨74101883130299940295553387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49401255420199960197035591 74101883130299940295553387)
          ·
            refine ⟨111152824695449910443330081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74101883130299940295553387 111152824695449910443330081)
            ·
              refine ⟨83364618521587432832497561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111152824695449910443330081 83364618521587432832497561)
              ·
                refine ⟨62523463891190574624373171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83364618521587432832497561 62523463891190574624373171)
                ·
                  refine ⟨93785195836785861936559757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62523463891190574624373171 93785195836785861936559757)
                  ·
                    refine ⟨35169448438794698226209909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93785195836785861936559757 35169448438794698226209909)
                    ·
                      refine ⟨3297135791137002958707179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35169448438794698226209909 3297135791137002958707179)
                      ·
                        rfl

theorem cell23_6421149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_6421149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421149 prefixEnd_6421149 := by exact prefixLift 6421149
  have htrace : WordTrace (prefixWord ++ tailWord_6421149) baseStart_6421149 baseEnd_6421149 := by
    simpa [prefixWord, tailWord_6421149, baseEnd_6421149] using wordTrace_append hprefix tailTrace_6421149
  have hstable : (prefixWord ++ tailWord_6421149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421149).length < 2 ^ (prefixWord ++ tailWord_6421149).sum := by decide
  have hdescent : baseEnd_6421149 < baseStart_6421149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421209 : List Nat := [1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 7]
def baseStart_6421209 : Nat := 118140960795 + 6421209 * 2 ^ 59
def prefixEnd_6421209 : Nat := 4983230072969 + 3 ^ 40 * 6421209 * 2
def baseEnd_6421209 : Nat := 3297166599976272723956903

theorem tailTrace_6421209 : CollatzResearch.WordTrace tailWord_6421209 prefixEnd_6421209 3297166599976272723956903 := by
  unfold tailWord_6421209
  simp only [CollatzResearch.WordTrace]
  refine ⟨234200732594063923033130681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156133821729375948688753787 234200732594063923033130681)
  ·
    refine ⟨175650549445547942274848011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234200732594063923033130681 175650549445547942274848011)
    ·
      refine ⟨263475824168321913412272017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175650549445547942274848011 263475824168321913412272017)
      ·
        refine ⟨197606868126241435059204013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263475824168321913412272017 197606868126241435059204013)
        ·
          refine ⟨74102575547340538147201505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197606868126241435059204013 74102575547340538147201505)
          ·
            refine ⟨55576931660505403610401129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74102575547340538147201505 55576931660505403610401129)
            ·
              refine ⟨41682698745379052707800847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55576931660505403610401129 41682698745379052707800847)
              ·
                refine ⟨62524048118068579061701271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41682698745379052707800847 62524048118068579061701271)
                ·
                  refine ⟨93786072177102868592551907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62524048118068579061701271 93786072177102868592551907)
                  ·
                    refine ⟨140679108265654302888827861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93786072177102868592551907 140679108265654302888827861)
                    ·
                      refine ⟨3297166599976272723956903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140679108265654302888827861 3297166599976272723956903)
                      ·
                        rfl

theorem cell23_6421209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_6421209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421209 prefixEnd_6421209 := by exact prefixLift 6421209
  have htrace : WordTrace (prefixWord ++ tailWord_6421209) baseStart_6421209 baseEnd_6421209 := by
    simpa [prefixWord, tailWord_6421209, baseEnd_6421209] using wordTrace_append hprefix tailTrace_6421209
  have hstable : (prefixWord ++ tailWord_6421209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421209).length < 2 ^ (prefixWord ++ tailWord_6421209).sum := by decide
  have hdescent : baseEnd_6421209 < baseStart_6421209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421239 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 5]
def baseStart_6421239 : Nat := 118140960795 + 6421239 * 2 ^ 59
def prefixEnd_6421239 : Nat := 4983230072969 + 3 ^ 40 * 6421239 * 2
def baseEnd_6421239 : Nat := 3297182004395907606581765

theorem tailTrace_6421239 : CollatzResearch.WordTrace tailWord_6421239 prefixEnd_6421239 3297182004395907606581765 := by
  unfold tailWord_6421239
  simp only [CollatzResearch.WordTrace]
  refine ⟨234201826783955238156722771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156134551189303492104481847 234201826783955238156722771)
  ·
    refine ⟨351302740175932857235084157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234201826783955238156722771 351302740175932857235084157)
    ·
      refine ⟨131738527565974821463156559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351302740175932857235084157 131738527565974821463156559)
      ·
        refine ⟨197607791348962232194734839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131738527565974821463156559 197607791348962232194734839)
        ·
          refine ⟨296411687023443348292102259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197607791348962232194734839 296411687023443348292102259)
          ·
            refine ⟨444617530535165022438153389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296411687023443348292102259 444617530535165022438153389)
            ·
              refine ⟨166731573950686883414307521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 444617530535165022438153389 166731573950686883414307521)
              ·
                refine ⟨125048680463015162560730641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166731573950686883414307521 125048680463015162560730641)
                ·
                  refine ⟨93786510347261371920547981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125048680463015162560730641 93786510347261371920547981)
                  ·
                    refine ⟨35169941380223014470205493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93786510347261371920547981 35169941380223014470205493)
                    ·
                      refine ⟨3297182004395907606581765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35169941380223014470205493 3297182004395907606581765)
                      ·
                        rfl

theorem cell23_6421239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 5].length) (baseStart_6421239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421239 prefixEnd_6421239 := by exact prefixLift 6421239
  have htrace : WordTrace (prefixWord ++ tailWord_6421239) baseStart_6421239 baseEnd_6421239 := by
    simpa [prefixWord, tailWord_6421239, baseEnd_6421239] using wordTrace_append hprefix tailTrace_6421239
  have hstable : (prefixWord ++ tailWord_6421239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421239).length < 2 ^ (prefixWord ++ tailWord_6421239).sum := by decide
  have hdescent : baseEnd_6421239 < baseStart_6421239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421289 : List Nat := [1, 2, 1, 1, 1, 1, 1, 4, 2, 9]
def baseStart_6421289 : Nat := 118140960795 + 6421289 * 2 ^ 59
def prefixEnd_6421289 : Nat := 4983230072969 + 3 ^ 40 * 6421289 * 2
def baseEnd_6421289 : Nat := 1099069226142877470318845

theorem tailTrace_6421289 : CollatzResearch.WordTrace tailWord_6421289 prefixEnd_6421289 1099069226142877470318845 := by
  unfold tailWord_6421289
  simp only [CollatzResearch.WordTrace]
  refine ⟨234203650433774096696042921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156135766955849397797361947 234203650433774096696042921)
  ·
    refine ⟨175652737825330572522032191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234203650433774096696042921 175652737825330572522032191)
    ·
      refine ⟨263479106737995858783048287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175652737825330572522032191 263479106737995858783048287)
      ·
        refine ⟨395218660106993788174572431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263479106737995858783048287 395218660106993788174572431)
        ·
          refine ⟨592827990160490682261858647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395218660106993788174572431 592827990160490682261858647)
          ·
            refine ⟨889241985240736023392787971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592827990160490682261858647 889241985240736023392787971)
            ·
              refine ⟨1333862977861104035089181957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889241985240736023392787971 1333862977861104035089181957)
              ·
                refine ⟨250099308348957006579221617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1333862977861104035089181957 250099308348957006579221617)
                ·
                  refine ⟨187574481261717754934416213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250099308348957006579221617 187574481261717754934416213)
                  ·
                    refine ⟨1099069226142877470318845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 187574481261717754934416213 1099069226142877470318845)
                    ·
                      rfl

theorem cell23_6421289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 9].length) (baseStart_6421289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421289 prefixEnd_6421289 := by exact prefixLift 6421289
  have htrace : WordTrace (prefixWord ++ tailWord_6421289) baseStart_6421289 baseEnd_6421289 := by
    simpa [prefixWord, tailWord_6421289, baseEnd_6421289] using wordTrace_append hprefix tailTrace_6421289
  have hstable : (prefixWord ++ tailWord_6421289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421289).length < 2 ^ (prefixWord ++ tailWord_6421289).sum := by decide
  have hdescent : baseEnd_6421289 < baseStart_6421289 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421310 : List Nat := [4, 2, 1, 2, 3, 1, 2, 2, 6]
def baseStart_6421310 : Nat := 118140960795 + 6421310 * 2 ^ 59
def prefixEnd_6421310 : Nat := 4983230072969 + 3 ^ 40 * 6421310 * 2
def baseEnd_6421310 : Nat := 366357606835819647643771

theorem tailTrace_6421310 : CollatzResearch.WordTrace tailWord_6421310 prefixEnd_6421310 366357606835819647643771 := by
  unfold tailWord_6421310
  simp only [CollatzResearch.WordTrace]
  refine ⟨29275552045837252160319673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156136277577798678188371589 29275552045837252160319673)
  ·
    refine ⟨21956664034377939120239755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29275552045837252160319673 21956664034377939120239755)
    ·
      refine ⟨32934996051566908680359633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21956664034377939120239755 32934996051566908680359633)
      ·
        refine ⟨24701247038675181510269725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32934996051566908680359633 24701247038675181510269725)
        ·
          refine ⟨9262967639503193066351147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24701247038675181510269725 9262967639503193066351147)
          ·
            refine ⟨13894451459254789599526721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9262967639503193066351147 13894451459254789599526721)
            ·
              refine ⟨10420838594441092199645041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13894451459254789599526721 10420838594441092199645041)
              ·
                refine ⟨7815628945830819149733781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10420838594441092199645041 7815628945830819149733781)
                ·
                  refine ⟨366357606835819647643771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7815628945830819149733781 366357606835819647643771)
                  ·
                    rfl

theorem cell23_6421310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_6421310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421310 prefixEnd_6421310 := by exact prefixLift 6421310
  have htrace : WordTrace (prefixWord ++ tailWord_6421310) baseStart_6421310 baseEnd_6421310 := by
    simpa [prefixWord, tailWord_6421310, baseEnd_6421310] using wordTrace_append hprefix tailTrace_6421310
  have hstable : (prefixWord ++ tailWord_6421310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421310).length < 2 ^ (prefixWord ++ tailWord_6421310).sum := by decide
  have hdescent : baseEnd_6421310 < baseStart_6421310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421343 : List Nat := [1, 1, 2, 3, 1, 3, 2, 4, 1, 1, 4]
def baseStart_6421343 : Nat := 118140960795 + 6421343 * 2 ^ 59
def prefixEnd_6421343 : Nat := 4983230072969 + 3 ^ 40 * 6421343 * 2
def baseEnd_6421343 : Nat := 3297235406383975199681287

theorem tailTrace_6421343 : CollatzResearch.WordTrace tailWord_6421343 prefixEnd_6421343 3297235406383975199681287 := by
  unfold tailWord_6421343
  simp only [CollatzResearch.WordTrace]
  refine ⟨234205619975578463918508683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156137079983718975945672455 234205619975578463918508683)
  ·
    refine ⟨351308429963367695877763025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234205619975578463918508683 351308429963367695877763025)
    ·
      refine ⟨263481322472525771908322269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351308429963367695877763025 263481322472525771908322269)
      ·
        refine ⟨98805495927197164465620851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263481322472525771908322269 98805495927197164465620851)
        ·
          refine ⟨148208243890795746698431277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98805495927197164465620851 148208243890795746698431277)
          ·
            refine ⟨55578091459048405011911729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148208243890795746698431277 55578091459048405011911729)
            ·
              refine ⟨41683568594286303758933797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55578091459048405011911729 41683568594286303758933797)
              ·
                refine ⟨7815669111428681954800087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41683568594286303758933797 7815669111428681954800087)
                ·
                  refine ⟨11723503667143022932200131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7815669111428681954800087 11723503667143022932200131)
                  ·
                    refine ⟨17585255500714534398300197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11723503667143022932200131 17585255500714534398300197)
                    ·
                      refine ⟨3297235406383975199681287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17585255500714534398300197 3297235406383975199681287)
                      ·
                        rfl

theorem cell23_6421343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_6421343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421343 prefixEnd_6421343 := by exact prefixLift 6421343
  have htrace : WordTrace (prefixWord ++ tailWord_6421343) baseStart_6421343 baseEnd_6421343 := by
    simpa [prefixWord, tailWord_6421343, baseEnd_6421343] using wordTrace_append hprefix tailTrace_6421343
  have hstable : (prefixWord ++ tailWord_6421343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421343).length < 2 ^ (prefixWord ++ tailWord_6421343).sum := by decide
  have hdescent : baseEnd_6421343 < baseStart_6421343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421347 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 2, 3, 2]
def baseStart_6421347 : Nat := 118140960795 + 6421347 * 2 ^ 59
def prefixEnd_6421347 : Nat := 4983230072969 + 3 ^ 40 * 6421347 * 2
def baseEnd_6421347 : Nat := 3297237460306593184031269

theorem tailTrace_6421347 : CollatzResearch.WordTrace tailWord_6421347 prefixEnd_6421347 3297237460306593184031269 := by
  unfold tailWord_6421347
  simp only [CollatzResearch.WordTrace]
  refine ⟨234205765867563972601654295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156137177245042648401102863 234205765867563972601654295)
  ·
    refine ⟨351308648801345958902481443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234205765867563972601654295 351308648801345958902481443)
    ·
      refine ⟨526962973202018938353722165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351308648801345958902481443 526962973202018938353722165)
      ·
        refine ⟨49402778737689275470661453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 526962973202018938353722165 49402778737689275470661453)
        ·
          refine ⟨18526042026633478301498045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49402778737689275470661453 18526042026633478301498045)
          ·
            refine ⟨6947265759987554363061767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18526042026633478301498045 6947265759987554363061767)
            ·
              refine ⟨10420898639981331544592651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6947265759987554363061767 10420898639981331544592651)
              ·
                refine ⟨15631347959971997316888977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10420898639981331544592651 15631347959971997316888977)
                ·
                  refine ⟨11723510969978997987666733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15631347959971997316888977 11723510969978997987666733)
                  ·
                    refine ⟨4396316613742124245375025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11723510969978997987666733 4396316613742124245375025)
                    ·
                      refine ⟨3297237460306593184031269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4396316613742124245375025 3297237460306593184031269)
                      ·
                        rfl

theorem cell23_6421347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 3, 2].length) (baseStart_6421347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421347 prefixEnd_6421347 := by exact prefixLift 6421347
  have htrace : WordTrace (prefixWord ++ tailWord_6421347) baseStart_6421347 baseEnd_6421347 := by
    simpa [prefixWord, tailWord_6421347, baseEnd_6421347] using wordTrace_append hprefix tailTrace_6421347
  have hstable : (prefixWord ++ tailWord_6421347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421347).length < 2 ^ (prefixWord ++ tailWord_6421347).sum := by decide
  have hdescent : baseEnd_6421347 < baseStart_6421347 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421360 : List Nat := [2, 1, 1, 1, 4, 1, 6, 1, 1, 1, 4]
def baseStart_6421360 : Nat := 118140960795 + 6421360 * 2 ^ 59
def prefixEnd_6421360 : Nat := 4983230072969 + 3 ^ 40 * 6421360 * 2
def baseEnd_6421360 : Nat := 3297244135555101633168709

theorem tailTrace_6421360 : CollatzResearch.WordTrace tailWord_6421360 prefixEnd_6421360 3297244135555101633168709 := by
  unfold tailWord_6421360
  simp only [CollatzResearch.WordTrace]
  refine ⟨117103120008258437910938767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156137493344344583881251689 117103120008258437910938767)
  ·
    refine ⟨175654680012387656866408151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117103120008258437910938767 175654680012387656866408151)
    ·
      refine ⟨263482020018581485299612227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175654680012387656866408151 263482020018581485299612227)
      ·
        refine ⟨395223030027872227949418341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263482020018581485299612227 395223030027872227949418341)
        ·
          refine ⟨74104318130226042740515939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 395223030027872227949418341 74104318130226042740515939)
          ·
            refine ⟨111156477195339064110773909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74104318130226042740515939 111156477195339064110773909)
            ·
              refine ⟨5210459868531518630192527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111156477195339064110773909 5210459868531518630192527)
              ·
                refine ⟨7815689802797277945288791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5210459868531518630192527 7815689802797277945288791)
                ·
                  refine ⟨11723534704195916917933187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7815689802797277945288791 11723534704195916917933187)
                  ·
                    refine ⟨17585302056293875376899781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11723534704195916917933187 17585302056293875376899781)
                    ·
                      refine ⟨3297244135555101633168709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17585302056293875376899781 3297244135555101633168709)
                      ·
                        rfl

theorem cell23_6421360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 6, 1, 1, 1, 4].length) (baseStart_6421360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421360 prefixEnd_6421360 := by exact prefixLift 6421360
  have htrace : WordTrace (prefixWord ++ tailWord_6421360) baseStart_6421360 baseEnd_6421360 := by
    simpa [prefixWord, tailWord_6421360, baseEnd_6421360] using wordTrace_append hprefix tailTrace_6421360
  have hstable : (prefixWord ++ tailWord_6421360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421360).length < 2 ^ (prefixWord ++ tailWord_6421360).sum := by decide
  have hdescent : baseEnd_6421360 < baseStart_6421360 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421450 : List Nat := [3, 1, 2, 1, 2, 1, 1, 5, 1, 4, 2]
def baseStart_6421450 : Nat := 118140960795 + 6421450 * 2 ^ 59
def prefixEnd_6421450 : Nat := 4983230072969 + 3 ^ 40 * 6421450 * 2
def baseEnd_6421450 : Nat := 3297290348814006281043295

theorem tailTrace_6421450 : CollatzResearch.WordTrace tailWord_6421450 prefixEnd_6421450 3297290348814006281043295 := by
  unfold tailWord_6421450
  simp only [CollatzResearch.WordTrace]
  refine ⟨58552380646547705298163451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156139681724127214128435869 58552380646547705298163451)
  ·
    refine ⟨87828570969821557947245177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58552380646547705298163451 87828570969821557947245177)
    ·
      refine ⟨65871428227366168460433883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87828570969821557947245177 65871428227366168460433883)
      ·
        refine ⟨98807142341049252690650825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65871428227366168460433883 98807142341049252690650825)
        ·
          refine ⟨74105356755786939517988119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98807142341049252690650825 74105356755786939517988119)
          ·
            refine ⟨111158035133680409276982179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74105356755786939517988119 111158035133680409276982179)
            ·
              refine ⟨166737052700520613915473269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111158035133680409276982179 166737052700520613915473269)
              ·
                refine ⟨15631598690673807554575619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166737052700520613915473269 15631598690673807554575619)
                ·
                  refine ⟨23447398036010711331863429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15631598690673807554575619 23447398036010711331863429)
                  ·
                    refine ⟨4396387131752008374724393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23447398036010711331863429 4396387131752008374724393)
                    ·
                      refine ⟨3297290348814006281043295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4396387131752008374724393 3297290348814006281043295)
                      ·
                        rfl

theorem cell23_6421450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_6421450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421450 prefixEnd_6421450 := by exact prefixLift 6421450
  have htrace : WordTrace (prefixWord ++ tailWord_6421450) baseStart_6421450 baseEnd_6421450 := by
    simpa [prefixWord, tailWord_6421450, baseEnd_6421450] using wordTrace_append hprefix tailTrace_6421450
  have hstable : (prefixWord ++ tailWord_6421450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421450).length < 2 ^ (prefixWord ++ tailWord_6421450).sum := by decide
  have hdescent : baseEnd_6421450 < baseStart_6421450 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421454 : List Nat := [4, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2]
def baseStart_6421454 : Nat := 118140960795 + 6421454 * 2 ^ 59
def prefixEnd_6421454 : Nat := 4983230072969 + 3 ^ 40 * 6421454 * 2
def baseEnd_6421454 : Nat := 3297292402736624265393277

theorem tailTrace_6421454 : CollatzResearch.WordTrace tailWord_6421454 prefixEnd_6421454 3297292402736624265393277 := by
  unfold tailWord_6421454
  simp only [CollatzResearch.WordTrace]
  refine ⟨29276208559772041234474927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156139778985450886583866277 29276208559772041234474927)
  ·
    refine ⟨43914312839658061851712391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29276208559772041234474927 43914312839658061851712391)
    ·
      refine ⟨65871469259487092777568587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43914312839658061851712391 65871469259487092777568587)
      ·
        refine ⟨98807203889230639166352881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65871469259487092777568587 98807203889230639166352881)
        ·
          refine ⟨74105402916922979374764661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98807203889230639166352881 74105402916922979374764661)
          ·
            refine ⟨6947381523461529316384187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74105402916922979374764661 6947381523461529316384187)
            ·
              refine ⟨10421072285192293974576281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6947381523461529316384187 10421072285192293974576281)
              ·
                refine ⟨7815804213894220480932211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10421072285192293974576281 7815804213894220480932211)
                ·
                  refine ⟨11723706320841330721398317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7815804213894220480932211 11723706320841330721398317)
                  ·
                    refine ⟨4396389870315499020524369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11723706320841330721398317 4396389870315499020524369)
                    ·
                      refine ⟨3297292402736624265393277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4396389870315499020524369 3297292402736624265393277)
                      ·
                        rfl

theorem cell23_6421454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_6421454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421454 prefixEnd_6421454 := by exact prefixLift 6421454
  have htrace : WordTrace (prefixWord ++ tailWord_6421454) baseStart_6421454 baseEnd_6421454 := by
    simpa [prefixWord, tailWord_6421454, baseEnd_6421454] using wordTrace_append hprefix tailTrace_6421454
  have hstable : (prefixWord ++ tailWord_6421454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421454).length < 2 ^ (prefixWord ++ tailWord_6421454).sum := by decide
  have hdescent : baseEnd_6421454 < baseStart_6421454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421456 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 9]
def baseStart_6421456 : Nat := 118140960795 + 6421456 * 2 ^ 59
def prefixEnd_6421456 : Nat := 4983230072969 + 3 ^ 40 * 6421456 * 2
def baseEnd_6421456 : Nat := 366365936633103695285363

theorem tailTrace_6421456 : CollatzResearch.WordTrace tailWord_6421456 prefixEnd_6421456 366365936633103695285363 := by
  unfold tailWord_6421456
  simp only [CollatzResearch.WordTrace]
  refine ⟨117104870712084542108686111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156139827616112722811581481 117104870712084542108686111)
  ·
    refine ⟨175657306068126813163029167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117104870712084542108686111 175657306068126813163029167)
    ·
      refine ⟨263485959102190219744543751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175657306068126813163029167 263485959102190219744543751)
      ·
        refine ⟨395228938653285329616815627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263485959102190219744543751 395228938653285329616815627)
        ·
          refine ⟨592843407979927994425223441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395228938653285329616815627 592843407979927994425223441)
          ·
            refine ⟨444632555984945995818917581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 592843407979927994425223441 444632555984945995818917581)
            ·
              refine ⟨166737208494354748432094093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 444632555984945995818917581 166737208494354748432094093)
              ·
                refine ⟨62526453185383030662035285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 166737208494354748432094093 62526453185383030662035285)
                ·
                  refine ⟨366365936633103695285363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 62526453185383030662035285 366365936633103695285363)
                  ·
                    rfl

theorem cell23_6421456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 9].length) (baseStart_6421456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421456 prefixEnd_6421456 := by exact prefixLift 6421456
  have htrace : WordTrace (prefixWord ++ tailWord_6421456) baseStart_6421456 baseEnd_6421456 := by
    simpa [prefixWord, tailWord_6421456, baseEnd_6421456] using wordTrace_append hprefix tailTrace_6421456
  have hstable : (prefixWord ++ tailWord_6421456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421456).length < 2 ^ (prefixWord ++ tailWord_6421456).sum := by decide
  have hdescent : baseEnd_6421456 < baseStart_6421456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421500 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 2, 3, 3]
def baseStart_6421500 : Nat := 118140960795 + 6421500 * 2 ^ 59
def prefixEnd_6421500 : Nat := 4983230072969 + 3 ^ 40 * 6421500 * 2
def baseEnd_6421500 : Nat := 3297316022846731085418065

theorem tailTrace_6421500 : CollatzResearch.WordTrace tailWord_6421500 prefixEnd_6421500 3297316022846731085418065 := by
  unfold tailWord_6421500
  simp only [CollatzResearch.WordTrace]
  refine ⟨117105673118004839865986977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156140897490673119821315969 117105673118004839865986977)
  ·
    refine ⟨87829254838503629899490233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117105673118004839865986977 87829254838503629899490233)
    ·
      refine ⟨65871941128877722424617675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87829254838503629899490233 65871941128877722424617675)
      ·
        refine ⟨98807911693316583636926513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65871941128877722424617675 98807911693316583636926513)
        ·
          refine ⟨74105933769987437727694885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98807911693316583636926513 74105933769987437727694885)
          ·
            refine ⟨13894862581872644573942791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74105933769987437727694885 13894862581872644573942791)
            ·
              refine ⟨20842293872808966860914187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13894862581872644573942791 20842293872808966860914187)
              ·
                refine ⟨31263440809213450291371281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20842293872808966860914187 31263440809213450291371281)
                ·
                  refine ⟨23447580606910087718528461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31263440809213450291371281 23447580606910087718528461)
                  ·
                    refine ⟨8792842727591282894448173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23447580606910087718528461 8792842727591282894448173)
                    ·
                      refine ⟨3297316022846731085418065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8792842727591282894448173 3297316022846731085418065)
                      ·
                        rfl

theorem cell23_6421500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 2, 3, 3].length) (baseStart_6421500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421500 prefixEnd_6421500 := by exact prefixLift 6421500
  have htrace : WordTrace (prefixWord ++ tailWord_6421500) baseStart_6421500 baseEnd_6421500 := by
    simpa [prefixWord, tailWord_6421500, baseEnd_6421500] using wordTrace_append hprefix tailTrace_6421500
  have hstable : (prefixWord ++ tailWord_6421500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421500).length < 2 ^ (prefixWord ++ tailWord_6421500).sum := by decide
  have hdescent : baseEnd_6421500 < baseStart_6421500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421522 : List Nat := [3, 2, 5, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_6421522 : Nat := 118140960795 + 6421522 * 2 ^ 59
def prefixEnd_6421522 : Nat := 4983230072969 + 3 ^ 40 * 6421522 * 2
def baseEnd_6421522 : Nat := 3297327319421129999342965

theorem tailTrace_6421522 : CollatzResearch.WordTrace tailWord_6421522 prefixEnd_6421522 3297327319421129999342965 := by
  unfold tailWord_6421522
  simp only [CollatzResearch.WordTrace]
  refine ⟨58553037160482494372318705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156141432427953318326183213 58553037160482494372318705)
  ·
    refine ⟨43914777870361870779239029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58553037160482494372318705 43914777870361870779239029)
    ·
      refine ⟨4117010425346425385553659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43914777870361870779239029 4117010425346425385553659)
      ·
        refine ⟨6175515638019638078330489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4117010425346425385553659 6175515638019638078330489)
        ·
          refine ⟨4631636728514728558747867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6175515638019638078330489 4631636728514728558747867)
          ·
            refine ⟨6947455092772092838121801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4631636728514728558747867 6947455092772092838121801)
            ·
              refine ⟨5210591319579069628591351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6947455092772092838121801 5210591319579069628591351)
              ·
                refine ⟨7815886979368604442887027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5210591319579069628591351 7815886979368604442887027)
                ·
                  refine ⟨11723830469052906664330541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7815886979368604442887027 11723830469052906664330541)
                  ·
                    refine ⟨4396436425894839999123953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11723830469052906664330541 4396436425894839999123953)
                    ·
                      refine ⟨3297327319421129999342965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4396436425894839999123953 3297327319421129999342965)
                      ·
                        rfl

theorem cell23_6421522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_6421522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421522 prefixEnd_6421522 := by exact prefixLift 6421522
  have htrace : WordTrace (prefixWord ++ tailWord_6421522) baseStart_6421522 baseEnd_6421522 := by
    simpa [prefixWord, tailWord_6421522, baseEnd_6421522] using wordTrace_append hprefix tailTrace_6421522
  have hstable : (prefixWord ++ tailWord_6421522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421522).length < 2 ^ (prefixWord ++ tailWord_6421522).sum := by decide
  have hdescent : baseEnd_6421522 < baseStart_6421522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421553 : List Nat := [1, 2, 2, 3, 1, 2, 1, 2, 2, 1, 6]
def baseStart_6421553 : Nat := 118140960795 + 6421553 * 2 ^ 59
def prefixEnd_6421553 : Nat := 4983230072969 + 3 ^ 40 * 6421553 * 2
def baseEnd_6421553 : Nat := 3297343237321419378055321

theorem tailTrace_6421553 : CollatzResearch.WordTrace tailWord_6421553 prefixEnd_6421553 3297343237321419378055321 := by
  unfold tailWord_6421553
  simp only [CollatzResearch.WordTrace]
  refine ⟨234213279304817669783653313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156142186203211779855768875 234213279304817669783653313)
  ·
    refine ⟨175659959478613252337739985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234213279304817669783653313 175659959478613252337739985)
    ·
      refine ⟨131744969608959939253304989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175659959478613252337739985 131744969608959939253304989)
      ·
        refine ⟨49404363603359977219989371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131744969608959939253304989 49404363603359977219989371)
        ·
          refine ⟨74106545405039965829984057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49404363603359977219989371 74106545405039965829984057)
          ·
            refine ⟨55579909053779974372488043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74106545405039965829984057 55579909053779974372488043)
            ·
              refine ⟨83369863580669961558732065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55579909053779974372488043 83369863580669961558732065)
              ·
                refine ⟨62527397685502471169049049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83369863580669961558732065 62527397685502471169049049)
                ·
                  refine ⟨46895548264126853376786787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62527397685502471169049049 46895548264126853376786787)
                  ·
                    refine ⟨70343322396190280065180181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46895548264126853376786787 70343322396190280065180181)
                    ·
                      refine ⟨3297343237321419378055321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70343322396190280065180181 3297343237321419378055321)
                      ·
                        rfl

theorem cell23_6421553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_6421553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421553 prefixEnd_6421553 := by exact prefixLift 6421553
  have htrace : WordTrace (prefixWord ++ tailWord_6421553) baseStart_6421553 baseEnd_6421553 := by
    simpa [prefixWord, tailWord_6421553, baseEnd_6421553] using wordTrace_append hprefix tailTrace_6421553
  have hstable : (prefixWord ++ tailWord_6421553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421553).length < 2 ^ (prefixWord ++ tailWord_6421553).sum := by decide
  have hdescent : baseEnd_6421553 < baseStart_6421553 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421560 : List Nat := [2, 1, 2, 1, 5, 1, 1, 2, 1, 4, 3]
def baseStart_6421560 : Nat := 118140960795 + 6421560 * 2 ^ 59
def prefixEnd_6421560 : Nat := 4983230072969 + 3 ^ 40 * 6421560 * 2
def baseEnd_6421560 : Nat := 3297346831686000850667789

theorem tailTrace_6421560 : CollatzResearch.WordTrace tailWord_6421560 prefixEnd_6421560 3297346831686000850667789 := by
  unfold tailWord_6421560
  simp only [CollatzResearch.WordTrace]
  refine ⟨117106767307896154989579067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156142356410528206652772089 117106767307896154989579067)
  ·
    refine ⟨175660150961844232484368601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117106767307896154989579067 175660150961844232484368601)
    ·
      refine ⟨131745113221383174363276451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175660150961844232484368601 131745113221383174363276451)
      ·
        refine ⟨197617669832074761544914677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131745113221383174363276451 197617669832074761544914677)
        ·
          refine ⟨18526656546757008894835751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197617669832074761544914677 18526656546757008894835751)
          ·
            refine ⟨27789984820135513342253627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18526656546757008894835751 27789984820135513342253627)
            ·
              refine ⟨41684977230203270013380441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27789984820135513342253627 41684977230203270013380441)
              ·
                refine ⟨31263732922652452510035331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41684977230203270013380441 31263732922652452510035331)
                ·
                  refine ⟨46895599383978678765052997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31263732922652452510035331 46895599383978678765052997)
                  ·
                    refine ⟨8792924884496002268447437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46895599383978678765052997 8792924884496002268447437)
                    ·
                      refine ⟨3297346831686000850667789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8792924884496002268447437 3297346831686000850667789)
                      ·
                        rfl

theorem cell23_6421560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_6421560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421560 prefixEnd_6421560 := by exact prefixLift 6421560
  have htrace : WordTrace (prefixWord ++ tailWord_6421560) baseStart_6421560 baseEnd_6421560 := by
    simpa [prefixWord, tailWord_6421560, baseEnd_6421560] using wordTrace_append hprefix tailTrace_6421560
  have hstable : (prefixWord ++ tailWord_6421560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421560).length < 2 ^ (prefixWord ++ tailWord_6421560).sum := by decide
  have hdescent : baseEnd_6421560 < baseStart_6421560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421603 : List Nat := [1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 7]
def baseStart_6421603 : Nat := 118140960795 + 6421603 * 2 ^ 59
def prefixEnd_6421603 : Nat := 4983230072969 + 3 ^ 40 * 6421603 * 2
def baseEnd_6421603 : Nat := 3297368911354144182430091

theorem tailTrace_6421603 : CollatzResearch.WordTrace tailWord_6421603 prefixEnd_6421603 3297368911354144182430091 := by
  unfold tailWord_6421603
  simp only [CollatzResearch.WordTrace]
  refine ⟨234215102954636528322973463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156143401969757685548648975 234215102954636528322973463)
  ·
    refine ⟨351322654431954792484460195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234215102954636528322973463 351322654431954792484460195)
    ·
      refine ⟨526983981647932188726690293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351322654431954792484460195 526983981647932188726690293)
      ·
        refine ⟨49404748279493642693127215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 526983981647932188726690293 49404748279493642693127215)
        ·
          refine ⟨74107122419240464039690823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49404748279493642693127215 74107122419240464039690823)
          ·
            refine ⟨111160683628860696059536235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74107122419240464039690823 111160683628860696059536235)
            ·
              refine ⟨166741025443291044089304353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111160683628860696059536235 166741025443291044089304353)
              ·
                refine ⟨125055769082468283066978265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166741025443291044089304353 125055769082468283066978265)
                ·
                  refine ⟨93791826811851212300233699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125055769082468283066978265 93791826811851212300233699)
                  ·
                    refine ⟨140687740217776818450350549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93791826811851212300233699 140687740217776818450350549)
                    ·
                      refine ⟨3297368911354144182430091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140687740217776818450350549 3297368911354144182430091)
                      ·
                        rfl

theorem cell23_6421603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_6421603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421603 prefixEnd_6421603 := by exact prefixLift 6421603
  have htrace : WordTrace (prefixWord ++ tailWord_6421603) baseStart_6421603 baseEnd_6421603 := by
    simpa [prefixWord, tailWord_6421603, baseEnd_6421603] using wordTrace_append hprefix tailTrace_6421603
  have hstable : (prefixWord ++ tailWord_6421603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421603).length < 2 ^ (prefixWord ++ tailWord_6421603).sum := by decide
  have hdescent : baseEnd_6421603 < baseStart_6421603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421614 : List Nat := [4, 1, 2, 2, 1, 4, 2, 1, 6]
def baseStart_6421614 : Nat := 118140960795 + 6421614 * 2 ^ 59
def prefixEnd_6421614 : Nat := 4983230072969 + 3 ^ 40 * 6421614 * 2
def baseEnd_6421614 : Nat := 366374951071260404376949

theorem tailTrace_6421614 : CollatzResearch.WordTrace tailWord_6421614 prefixEnd_6421614 366374951071260404376949 := by
  unfold tailWord_6421614
  simp only [CollatzResearch.WordTrace]
  refine ⟨29276938019699584650202987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156143669438397784801082597 29276938019699584650202987)
  ·
    refine ⟨43915407029549376975304481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29276938019699584650202987 43915407029549376975304481)
    ·
      refine ⟨32936555272162032731478361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43915407029549376975304481 32936555272162032731478361)
      ·
        refine ⟨24702416454121524548608771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32936555272162032731478361 24702416454121524548608771)
        ·
          refine ⟨37053624681182286822913157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24702416454121524548608771 37053624681182286822913157)
          ·
            refine ⟨6947554627721678779296217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37053624681182286822913157 6947554627721678779296217)
            ·
              refine ⟨5210665970791259084472163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6947554627721678779296217 5210665970791259084472163)
              ·
                refine ⟨7815998956186888626708245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5210665970791259084472163 7815998956186888626708245)
                ·
                  refine ⟨366374951071260404376949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7815998956186888626708245 366374951071260404376949)
                  ·
                    rfl

theorem cell23_6421614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_6421614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421614 prefixEnd_6421614 := by exact prefixLift 6421614
  have htrace : WordTrace (prefixWord ++ tailWord_6421614) baseStart_6421614 baseEnd_6421614 := by
    simpa [prefixWord, tailWord_6421614, baseEnd_6421614] using wordTrace_append hprefix tailTrace_6421614
  have hstable : (prefixWord ++ tailWord_6421614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421614).length < 2 ^ (prefixWord ++ tailWord_6421614).sum := by decide
  have hdescent : baseEnd_6421614 < baseStart_6421614 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421658 : List Nat := [3, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3]
def baseStart_6421658 : Nat := 118140960795 + 6421658 * 2 ^ 59
def prefixEnd_6421658 : Nat := 4983230072969 + 3 ^ 40 * 6421658 * 2
def baseEnd_6421658 : Nat := 3297397152790141467242339

theorem tailTrace_6421658 : CollatzResearch.WordTrace tailWord_6421658 prefixEnd_6421658 3297397152790141467242339 := by
  unfold tailWord_6421658
  simp only [CollatzResearch.WordTrace]
  refine ⟨58554277242359318179056407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156144739312958181810817085 58554277242359318179056407)
  ·
    refine ⟨87831415863538977268584611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58554277242359318179056407 87831415863538977268584611)
    ·
      refine ⟨131747123795308465902876917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87831415863538977268584611 131747123795308465902876917)
      ·
        refine ⟨12351292855810168678394711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131747123795308465902876917 12351292855810168678394711)
        ·
          refine ⟨18526939283715253017592067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12351292855810168678394711 18526939283715253017592067)
          ·
            refine ⟨27790408925572879526388101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18526939283715253017592067 27790408925572879526388101)
            ·
              refine ⟨5210701673544914911197769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27790408925572879526388101 5210701673544914911197769)
              ·
                refine ⟨3908026255158686183398327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5210701673544914911197769 3908026255158686183398327)
                ·
                  refine ⟨5862039382738029275097491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3908026255158686183398327 5862039382738029275097491)
                  ·
                    refine ⟨8793059074107043912646237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5862039382738029275097491 8793059074107043912646237)
                    ·
                      refine ⟨3297397152790141467242339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8793059074107043912646237 3297397152790141467242339)
                      ·
                        rfl

theorem cell23_6421658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_6421658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421658 prefixEnd_6421658 := by exact prefixLift 6421658
  have htrace : WordTrace (prefixWord ++ tailWord_6421658) baseStart_6421658 baseEnd_6421658 := by
    simpa [prefixWord, tailWord_6421658, baseEnd_6421658] using wordTrace_append hprefix tailTrace_6421658
  have hstable : (prefixWord ++ tailWord_6421658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421658).length < 2 ^ (prefixWord ++ tailWord_6421658).sum := by decide
  have hdescent : baseEnd_6421658 < baseStart_6421658 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421664 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 3, 2, 2]
def baseStart_6421664 : Nat := 118140960795 + 6421664 * 2 ^ 59
def prefixEnd_6421664 : Nat := 4983230072969 + 3 ^ 40 * 6421664 * 2
def baseEnd_6421664 : Nat := 3297400233674068443767311

theorem tailTrace_6421664 : CollatzResearch.WordTrace tailWord_6421664 prefixEnd_6421664 3297400233674068443767311 := by
  unfold tailWord_6421664
  simp only [CollatzResearch.WordTrace]
  refine ⟨117108663903707767870472023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156144885204943690493962697 117108663903707767870472023)
  ·
    refine ⟨175662995855561651805708035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117108663903707767870472023 175662995855561651805708035)
    ·
      refine ⟨263494493783342477708562053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175662995855561651805708035 263494493783342477708562053)
      ·
        refine ⟨49405217584376714570355385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263494493783342477708562053 49405217584376714570355385)
        ·
          refine ⟨37053913188282535927766539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49405217584376714570355385 37053913188282535927766539)
          ·
            refine ⟨55580869782423803891649809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37053913188282535927766539 55580869782423803891649809)
            ·
              refine ⟨41685652336817852918737357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55580869782423803891649809 41685652336817852918737357)
              ·
                refine ⟨15632119626306694844526509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41685652336817852918737357 15632119626306694844526509)
                ·
                  refine ⟨5862044859865010566697441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15632119626306694844526509 5862044859865010566697441)
                  ·
                    refine ⟨4396533644898757925023081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5862044859865010566697441 4396533644898757925023081)
                    ·
                      refine ⟨3297400233674068443767311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4396533644898757925023081 3297400233674068443767311)
                      ·
                        rfl

theorem cell23_6421664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_6421664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421664 prefixEnd_6421664 := by exact prefixLift 6421664
  have htrace : WordTrace (prefixWord ++ tailWord_6421664) baseStart_6421664 baseEnd_6421664 := by
    simpa [prefixWord, tailWord_6421664, baseEnd_6421664] using wordTrace_append hprefix tailTrace_6421664
  have hstable : (prefixWord ++ tailWord_6421664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421664).length < 2 ^ (prefixWord ++ tailWord_6421664).sum := by decide
  have hdescent : baseEnd_6421664 < baseStart_6421664 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421674 : List Nat := [3, 1, 5, 1, 1, 2, 2, 1, 1, 6]
def baseStart_6421674 : Nat := 118140960795 + 6421674 * 2 ^ 59
def prefixEnd_6421674 : Nat := 4983230072969 + 3 ^ 40 * 6421674 * 2
def baseEnd_6421674 : Nat := 1099135122826871134880755

theorem tailTrace_6421674 : CollatzResearch.WordTrace tailWord_6421674 prefixEnd_6421674 1099135122826871134880755 := by
  unfold tailWord_6421674
  simp only [CollatzResearch.WordTrace]
  refine ⟨58554423134344826862202019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156145128358252871632538717 58554423134344826862202019)
  ·
    refine ⟨87831634701517240293303029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58554423134344826862202019 87831634701517240293303029)
    ·
      refine ⟨8234215753267241277497159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87831634701517240293303029 8234215753267241277497159)
      ·
        refine ⟨12351323629900861916245739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8234215753267241277497159 12351323629900861916245739)
        ·
          refine ⟨18526985444851292874368609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12351323629900861916245739 18526985444851292874368609)
          ·
            refine ⟨13895239083638469655776457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18526985444851292874368609 13895239083638469655776457)
            ·
              refine ⟨10421429312728852241832343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13895239083638469655776457 10421429312728852241832343)
              ·
                refine ⟨15632143969093278362748515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10421429312728852241832343 15632143969093278362748515)
                ·
                  refine ⟨23448215953639917544122773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15632143969093278362748515 23448215953639917544122773)
                  ·
                    refine ⟨1099135122826871134880755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23448215953639917544122773 1099135122826871134880755)
                    ·
                      rfl

theorem cell23_6421674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_6421674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421674 prefixEnd_6421674 := by exact prefixLift 6421674
  have htrace : WordTrace (prefixWord ++ tailWord_6421674) baseStart_6421674 baseEnd_6421674 := by
    simpa [prefixWord, tailWord_6421674, baseEnd_6421674] using wordTrace_append hprefix tailTrace_6421674
  have hstable : (prefixWord ++ tailWord_6421674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421674).length < 2 ^ (prefixWord ++ tailWord_6421674).sum := by decide
  have hdescent : baseEnd_6421674 < baseStart_6421674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421680 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 3]
def baseStart_6421680 : Nat := 118140960795 + 6421680 * 2 ^ 59
def prefixEnd_6421680 : Nat := 4983230072969 + 3 ^ 40 * 6421680 * 2
def baseEnd_6421680 : Nat := 3297408449364540381167237

theorem tailTrace_6421680 : CollatzResearch.WordTrace tailWord_6421680 prefixEnd_6421680 3297408449364540381167237 := by
  unfold tailWord_6421680
  simp only [CollatzResearch.WordTrace]
  refine ⟨117108955687678785236763247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156145274250238380315684329 117108955687678785236763247)
  ·
    refine ⟨175663433531518177855144871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117108955687678785236763247 175663433531518177855144871)
    ·
      refine ⟨263495150297277266782717307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175663433531518177855144871 263495150297277266782717307)
      ·
        refine ⟨395242725445915900174075961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263495150297277266782717307 395242725445915900174075961)
        ·
          refine ⟨296432044084436925130556971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395242725445915900174075961 296432044084436925130556971)
          ·
            refine ⟨444648066126655387695835457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296432044084436925130556971 444648066126655387695835457)
            ·
              refine ⟨333486049594991540771876593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444648066126655387695835457 333486049594991540771876593)
              ·
                refine ⟨250114537196243655578907445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333486049594991540771876593 250114537196243655578907445)
                ·
                  refine ⟨23448237862147842710522573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250114537196243655578907445 23448237862147842710522573)
                  ·
                    refine ⟨8793089198305441016445965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23448237862147842710522573 8793089198305441016445965)
                    ·
                      refine ⟨3297408449364540381167237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8793089198305441016445965 3297408449364540381167237)
                      ·
                        rfl

theorem cell23_6421680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 3].length) (baseStart_6421680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421680 prefixEnd_6421680 := by exact prefixLift 6421680
  have htrace : WordTrace (prefixWord ++ tailWord_6421680) baseStart_6421680 baseEnd_6421680 := by
    simpa [prefixWord, tailWord_6421680, baseEnd_6421680] using wordTrace_append hprefix tailTrace_6421680
  have hstable : (prefixWord ++ tailWord_6421680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421680).length < 2 ^ (prefixWord ++ tailWord_6421680).sum := by decide
  have hdescent : baseEnd_6421680 < baseStart_6421680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421681 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 3, 2, 2]
def baseStart_6421681 : Nat := 118140960795 + 6421681 * 2 ^ 59
def prefixEnd_6421681 : Nat := 4983230072969 + 3 ^ 40 * 6421681 * 2
def baseEnd_6421681 : Nat := 3297408962845194877254733

theorem tailTrace_6421681 : CollatzResearch.WordTrace tailWord_6421681 prefixEnd_6421681 3297408962845194877254733 := by
  unfold tailWord_6421681
  simp only [CollatzResearch.WordTrace]
  refine ⟨234217947848353947644312897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156145298565569298429541931 234217947848353947644312897)
  ·
    refine ⟨175663460886265460733234673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234217947848353947644312897 175663460886265460733234673)
    ·
      refine ⟨131747595664699095549926005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175663460886265460733234673 131747595664699095549926005)
      ·
        refine ⟨12351337093565540207805563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131747595664699095549926005 12351337093565540207805563)
        ·
          refine ⟨18527005640348310311708345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12351337093565540207805563 18527005640348310311708345)
          ·
            refine ⟨13895254230261232733781259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18527005640348310311708345 13895254230261232733781259)
            ·
              refine ⟨20842881345391849100671889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13895254230261232733781259 20842881345391849100671889)
              ·
                refine ⟨15632161009043886825503917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20842881345391849100671889 15632161009043886825503917)
                ·
                  refine ⟨5862060378391457559563969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15632161009043886825503917 5862060378391457559563969)
                  ·
                    refine ⟨4396545283793593169672977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5862060378391457559563969 4396545283793593169672977)
                    ·
                      refine ⟨3297408962845194877254733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4396545283793593169672977 3297408962845194877254733)
                      ·
                        rfl

theorem cell23_6421681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 2, 2].length) (baseStart_6421681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421681 prefixEnd_6421681 := by exact prefixLift 6421681
  have htrace : WordTrace (prefixWord ++ tailWord_6421681) baseStart_6421681 baseEnd_6421681 := by
    simpa [prefixWord, tailWord_6421681, baseEnd_6421681] using wordTrace_append hprefix tailTrace_6421681
  have hstable : (prefixWord ++ tailWord_6421681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421681).length < 2 ^ (prefixWord ++ tailWord_6421681).sum := by decide
  have hdescent : baseEnd_6421681 < baseStart_6421681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421698 : List Nat := [3, 5, 1, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_6421698 : Nat := 118140960795 + 6421698 * 2 ^ 59
def prefixEnd_6421698 : Nat := 4983230072969 + 3 ^ 40 * 6421698 * 2
def baseEnd_6421698 : Nat := 3297417692016321310742155

theorem tailTrace_6421698 : CollatzResearch.WordTrace tailWord_6421698 prefixEnd_6421698 3297417692016321310742155 := by
  unfold tailWord_6421698
  simp only [CollatzResearch.WordTrace]
  refine ⟨58554641972323089886920437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156145711926194906365121165 58554641972323089886920437)
  ·
    refine ⟨5489497684905289676898791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 58554641972323089886920437 5489497684905289676898791)
    ·
      refine ⟨8234246527357934515348187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5489497684905289676898791 8234246527357934515348187)
      ·
        refine ⟨12351369791036901773022281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8234246527357934515348187 12351369791036901773022281)
        ·
          refine ⟨9263527343277676329766711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12351369791036901773022281 9263527343277676329766711)
          ·
            refine ⟨13895291014916514494650067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9263527343277676329766711 13895291014916514494650067)
            ·
              refine ⟨20842936522374771741975101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13895291014916514494650067 20842936522374771741975101)
              ·
                refine ⟨7816101195890539403240663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20842936522374771741975101 7816101195890539403240663)
                ·
                  refine ⟨11724151793835809104860995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7816101195890539403240663 11724151793835809104860995)
                  ·
                    refine ⟨17586227690753713657291493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11724151793835809104860995 17586227690753713657291493)
                    ·
                      refine ⟨3297417692016321310742155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17586227690753713657291493 3297417692016321310742155)
                      ·
                        rfl

theorem cell23_6421698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_6421698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421698 prefixEnd_6421698 := by exact prefixLift 6421698
  have htrace : WordTrace (prefixWord ++ tailWord_6421698) baseStart_6421698 baseEnd_6421698 := by
    simpa [prefixWord, tailWord_6421698, baseEnd_6421698] using wordTrace_append hprefix tailTrace_6421698
  have hstable : (prefixWord ++ tailWord_6421698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421698).length < 2 ^ (prefixWord ++ tailWord_6421698).sum := by decide
  have hdescent : baseEnd_6421698 < baseStart_6421698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421707 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 5, 3, 2]
def baseStart_6421707 : Nat := 118140960795 + 6421707 * 2 ^ 59
def prefixEnd_6421707 : Nat := 4983230072969 + 3 ^ 40 * 6421707 * 2
def baseEnd_6421707 : Nat := 3297422313342211775529613

theorem tailTrace_6421707 : CollatzResearch.WordTrace tailWord_6421707 prefixEnd_6421707 3297422313342211775529613 := by
  unfold tailWord_6421707
  simp only [CollatzResearch.WordTrace]
  refine ⟨234218896146259754084759375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156145930764173169389839583 234218896146259754084759375)
  ·
    refine ⟨351328344219389631127139063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234218896146259754084759375 351328344219389631127139063)
    ·
      refine ⟨526992516329084446690708595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351328344219389631127139063 526992516329084446690708595)
      ·
        refine ⟨790488774493626670036062893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526992516329084446690708595 790488774493626670036062893)
        ·
          refine ⟨296433290435110001263523585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 790488774493626670036062893 296433290435110001263523585)
          ·
            refine ⟨222324967826332500947642689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296433290435110001263523585 222324967826332500947642689)
            ·
              refine ⟨166743725869749375710732017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222324967826332500947642689 166743725869749375710732017)
              ·
                refine ⟨125057794402312031783049013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166743725869749375710732017 125057794402312031783049013)
                ·
                  refine ⟨11724168225216752979660845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 125057794402312031783049013 11724168225216752979660845)
                  ·
                    refine ⟨4396563084456282367372817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11724168225216752979660845 4396563084456282367372817)
                    ·
                      refine ⟨3297422313342211775529613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4396563084456282367372817 3297422313342211775529613)
                      ·
                        rfl

theorem cell23_6421707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 3, 2].length) (baseStart_6421707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421707 prefixEnd_6421707 := by exact prefixLift 6421707
  have htrace : WordTrace (prefixWord ++ tailWord_6421707) baseStart_6421707 baseEnd_6421707 := by
    simpa [prefixWord, tailWord_6421707, baseEnd_6421707] using wordTrace_append hprefix tailTrace_6421707
  have hstable : (prefixWord ++ tailWord_6421707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421707).length < 2 ^ (prefixWord ++ tailWord_6421707).sum := by decide
  have hdescent : baseEnd_6421707 < baseStart_6421707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421714 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_6421714 : Nat := 118140960795 + 6421714 * 2 ^ 59
def prefixEnd_6421714 : Nat := 4983230072969 + 3 ^ 40 * 6421714 * 2
def baseEnd_6421714 : Nat := 3297425907706793248142081

theorem tailTrace_6421714 : CollatzResearch.WordTrace tailWord_6421714 prefixEnd_6421714 3297425907706793248142081 := by
  unfold tailWord_6421714
  simp only [CollatzResearch.WordTrace]
  refine ⟨58554787864308598570066049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156146100971489596186842797 58554787864308598570066049)
  ·
    refine ⟨43916090898231448927549537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58554787864308598570066049 43916090898231448927549537)
    ·
      refine ⟨32937068173673586695662153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43916090898231448927549537 32937068173673586695662153)
      ·
        refine ⟨24702801130255190021746615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32937068173673586695662153 24702801130255190021746615)
        ·
          refine ⟨37054201695382785032619923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24702801130255190021746615 37054201695382785032619923)
          ·
            refine ⟨55581302543074177548929885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37054201695382785032619923 55581302543074177548929885)
            ·
              refine ⟨20842988453652816580848707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55581302543074177548929885 20842988453652816580848707)
              ·
                refine ⟨31264482680479224871273061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20842988453652816580848707 31264482680479224871273061)
                ·
                  refine ⟨5862090502589854663363699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31264482680479224871273061 5862090502589854663363699)
                  ·
                    refine ⟨8793135753884781995045549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5862090502589854663363699 8793135753884781995045549)
                    ·
                      refine ⟨3297425907706793248142081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8793135753884781995045549 3297425907706793248142081)
                      ·
                        rfl

theorem cell23_6421714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_6421714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421714 prefixEnd_6421714 := by exact prefixLift 6421714
  have htrace : WordTrace (prefixWord ++ tailWord_6421714) baseStart_6421714 baseEnd_6421714 := by
    simpa [prefixWord, tailWord_6421714, baseEnd_6421714] using wordTrace_append hprefix tailTrace_6421714
  have hstable : (prefixWord ++ tailWord_6421714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421714).length < 2 ^ (prefixWord ++ tailWord_6421714).sum := by decide
  have hdescent : baseEnd_6421714 < baseStart_6421714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421741 : List Nat := [1, 5, 1, 2, 2, 1, 1, 4, 1, 3, 2]
def baseStart_6421741 : Nat := 118140960795 + 6421741 * 2 ^ 59
def prefixEnd_6421741 : Nat := 4983230072969 + 3 ^ 40 * 6421741 * 2
def baseEnd_6421741 : Nat := 3297439771684464642504457

theorem tailTrace_6421741 : CollatzResearch.WordTrace tailWord_6421741 prefixEnd_6421741 3297439771684464642504457 := by
  unfold tailWord_6421741
  simp only [CollatzResearch.WordTrace]
  refine ⟨234220136228136577891497077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156146757485424385260998051 234220136228136577891497077)
  ·
    refine ⟨21958137771387804177327851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234220136228136577891497077 21958137771387804177327851)
    ·
      refine ⟨32937206657081706265991777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21958137771387804177327851 32937206657081706265991777)
      ·
        refine ⟨24702904992811279699493833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32937206657081706265991777 24702904992811279699493833)
        ·
          refine ⟨18527178744608459774620375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24702904992811279699493833 18527178744608459774620375)
          ·
            refine ⟨27790768116912689661930563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18527178744608459774620375 27790768116912689661930563)
            ·
              refine ⟨41686152175369034492895845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27790768116912689661930563 41686152175369034492895845)
              ·
                refine ⟨7816153532881693967417971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41686152175369034492895845 7816153532881693967417971)
                ·
                  refine ⟨11724230299322540951126957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7816153532881693967417971 11724230299322540951126957)
                  ·
                    refine ⟨4396586362245952856672609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11724230299322540951126957 4396586362245952856672609)
                    ·
                      refine ⟨3297439771684464642504457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4396586362245952856672609 3297439771684464642504457)
                      ·
                        rfl

theorem cell23_6421741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_6421741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421741 prefixEnd_6421741 := by exact prefixLift 6421741
  have htrace : WordTrace (prefixWord ++ tailWord_6421741) baseStart_6421741 baseEnd_6421741 := by
    simpa [prefixWord, tailWord_6421741, baseEnd_6421741] using wordTrace_append hprefix tailTrace_6421741
  have hstable : (prefixWord ++ tailWord_6421741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421741).length < 2 ^ (prefixWord ++ tailWord_6421741).sum := by decide
  have hdescent : baseEnd_6421741 < baseStart_6421741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421754 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2]
def baseStart_6421754 : Nat := 118140960795 + 6421754 * 2 ^ 59
def prefixEnd_6421754 : Nat := 4983230072969 + 3 ^ 40 * 6421754 * 2
def baseEnd_6421754 : Nat := 3297446446932973091641897

theorem tailTrace_6421754 : CollatzResearch.WordTrace tailWord_6421754 prefixEnd_6421754 3297446446932973091641897 := by
  unfold tailWord_6421754
  simp only [CollatzResearch.WordTrace]
  refine ⟨58555152594272370277930079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156147073584726320741146877 58555152594272370277930079)
  ·
    refine ⟨87832728891408555416895119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58555152594272370277930079 87832728891408555416895119)
    ·
      refine ⟨131749093337112833125342679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87832728891408555416895119 131749093337112833125342679)
      ·
        refine ⟨197623640005669249688014019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131749093337112833125342679 197623640005669249688014019)
        ·
          refine ⟨296435460008503874532021029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197623640005669249688014019 296435460008503874532021029)
          ·
            refine ⟨55581648751594476474753943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 296435460008503874532021029 55581648751594476474753943)
            ·
              refine ⟨83372473127391714712130915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55581648751594476474753943 83372473127391714712130915)
              ·
                refine ⟨125058709691087572068196373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83372473127391714712130915 125058709691087572068196373)
                ·
                  refine ⟨5862127016769729940696705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 125058709691087572068196373 5862127016769729940696705)
                  ·
                    refine ⟨4396595262577297455522529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5862127016769729940696705 4396595262577297455522529)
                    ·
                      refine ⟨3297446446932973091641897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4396595262577297455522529 3297446446932973091641897)
                      ·
                        rfl

theorem cell23_6421754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 6, 2, 2].length) (baseStart_6421754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421754 prefixEnd_6421754 := by exact prefixLift 6421754
  have htrace : WordTrace (prefixWord ++ tailWord_6421754) baseStart_6421754 baseEnd_6421754 := by
    simpa [prefixWord, tailWord_6421754, baseEnd_6421754] using wordTrace_append hprefix tailTrace_6421754
  have hstable : (prefixWord ++ tailWord_6421754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421754).length < 2 ^ (prefixWord ++ tailWord_6421754).sum := by decide
  have hdescent : baseEnd_6421754 < baseStart_6421754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421770 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_6421770 : Nat := 118140960795 + 6421770 * 2 ^ 59
def prefixEnd_6421770 : Nat := 4983230072969 + 3 ^ 40 * 6421770 * 2
def baseEnd_6421770 : Nat := 3297454662623445029041823

theorem tailTrace_6421770 : CollatzResearch.WordTrace tailWord_6421770 prefixEnd_6421770 3297454662623445029041823 := by
  unfold tailWord_6421770
  simp only [CollatzResearch.WordTrace]
  refine ⟨58555298486257878961075691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156147462630021010562868509 58555298486257878961075691)
  ·
    refine ⟨87832947729386818441613537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58555298486257878961075691 87832947729386818441613537)
    ·
      refine ⟨65874710797040113831210153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87832947729386818441613537 65874710797040113831210153)
      ·
        refine ⟨49406033097780085373407615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65874710797040113831210153 49406033097780085373407615)
        ·
          refine ⟨74109049646670128060111423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49406033097780085373407615 74109049646670128060111423)
          ·
            refine ⟨111163574470005192090167135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74109049646670128060111423 111163574470005192090167135)
            ·
              refine ⟨166745361705007788135250703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111163574470005192090167135 166745361705007788135250703)
              ·
                refine ⟨250118042557511682202876055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166745361705007788135250703 250118042557511682202876055)
                ·
                  refine ⟨375177063836267523304314083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250118042557511682202876055 375177063836267523304314083)
                  ·
                    refine ⟨562765595754401284956471125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 375177063836267523304314083 562765595754401284956471125)
                    ·
                      refine ⟨3297454662623445029041823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 562765595754401284956471125 3297454662623445029041823)
                      ·
                        rfl

theorem cell23_6421770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_6421770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421770 prefixEnd_6421770 := by exact prefixLift 6421770
  have htrace : WordTrace (prefixWord ++ tailWord_6421770) baseStart_6421770 baseEnd_6421770 := by
    simpa [prefixWord, tailWord_6421770, baseEnd_6421770] using wordTrace_append hprefix tailTrace_6421770
  have hstable : (prefixWord ++ tailWord_6421770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421770).length < 2 ^ (prefixWord ++ tailWord_6421770).sum := by decide
  have hdescent : baseEnd_6421770 < baseStart_6421770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421788 : List Nat := [2, 2, 3, 1, 1, 1, 6, 1, 2, 2, 2]
def baseStart_6421788 : Nat := 118140960795 + 6421788 * 2 ^ 59
def prefixEnd_6421788 : Nat := 4983230072969 + 3 ^ 40 * 6421788 * 2
def baseEnd_6421788 : Nat := 3297463905275225958616741

theorem tailTrace_6421788 : CollatzResearch.WordTrace tailWord_6421788 prefixEnd_6421788 3297463905275225958616741 := by
  unfold tailWord_6421788
  simp only [CollatzResearch.WordTrace]
  refine ⟨117110925229483152459229009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156147900305977536612305345 117110925229483152459229009)
  ·
    refine ⟨87833193922112364344421757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117110925229483152459229009 87833193922112364344421757)
    ·
      refine ⟨32937447720792136629158159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87833193922112364344421757 32937447720792136629158159)
      ·
        refine ⟨49406171581188204943737239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32937447720792136629158159 49406171581188204943737239)
        ·
          refine ⟨74109257371782307415605859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49406171581188204943737239 74109257371782307415605859)
          ·
            refine ⟨111163886057673461123408789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74109257371782307415605859 111163886057673461123408789)
            ·
              refine ⟨5210807158953443490159787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111163886057673461123408789 5210807158953443490159787)
              ·
                refine ⟨7816210738430165235239681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5210807158953443490159787 7816210738430165235239681)
                ·
                  refine ⟨5862158053822623926429761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7816210738430165235239681 5862158053822623926429761)
                  ·
                    refine ⟨4396618540366967944822321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5862158053822623926429761 4396618540366967944822321)
                    ·
                      refine ⟨3297463905275225958616741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4396618540366967944822321 3297463905275225958616741)
                      ·
                        rfl

theorem cell23_6421788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 2, 2, 2].length) (baseStart_6421788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421788 prefixEnd_6421788 := by exact prefixLift 6421788
  have htrace : WordTrace (prefixWord ++ tailWord_6421788) baseStart_6421788 baseEnd_6421788 := by
    simpa [prefixWord, tailWord_6421788, baseEnd_6421788] using wordTrace_append hprefix tailTrace_6421788
  have hstable : (prefixWord ++ tailWord_6421788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421788).length < 2 ^ (prefixWord ++ tailWord_6421788).sum := by decide
  have hdescent : baseEnd_6421788 < baseStart_6421788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421828 : List Nat := [2, 3, 4, 1, 1, 1, 4, 2, 5]
def baseStart_6421828 : Nat := 118140960795 + 6421828 * 2 ^ 59
def prefixEnd_6421828 : Nat := 4983230072969 + 3 ^ 40 * 6421828 * 2
def baseEnd_6421828 : Nat := 366387160500156200235173

theorem tailTrace_6421828 : CollatzResearch.WordTrace tailWord_6421828 prefixEnd_6421828 366387160500156200235173 := by
  unfold tailWord_6421828
  simp only [CollatzResearch.WordTrace]
  refine ⟨117111654689410695874957069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156148872919214261166609425 117111654689410695874957069)
  ·
    refine ⟨43916870508529010953108901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117111654689410695874957069 43916870508529010953108901)
    ·
      refine ⟨8234413220349189553707919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43916870508529010953108901 8234413220349189553707919)
      ·
        refine ⟨12351619830523784330561879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8234413220349189553707919 12351619830523784330561879)
        ·
          refine ⟨18527429745785676495842819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12351619830523784330561879 18527429745785676495842819)
          ·
            refine ⟨27791144618678514743764229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18527429745785676495842819 27791144618678514743764229)
            ·
              refine ⟨5210839616002221514455793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27791144618678514743764229 5210839616002221514455793)
              ·
                refine ⟨3908129712001666135841845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5210839616002221514455793 3908129712001666135841845)
                ·
                  refine ⟨366387160500156200235173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3908129712001666135841845 366387160500156200235173)
                  ·
                    rfl

theorem cell23_6421828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_6421828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421828 prefixEnd_6421828 := by exact prefixLift 6421828
  have htrace : WordTrace (prefixWord ++ tailWord_6421828) baseStart_6421828 baseEnd_6421828 := by
    simpa [prefixWord, tailWord_6421828, baseEnd_6421828] using wordTrace_append hprefix tailTrace_6421828
  have hstable : (prefixWord ++ tailWord_6421828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421828).length < 2 ^ (prefixWord ++ tailWord_6421828).sum := by decide
  have hdescent : baseEnd_6421828 < baseStart_6421828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421871 : List Nat := [1, 1, 2, 1, 3, 1, 6, 3, 1, 4]
def baseStart_6421871 : Nat := 118140960795 + 6421871 * 2 ^ 59
def prefixEnd_6421871 : Nat := 4983230072969 + 3 ^ 40 * 6421871 * 2
def baseEnd_6421871 : Nat := 1099168841389849711292953

theorem tailTrace_6421871 : CollatzResearch.WordTrace tailWord_6421871 prefixEnd_6421871 1099168841389849711292953 := by
  unfold tailWord_6421871
  simp only [CollatzResearch.WordTrace]
  refine ⟨234224877717665610093729467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156149918478443740062486311 234224877717665610093729467)
  ·
    refine ⟨351337316576498415140594201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234224877717665610093729467 351337316576498415140594201)
    ·
      refine ⟨263502987432373811355445651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351337316576498415140594201 263502987432373811355445651)
      ·
        refine ⟨395254481148560717033168477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263502987432373811355445651 395254481148560717033168477)
        ·
          refine ⟨148220430430710268887438179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395254481148560717033168477 148220430430710268887438179)
          ·
            refine ⟨222330645646065403331157269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148220430430710268887438179 222330645646065403331157269)
            ·
              refine ⟨10421749014659315781147997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 222330645646065403331157269 10421749014659315781147997)
              ·
                refine ⟨3908155880497243417930499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10421749014659315781147997 3908155880497243417930499)
                ·
                  refine ⟨5862233820745865126895749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3908155880497243417930499 5862233820745865126895749)
                  ·
                    refine ⟨1099168841389849711292953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5862233820745865126895749 1099168841389849711292953)
                    ·
                      rfl

theorem cell23_6421871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 1, 4].length) (baseStart_6421871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421871 prefixEnd_6421871 := by exact prefixLift 6421871
  have htrace : WordTrace (prefixWord ++ tailWord_6421871) baseStart_6421871 baseEnd_6421871 := by
    simpa [prefixWord, tailWord_6421871, baseEnd_6421871] using wordTrace_append hprefix tailTrace_6421871
  have hstable : (prefixWord ++ tailWord_6421871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421871).length < 2 ^ (prefixWord ++ tailWord_6421871).sum := by decide
  have hdescent : baseEnd_6421871 < baseStart_6421871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421944 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 4, 4]
def baseStart_6421944 : Nat := 118140960795 + 6421944 * 2 ^ 59
def prefixEnd_6421944 : Nat := 4983230072969 + 3 ^ 40 * 6421944 * 2
def baseEnd_6421944 : Nat := 1099181336085775782755341

theorem tailTrace_6421944 : CollatzResearch.WordTrace tailWord_6421944 prefixEnd_6421944 1099181336085775782755341 := by
  unfold tailWord_6421944
  simp only [CollatzResearch.WordTrace]
  refine ⟨117113770123200571780568443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156151693497600762374091257 117113770123200571780568443)
  ·
    refine ⟨175670655184800857670852665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117113770123200571780568443 175670655184800857670852665)
    ·
      refine ⟨131752991388600643253139499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175670655184800857670852665 131752991388600643253139499)
      ·
        refine ⟨197629487082900964879709249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131752991388600643253139499 197629487082900964879709249)
        ·
          refine ⟨148222115312175723659781937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197629487082900964879709249 148222115312175723659781937)
          ·
            refine ⟨111166586484131792744836453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148222115312175723659781937 111166586484131792744836453)
            ·
              refine ⟨20843734965774711139656835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111166586484131792744836453 20843734965774711139656835)
              ·
                refine ⟨31265602448662066709485253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20843734965774711139656835 31265602448662066709485253)
                ·
                  refine ⟨5862300459124137508028485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31265602448662066709485253 5862300459124137508028485)
                  ·
                    refine ⟨1099181336085775782755341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5862300459124137508028485 1099181336085775782755341)
                    ·
                      rfl

theorem cell23_6421944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 4, 4].length) (baseStart_6421944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421944 prefixEnd_6421944 := by exact prefixLift 6421944
  have htrace : WordTrace (prefixWord ++ tailWord_6421944) baseStart_6421944 baseEnd_6421944 := by
    simpa [prefixWord, tailWord_6421944, baseEnd_6421944] using wordTrace_append hprefix tailTrace_6421944
  have hstable : (prefixWord ++ tailWord_6421944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421944).length < 2 ^ (prefixWord ++ tailWord_6421944).sum := by decide
  have hdescent : baseEnd_6421944 < baseStart_6421944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421945 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 3, 1, 3]
def baseStart_6421945 : Nat := 118140960795 + 6421945 * 2 ^ 59
def prefixEnd_6421945 : Nat := 4983230072969 + 3 ^ 40 * 6421945 * 2
def baseEnd_6421945 : Nat := 3297544521737981844353519

theorem tailTrace_6421945 : CollatzResearch.WordTrace tailWord_6421945 prefixEnd_6421945 3297544521737981844353519 := by
  unfold tailWord_6421945
  simp only [CollatzResearch.WordTrace]
  refine ⟨234227576719397520731923289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156151717812931680487948859 234227576719397520731923289)
  ·
    refine ⟨175670682539548140548942467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234227576719397520731923289 175670682539548140548942467)
    ·
      refine ⟨263506023809322210823413701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175670682539548140548942467 263506023809322210823413701)
      ·
        refine ⟨49407379464247914529390069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263506023809322210823413701 49407379464247914529390069)
        ·
          refine ⟨4631941824773241987130319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 49407379464247914529390069 4631941824773241987130319)
          ·
            refine ⟨6947912737159862980695479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4631941824773241987130319 6947912737159862980695479)
            ·
              refine ⟨10421869105739794471043219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6947912737159862980695479 10421869105739794471043219)
              ·
                refine ⟨15632803658609691706564829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10421869105739794471043219 15632803658609691706564829)
                ·
                  refine ⟨5862301371978634389961811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15632803658609691706564829 5862301371978634389961811)
                  ·
                    refine ⟨8793452057967951584942717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5862301371978634389961811 8793452057967951584942717)
                    ·
                      refine ⟨3297544521737981844353519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8793452057967951584942717 3297544521737981844353519)
                      ·
                        rfl

theorem cell23_6421945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 3, 1, 3].length) (baseStart_6421945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421945 prefixEnd_6421945 := by exact prefixLift 6421945
  have htrace : WordTrace (prefixWord ++ tailWord_6421945) baseStart_6421945 baseEnd_6421945 := by
    simpa [prefixWord, tailWord_6421945, baseEnd_6421945] using wordTrace_append hprefix tailTrace_6421945
  have hstable : (prefixWord ++ tailWord_6421945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421945).length < 2 ^ (prefixWord ++ tailWord_6421945).sum := by decide
  have hdescent : baseEnd_6421945 < baseStart_6421945 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421964 : List Nat := [2, 2, 1, 4, 2, 1, 2, 1, 1, 1, 6]
def baseStart_6421964 : Nat := 118140960795 + 6421964 * 2 ^ 59
def prefixEnd_6421964 : Nat := 4983230072969 + 3 ^ 40 * 6421964 * 2
def baseEnd_6421964 : Nat := 3297554277870417270015931

theorem tailTrace_6421964 : CollatzResearch.WordTrace tailWord_6421964 prefixEnd_6421964 3297554277870417270015931 := by
  unfold tailWord_6421964
  simp only [CollatzResearch.WordTrace]
  refine ⟨117114134853164343488432473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156152179804219124651243297 117114134853164343488432473)
  ·
    refine ⟨87835601139873257616324355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117114134853164343488432473 87835601139873257616324355)
    ·
      refine ⟨131753401709809886424486533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87835601139873257616324355 131753401709809886424486533)
      ·
        refine ⟨24703762820589353704591225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131753401709809886424486533 24703762820589353704591225)
        ·
          refine ⟨18527822115442015278443419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24703762820589353704591225 18527822115442015278443419)
          ·
            refine ⟨27791733173163022917665129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18527822115442015278443419 27791733173163022917665129)
            ·
              refine ⟨20843799879872267188248847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27791733173163022917665129 20843799879872267188248847)
              ·
                refine ⟨31265699819808400782373271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20843799879872267188248847 31265699819808400782373271)
                ·
                  refine ⟨46898549729712601173559907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31265699819808400782373271 46898549729712601173559907)
                  ·
                    refine ⟨70347824594568901760339861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46898549729712601173559907 70347824594568901760339861)
                    ·
                      refine ⟨3297554277870417270015931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70347824594568901760339861 3297554277870417270015931)
                      ·
                        rfl

theorem cell23_6421964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_6421964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421964 prefixEnd_6421964 := by exact prefixLift 6421964
  have htrace : WordTrace (prefixWord ++ tailWord_6421964) baseStart_6421964 baseEnd_6421964 := by
    simpa [prefixWord, tailWord_6421964, baseEnd_6421964] using wordTrace_append hprefix tailTrace_6421964
  have hstable : (prefixWord ++ tailWord_6421964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421964).length < 2 ^ (prefixWord ++ tailWord_6421964).sum := by decide
  have hdescent : baseEnd_6421964 < baseStart_6421964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6421981 : List Nat := [1, 4, 3, 1, 1, 3, 1, 2, 1, 2, 4]
def baseStart_6421981 : Nat := 118140960795 + 6421981 * 2 ^ 59
def prefixEnd_6421981 : Nat := 4983230072969 + 3 ^ 40 * 6421981 * 2
def baseEnd_6421981 : Nat := 3297563007041543703503353

theorem tailTrace_6421981 : CollatzResearch.WordTrace tailWord_6421981 prefixEnd_6421981 3297563007041543703503353 := by
  unfold tailWord_6421981
  simp only [CollatzResearch.WordTrace]
  refine ⟨234228889747267098880233797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156152593164844732586822531 234228889747267098880233797)
  ·
    refine ⟨43917916827612581040043837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234228889747267098880233797 43917916827612581040043837)
    ·
      refine ⟨16469218810354717890016439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43917916827612581040043837 16469218810354717890016439)
      ·
        refine ⟨24703828215532076835024659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16469218810354717890016439 24703828215532076835024659)
        ·
          refine ⟨37055742323298115252536989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24703828215532076835024659 37055742323298115252536989)
          ·
            refine ⟨13895903371236793219701371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37055742323298115252536989 13895903371236793219701371)
            ·
              refine ⟨20843855056855189829552057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13895903371236793219701371 20843855056855189829552057)
              ·
                refine ⟨15632891292641392372164043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20843855056855189829552057 15632891292641392372164043)
                ·
                  refine ⟨23449336938962088558246065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15632891292641392372164043 23449336938962088558246065)
                  ·
                    refine ⟨17587002704221566418684549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23449336938962088558246065 17587002704221566418684549)
                    ·
                      refine ⟨3297563007041543703503353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17587002704221566418684549 3297563007041543703503353)
                      ·
                        rfl

theorem cell23_6421981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_6421981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6421981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6421981 prefixEnd_6421981 := by exact prefixLift 6421981
  have htrace : WordTrace (prefixWord ++ tailWord_6421981) baseStart_6421981 baseEnd_6421981 := by
    simpa [prefixWord, tailWord_6421981, baseEnd_6421981] using wordTrace_append hprefix tailTrace_6421981
  have hstable : (prefixWord ++ tailWord_6421981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6421981).length < 2 ^ (prefixWord ++ tailWord_6421981).sum := by decide
  have hdescent : baseEnd_6421981 < baseStart_6421981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6421981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422002 : List Nat := [3, 2, 1, 4, 1, 2, 1, 4, 1, 2, 2]
def baseStart_6422002 : Nat := 118140960795 + 6422002 * 2 ^ 59
def prefixEnd_6422002 : Nat := 4983230072969 + 3 ^ 40 * 6422002 * 2
def baseEnd_6422002 : Nat := 3297573790135288121340757

theorem tailTrace_6422002 : CollatzResearch.WordTrace tailWord_6422002 prefixEnd_6422002 3297573790135288121340757 := by
  unfold tailWord_6422002
  simp only [CollatzResearch.WordTrace]
  refine ⟨58557413920047754866687065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156153103786794012977832173 58557413920047754866687065)
  ·
    refine ⟨43918060440035816150015299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58557413920047754866687065 43918060440035816150015299)
    ·
      refine ⟨65877090660053724225022949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43918060440035816150015299 65877090660053724225022949)
      ·
        refine ⟨12351954498760073292191803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65877090660053724225022949 12351954498760073292191803)
        ·
          refine ⟨18527931748140109938287705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12351954498760073292191803 18527931748140109938287705)
          ·
            refine ⟨13895948811105082453715779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18527931748140109938287705 13895948811105082453715779)
            ·
              refine ⟨20843923216657623680573669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13895948811105082453715779 20843923216657623680573669)
              ·
                refine ⟨3908235603123304440107563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20843923216657623680573669 3908235603123304440107563)
                ·
                  refine ⟨5862353404684956660161345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3908235603123304440107563 5862353404684956660161345)
                  ·
                    refine ⟨4396765053513717495121009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5862353404684956660161345 4396765053513717495121009)
                    ·
                      refine ⟨3297573790135288121340757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4396765053513717495121009 3297573790135288121340757)
                      ·
                        rfl

theorem cell23_6422002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_6422002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422002 prefixEnd_6422002 := by exact prefixLift 6422002
  have htrace : WordTrace (prefixWord ++ tailWord_6422002) baseStart_6422002 baseEnd_6422002 := by
    simpa [prefixWord, tailWord_6422002, baseEnd_6422002] using wordTrace_append hprefix tailTrace_6422002
  have hstable : (prefixWord ++ tailWord_6422002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422002).length < 2 ^ (prefixWord ++ tailWord_6422002).sum := by decide
  have hdescent : baseEnd_6422002 < baseStart_6422002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422018 : List Nat := [3, 4, 1, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_6422018 : Nat := 118140960795 + 6422018 * 2 ^ 59
def prefixEnd_6422018 : Nat := 4983230072969 + 3 ^ 40 * 6422018 * 2
def baseEnd_6422018 : Nat := 3297582005825760058740683

theorem tailTrace_6422018 : CollatzResearch.WordTrace tailWord_6422018 prefixEnd_6422018 3297582005825760058740683 := by
  unfold tailWord_6422018
  simp only [CollatzResearch.WordTrace]
  refine ⟨58557559812033263549832677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156153492832088702799553805 58557559812033263549832677)
  ·
    refine ⟨10979542464756236915593627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58557559812033263549832677 10979542464756236915593627)
    ·
      refine ⟨16469313697134355373390441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10979542464756236915593627 16469313697134355373390441)
      ·
        refine ⟨12351985272850766530042831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16469313697134355373390441 12351985272850766530042831)
        ·
          refine ⟨18527977909276149795064247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12351985272850766530042831 18527977909276149795064247)
          ·
            refine ⟨27791966863914224692596371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18527977909276149795064247 27791966863914224692596371)
            ·
              refine ⟨41687950295871337038894557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27791966863914224692596371 41687950295871337038894557)
              ·
                refine ⟨15632981360951751389585459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41687950295871337038894557 15632981360951751389585459)
                ·
                  refine ⟨23449472041427627084378189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15632981360951751389585459 23449472041427627084378189)
                  ·
                    refine ⟨8793552015535360156641821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23449472041427627084378189 8793552015535360156641821)
                    ·
                      refine ⟨3297582005825760058740683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8793552015535360156641821 3297582005825760058740683)
                      ·
                        rfl

theorem cell23_6422018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_6422018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422018 prefixEnd_6422018 := by exact prefixLift 6422018
  have htrace : WordTrace (prefixWord ++ tailWord_6422018) baseStart_6422018 baseEnd_6422018 := by
    simpa [prefixWord, tailWord_6422018, baseEnd_6422018] using wordTrace_append hprefix tailTrace_6422018
  have hstable : (prefixWord ++ tailWord_6422018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422018).length < 2 ^ (prefixWord ++ tailWord_6422018).sum := by decide
  have hdescent : baseEnd_6422018 < baseStart_6422018 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422044 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 1, 3, 5]
def baseStart_6422044 : Nat := 118140960795 + 6422044 * 2 ^ 59
def prefixEnd_6422044 : Nat := 4983230072969 + 3 ^ 40 * 6422044 * 2
def baseEnd_6422044 : Nat := 3297595356322776957015563

theorem tailTrace_6422044 : CollatzResearch.WordTrace tailWord_6422044 prefixEnd_6422044 3297595356322776957015563 := by
  unfold tailWord_6422044
  simp only [CollatzResearch.WordTrace]
  refine ⟨117115593773019430319888593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156154125030692573759851457 117115593773019430319888593)
  ·
    refine ⟨87836695329764572739916445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117115593773019430319888593 87836695329764572739916445)
    ·
      refine ⟨32938760748661714777468667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87836695329764572739916445 32938760748661714777468667)
      ·
        refine ⟨49408141122992572166203001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32938760748661714777468667 49408141122992572166203001)
        ·
          refine ⟨37056105842244429124652251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49408141122992572166203001 37056105842244429124652251)
          ·
            refine ⟨55584158763366643686978377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37056105842244429124652251 55584158763366643686978377)
            ·
              refine ⟨41688119072524982765233783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55584158763366643686978377 41688119072524982765233783)
              ·
                refine ⟨62532178608787474147850675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41688119072524982765233783 62532178608787474147850675)
                ·
                  refine ⟨93798267913181211221776013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62532178608787474147850675 93798267913181211221776013)
                  ·
                    refine ⟨35174350467442954208166005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93798267913181211221776013 35174350467442954208166005)
                    ·
                      refine ⟨3297595356322776957015563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35174350467442954208166005 3297595356322776957015563)
                      ·
                        rfl

theorem cell23_6422044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_6422044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422044 prefixEnd_6422044 := by exact prefixLift 6422044
  have htrace : WordTrace (prefixWord ++ tailWord_6422044) baseStart_6422044 baseEnd_6422044 := by
    simpa [prefixWord, tailWord_6422044, baseEnd_6422044] using wordTrace_append hprefix tailTrace_6422044
  have hstable : (prefixWord ++ tailWord_6422044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422044).length < 2 ^ (prefixWord ++ tailWord_6422044).sum := by decide
  have hdescent : baseEnd_6422044 < baseStart_6422044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422046 : List Nat := [4, 3, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_6422046 : Nat := 118140960795 + 6422046 * 2 ^ 59
def prefixEnd_6422046 : Nat := 4983230072969 + 3 ^ 40 * 6422046 * 2
def baseEnd_6422046 : Nat := 1099198794428028649730185

theorem tailTrace_6422046 : CollatzResearch.WordTrace tailWord_6422046 prefixEnd_6422046 1099198794428028649730185 := by
  unfold tailWord_6422046
  simp only [CollatzResearch.WordTrace]
  refine ⟨29278907561503951872668749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156154173661354409987566661 29278907561503951872668749)
  ·
    refine ⟨10979590335563981952250781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29278907561503951872668749 10979590335563981952250781)
    ·
      refine ⟨4117346375836493232094043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10979590335563981952250781 4117346375836493232094043)
      ·
        refine ⟨6176019563754739848141065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4117346375836493232094043 6176019563754739848141065)
        ·
          refine ⟨4632014672816054886105799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6176019563754739848141065 4632014672816054886105799)
          ·
            refine ⟨6948022009224082329158699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4632014672816054886105799 6948022009224082329158699)
            ·
              refine ⟨10422033013836123493738049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6948022009224082329158699 10422033013836123493738049)
              ·
                refine ⟨7816524760377092620303537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10422033013836123493738049 7816524760377092620303537)
                ·
                  refine ⟨5862393570282819465227653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7816524760377092620303537 5862393570282819465227653)
                  ·
                    refine ⟨1099198794428028649730185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5862393570282819465227653 1099198794428028649730185)
                    ·
                      rfl

theorem cell23_6422046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_6422046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422046 prefixEnd_6422046 := by exact prefixLift 6422046
  have htrace : WordTrace (prefixWord ++ tailWord_6422046) baseStart_6422046 baseEnd_6422046 := by
    simpa [prefixWord, tailWord_6422046, baseEnd_6422046] using wordTrace_append hprefix tailTrace_6422046
  have hstable : (prefixWord ++ tailWord_6422046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422046).length < 2 ^ (prefixWord ++ tailWord_6422046).sum := by decide
  have hdescent : baseEnd_6422046 < baseStart_6422046 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422098 : List Nat := [3, 2, 2, 1, 2, 2, 3, 3, 5]
def baseStart_6422098 : Nat := 118140960795 + 6422098 * 2 ^ 59
def prefixEnd_6422098 : Nat := 4983230072969 + 3 ^ 40 * 6422098 * 2
def baseEnd_6422098 : Nat := 366402564919791082860035

theorem tailTrace_6422098 : CollatzResearch.WordTrace tailWord_6422098 prefixEnd_6422098 366402564919791082860035 := by
  unfold tailWord_6422098
  simp only [CollatzResearch.WordTrace]
  refine ⟨58558289271960806965560737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156155438058562151908161965 58558289271960806965560737)
  ·
    refine ⟨43918716953970605224170553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58558289271960806965560737 43918716953970605224170553)
    ·
      refine ⟨32939037715477953918127915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43918716953970605224170553 32939037715477953918127915)
      ·
        refine ⟨49408556573216930877191873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32939037715477953918127915 49408556573216930877191873)
        ·
          refine ⟨37056417429912698157893905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49408556573216930877191873 37056417429912698157893905)
          ·
            refine ⟨27792313072434523618420429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37056417429912698157893905 27792313072434523618420429)
            ·
              refine ⟨10422117402162946356907661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27792313072434523618420429 10422117402162946356907661)
              ·
                refine ⟨3908294025811104883840373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10422117402162946356907661 3908294025811104883840373)
                ·
                  refine ⟨366402564919791082860035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3908294025811104883840373 366402564919791082860035)
                  ·
                    rfl

theorem cell23_6422098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 3, 5].length) (baseStart_6422098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422098 prefixEnd_6422098 := by exact prefixLift 6422098
  have htrace : WordTrace (prefixWord ++ tailWord_6422098) baseStart_6422098 baseEnd_6422098 := by
    simpa [prefixWord, tailWord_6422098, baseEnd_6422098] using wordTrace_append hprefix tailTrace_6422098
  have hstable : (prefixWord ++ tailWord_6422098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422098).length < 2 ^ (prefixWord ++ tailWord_6422098).sum := by decide
  have hdescent : baseEnd_6422098 < baseStart_6422098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422101 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 1, 7, 2]
def baseStart_6422101 : Nat := 118140960795 + 6422101 * 2 ^ 59
def prefixEnd_6422101 : Nat := 4983230072969 + 3 ^ 40 * 6422101 * 2
def baseEnd_6422101 : Nat := 3297624624720083234002801

theorem tailTrace_6422101 : CollatzResearch.WordTrace tailWord_6422101 prefixEnd_6422101 3297624624720083234002801 := by
  unfold tailWord_6422101
  simp only [CollatzResearch.WordTrace]
  refine ⟨234233266506832359374602157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156155511004554906249734771 234233266506832359374602157)
  ·
    refine ⟨87837474940062134765475809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234233266506832359374602157 87837474940062134765475809)
    ·
      refine ⟨65878106205046601074106857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87837474940062134765475809 65878106205046601074106857)
      ·
        refine ⟨49408579653784950805580143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65878106205046601074106857 49408579653784950805580143)
        ·
          refine ⟨74112869480677426208370215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49408579653784950805580143 74112869480677426208370215)
          ·
            refine ⟨111169304221016139312555323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74112869480677426208370215 111169304221016139312555323)
            ·
              refine ⟨166753956331524208968832985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111169304221016139312555323 166753956331524208968832985)
              ·
                refine ⟨125065467248643156726624739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166753956331524208968832985 125065467248643156726624739)
                ·
                  refine ⟨187598200872964735089937109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125065467248643156726624739 187598200872964735089937109)
                  ·
                    refine ⟨4396832832960110978670401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 187598200872964735089937109 4396832832960110978670401)
                    ·
                      refine ⟨3297624624720083234002801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4396832832960110978670401 3297624624720083234002801)
                      ·
                        rfl

theorem cell23_6422101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 7, 2].length) (baseStart_6422101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422101 prefixEnd_6422101 := by exact prefixLift 6422101
  have htrace : WordTrace (prefixWord ++ tailWord_6422101) baseStart_6422101 baseEnd_6422101 := by
    simpa [prefixWord, tailWord_6422101, baseEnd_6422101] using wordTrace_append hprefix tailTrace_6422101
  have hstable : (prefixWord ++ tailWord_6422101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422101).length < 2 ^ (prefixWord ++ tailWord_6422101).sum := by decide
  have hdescent : baseEnd_6422101 < baseStart_6422101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422104 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 1, 2, 5]
def baseStart_6422104 : Nat := 118140960795 + 6422104 * 2 ^ 59
def prefixEnd_6422104 : Nat := 4983230072969 + 3 ^ 40 * 6422104 * 2
def baseEnd_6422104 : Nat := 3297626165162046722265287

theorem tailTrace_6422104 : CollatzResearch.WordTrace tailWord_6422104 prefixEnd_6422104 3297626165162046722265287 := by
  unfold tailWord_6422104
  simp only [CollatzResearch.WordTrace]
  refine ⟨117116687962910745443480683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156155583950547660591307577 117116687962910745443480683)
  ·
    refine ⟨175675031944366118165221025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117116687962910745443480683 175675031944366118165221025)
    ·
      refine ⟨131756273958274588623915769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175675031944366118165221025 131756273958274588623915769)
      ·
        refine ⟨98817205468705941467936827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131756273958274588623915769 98817205468705941467936827)
        ·
          refine ⟨148225808203058912201905241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98817205468705941467936827 148225808203058912201905241)
          ·
            refine ⟨111169356152294184151428931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148225808203058912201905241 111169356152294184151428931)
            ·
              refine ⟨166754034228441276227143397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111169356152294184151428931 166754034228441276227143397)
              ·
                refine ⟨31266381417832739292589387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166754034228441276227143397 31266381417832739292589387)
                ·
                  refine ⟨46899572126749108938884081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31266381417832739292589387 46899572126749108938884081)
                  ·
                    refine ⟨35174679095061831704163061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46899572126749108938884081 35174679095061831704163061)
                    ·
                      refine ⟨3297626165162046722265287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35174679095061831704163061 3297626165162046722265287)
                      ·
                        rfl

theorem cell23_6422104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_6422104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422104 prefixEnd_6422104 := by exact prefixLift 6422104
  have htrace : WordTrace (prefixWord ++ tailWord_6422104) baseStart_6422104 baseEnd_6422104 := by
    simpa [prefixWord, tailWord_6422104, baseEnd_6422104] using wordTrace_append hprefix tailTrace_6422104
  have hstable : (prefixWord ++ tailWord_6422104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422104).length < 2 ^ (prefixWord ++ tailWord_6422104).sum := by decide
  have hdescent : baseEnd_6422104 < baseStart_6422104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422126 : List Nat := [4, 1, 2, 2, 4, 1, 2, 1, 2, 2, 2]
def baseStart_6422126 : Nat := 118140960795 + 6422126 * 2 ^ 59
def prefixEnd_6422126 : Nat := 4983230072969 + 3 ^ 40 * 6422126 * 2
def baseEnd_6422126 : Nat := 3297637461736445636190187

theorem tailTrace_6422126 : CollatzResearch.WordTrace tailWord_6422126 prefixEnd_6422126 3297637461736445636190187 := by
  unfold tailWord_6422126
  simp only [CollatzResearch.WordTrace]
  refine ⟨29279272291467723580532779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156156118887827859096174821 29279272291467723580532779)
  ·
    refine ⟨43918908437201585370799169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29279272291467723580532779 43918908437201585370799169)
    ·
      refine ⟨32939181327901189028099377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43918908437201585370799169 32939181327901189028099377)
      ·
        refine ⟨24704385995925891771074533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32939181327901189028099377 24704385995925891771074533)
        ·
          refine ⟨4632072374236104707076475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24704385995925891771074533 4632072374236104707076475)
          ·
            refine ⟨6948108561354157060614713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4632072374236104707076475 6948108561354157060614713)
            ·
              refine ⟨5211081421015617795461035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6948108561354157060614713 5211081421015617795461035)
              ·
                refine ⟨7816622131523426693191553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5211081421015617795461035 7816622131523426693191553)
                ·
                  refine ⟨5862466598642570019893665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7816622131523426693191553 5862466598642570019893665)
                  ·
                    refine ⟨4396849948981927514920249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5862466598642570019893665 4396849948981927514920249)
                    ·
                      refine ⟨3297637461736445636190187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4396849948981927514920249 3297637461736445636190187)
                      ·
                        rfl

theorem cell23_6422126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_6422126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422126 prefixEnd_6422126 := by exact prefixLift 6422126
  have htrace : WordTrace (prefixWord ++ tailWord_6422126) baseStart_6422126 baseEnd_6422126 := by
    simpa [prefixWord, tailWord_6422126, baseEnd_6422126] using wordTrace_append hprefix tailTrace_6422126
  have hstable : (prefixWord ++ tailWord_6422126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422126).length < 2 ^ (prefixWord ++ tailWord_6422126).sum := by decide
  have hdescent : baseEnd_6422126 < baseStart_6422126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422131 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 6, 4, 2]
def baseStart_6422131 : Nat := 118140960795 + 6422131 * 2 ^ 59
def prefixEnd_6422131 : Nat := 4983230072969 + 3 ^ 40 * 6422131 * 2
def baseEnd_6422131 : Nat := 3297640029139718116627663

theorem tailTrace_6422131 : CollatzResearch.WordTrace tailWord_6422131 prefixEnd_6422131 3297640029139718116627663 := by
  unfold tailWord_6422131
  simp only [CollatzResearch.WordTrace]
  refine ⟨234234360696723674498194247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156156240464482449665462831 234234360696723674498194247)
  ·
    refine ⟨351351541045085511747291371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234234360696723674498194247 351351541045085511747291371)
    ·
      refine ⟨527027311567628267620937057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351351541045085511747291371 527027311567628267620937057)
      ·
        refine ⟨395270483675721200715702793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 527027311567628267620937057 395270483675721200715702793)
        ·
          refine ⟨296452862756790900536777095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395270483675721200715702793 296452862756790900536777095)
          ·
            refine ⟨444679294135186350805165643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296452862756790900536777095 444679294135186350805165643)
            ·
              refine ⟨667018941202779526207748465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444679294135186350805165643 667018941202779526207748465)
              ·
                refine ⟨500264205902084644655811349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 667018941202779526207748465 500264205902084644655811349)
                ·
                  refine ⟨23449884651660217718241157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 500264205902084644655811349 23449884651660217718241157)
                  ·
                    refine ⟨4396853372186290822170217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23449884651660217718241157 4396853372186290822170217)
                    ·
                      refine ⟨3297640029139718116627663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4396853372186290822170217 3297640029139718116627663)
                      ·
                        rfl

theorem cell23_6422131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 4, 2].length) (baseStart_6422131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422131 prefixEnd_6422131 := by exact prefixLift 6422131
  have htrace : WordTrace (prefixWord ++ tailWord_6422131) baseStart_6422131 baseEnd_6422131 := by
    simpa [prefixWord, tailWord_6422131, baseEnd_6422131] using wordTrace_append hprefix tailTrace_6422131
  have hstable : (prefixWord ++ tailWord_6422131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422131).length < 2 ^ (prefixWord ++ tailWord_6422131).sum := by decide
  have hdescent : baseEnd_6422131 < baseStart_6422131 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422168 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 2, 2, 3]
def baseStart_6422168 : Nat := 118140960795 + 6422168 * 2 ^ 59
def prefixEnd_6422168 : Nat := 4983230072969 + 3 ^ 40 * 6422168 * 2
def baseEnd_6422168 : Nat := 3297659027923934471864993

theorem tailTrace_6422168 : CollatzResearch.WordTrace tailWord_6422168 prefixEnd_6422168 3297659027923934471864993 := by
  unfold tailWord_6422168
  simp only [CollatzResearch.WordTrace]
  refine ⟨117117855098794814908645579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156157140131726419878194105 117117855098794814908645579)
  ·
    refine ⟨175676782648192222362968369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117117855098794814908645579 175676782648192222362968369)
    ·
      refine ⟨131757586986144166772226277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175676782648192222362968369 131757586986144166772226277)
      ·
        refine ⟨24704547559902031269792427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131757586986144166772226277 24704547559902031269792427)
        ·
          refine ⟨37056821339853046904688641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24704547559902031269792427 37056821339853046904688641)
          ·
            refine ⟨27792616004889785178516481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37056821339853046904688641 27792616004889785178516481)
            ·
              refine ⟨20844462003667338883887361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27792616004889785178516481 20844462003667338883887361)
              ·
                refine ⟨15633346502750504162915521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20844462003667338883887361 15633346502750504162915521)
                ·
                  refine ⟨11725009877062878122186641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15633346502750504162915521 11725009877062878122186641)
                  ·
                    refine ⟨8793757407797158591639981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11725009877062878122186641 8793757407797158591639981)
                    ·
                      refine ⟨3297659027923934471864993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8793757407797158591639981 3297659027923934471864993)
                      ·
                        rfl

theorem cell23_6422168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_6422168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422168 prefixEnd_6422168 := by exact prefixLift 6422168
  have htrace : WordTrace (prefixWord ++ tailWord_6422168) baseStart_6422168 baseEnd_6422168 := by
    simpa [prefixWord, tailWord_6422168, baseEnd_6422168] using wordTrace_append hprefix tailTrace_6422168
  have hstable : (prefixWord ++ tailWord_6422168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422168).length < 2 ^ (prefixWord ++ tailWord_6422168).sum := by decide
  have hdescent : baseEnd_6422168 < baseStart_6422168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422201 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 3, 5]
def baseStart_6422201 : Nat := 118140960795 + 6422201 * 2 ^ 59
def prefixEnd_6422201 : Nat := 4983230072969 + 3 ^ 40 * 6422201 * 2
def baseEnd_6422201 : Nat := 1099225324261844280917447

theorem tailTrace_6422201 : CollatzResearch.WordTrace tailWord_6422201 prefixEnd_6422201 1099225324261844280917447 := by
  unfold tailWord_6422201
  simp only [CollatzResearch.WordTrace]
  refine ⟨234236913806470076453242457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156157942537646717635494971 234236913806470076453242457)
  ·
    refine ⟨175677685354852557339931843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234236913806470076453242457 175677685354852557339931843)
    ·
      refine ⟨263516528032278836009897765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175677685354852557339931843 263516528032278836009897765)
      ·
        refine ⟨49409349006052281751855831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263516528032278836009897765 49409349006052281751855831)
        ·
          refine ⟨74114023509078422627783747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49409349006052281751855831 74114023509078422627783747)
          ·
            refine ⟨111171035263617633941675621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74114023509078422627783747 111171035263617633941675621)
            ·
              refine ⟨20844569111928306364064179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111171035263617633941675621 20844569111928306364064179)
              ·
                refine ⟨31266853667892459546096269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20844569111928306364064179 31266853667892459546096269)
                ·
                  refine ⟨11725070125459672329786101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31266853667892459546096269 11725070125459672329786101)
                  ·
                    refine ⟨1099225324261844280917447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11725070125459672329786101 1099225324261844280917447)
                    ·
                      rfl

theorem cell23_6422201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 3, 5].length) (baseStart_6422201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422201 prefixEnd_6422201 := by exact prefixLift 6422201
  have htrace : WordTrace (prefixWord ++ tailWord_6422201) baseStart_6422201 baseEnd_6422201 := by
    simpa [prefixWord, tailWord_6422201, baseEnd_6422201] using wordTrace_append hprefix tailTrace_6422201
  have hstable : (prefixWord ++ tailWord_6422201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422201).length < 2 ^ (prefixWord ++ tailWord_6422201).sum := by decide
  have hdescent : baseEnd_6422201 < baseStart_6422201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422208 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 1, 5, 2]
def baseStart_6422208 : Nat := 118140960795 + 6422208 * 2 ^ 59
def prefixEnd_6422208 : Nat := 4983230072969 + 3 ^ 40 * 6422208 * 2
def baseEnd_6422208 : Nat := 3297679567150114315364809

theorem tailTrace_6422208 : CollatzResearch.WordTrace tailWord_6422208 prefixEnd_6422208 3297679567150114315364809 := by
  unfold tailWord_6422208
  simp only [CollatzResearch.WordTrace]
  refine ⟨117118584558722358324373639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156158112744963144432498185 117118584558722358324373639)
  ·
    refine ⟨175677876838083537486560459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117118584558722358324373639 175677876838083537486560459)
    ·
      refine ⟨263516815257125306229840689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175677876838083537486560459 263516815257125306229840689)
      ·
        refine ⟨197637611442843979672380517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263516815257125306229840689 197637611442843979672380517)
        ·
          refine ⟨37057052145533246188571347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197637611442843979672380517 37057052145533246188571347)
          ·
            refine ⟨55585578218299869282857021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37057052145533246188571347 55585578218299869282857021)
            ·
              refine ⟨20844591831862450981071383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55585578218299869282857021 20844591831862450981071383)
              ·
                refine ⟨31266887747793676471607075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20844591831862450981071383 31266887747793676471607075)
                ·
                  refine ⟨46900331621690514707410613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31266887747793676471607075 46900331621690514707410613)
                  ·
                    refine ⟨4396906089533485753819745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46900331621690514707410613 4396906089533485753819745)
                    ·
                      refine ⟨3297679567150114315364809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4396906089533485753819745 3297679567150114315364809)
                      ·
                        rfl

theorem cell23_6422208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 1, 5, 2].length) (baseStart_6422208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422208 prefixEnd_6422208 := by exact prefixLift 6422208
  have htrace : WordTrace (prefixWord ++ tailWord_6422208) baseStart_6422208 baseEnd_6422208 := by
    simpa [prefixWord, tailWord_6422208, baseEnd_6422208] using wordTrace_append hprefix tailTrace_6422208
  have hstable : (prefixWord ++ tailWord_6422208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422208).length < 2 ^ (prefixWord ++ tailWord_6422208).sum := by decide
  have hdescent : baseEnd_6422208 < baseStart_6422208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422248 : List Nat := [2, 1, 4, 1, 3, 1, 3, 1, 1, 6]
def baseStart_6422248 : Nat := 118140960795 + 6422248 * 2 ^ 59
def prefixEnd_6422248 : Nat := 4983230072969 + 3 ^ 40 * 6422248 * 2
def baseEnd_6422248 : Nat := 1099233368792098052954875

theorem tailTrace_6422248 : CollatzResearch.WordTrace tailWord_6422248 prefixEnd_6422248 1099233368792098052954875 := by
  unfold tailWord_6422248
  simp only [CollatzResearch.WordTrace]
  refine ⟨117119314018649901740101699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156159085358199868986802265 117119314018649901740101699)
  ·
    refine ⟨175678971027974852610152549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117119314018649901740101699 175678971027974852610152549)
    ·
      refine ⟨32939807067745284864403603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175678971027974852610152549 32939807067745284864403603)
      ·
        refine ⟨49409710601617927296605405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32939807067745284864403603 49409710601617927296605405)
        ·
          refine ⟨18528641475606722736227027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49409710601617927296605405 18528641475606722736227027)
          ·
            refine ⟨27792962213410084104340541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18528641475606722736227027 27792962213410084104340541)
            ·
              refine ⟨10422360830028781539127703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27792962213410084104340541 10422360830028781539127703)
              ·
                refine ⟨15633541245043172308691555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10422360830028781539127703 15633541245043172308691555)
                ·
                  refine ⟨23450311867564758463037333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15633541245043172308691555 23450311867564758463037333)
                  ·
                    refine ⟨1099233368792098052954875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23450311867564758463037333 1099233368792098052954875)
                    ·
                      rfl

theorem cell23_6422248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_6422248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422248 prefixEnd_6422248 := by exact prefixLift 6422248
  have htrace : WordTrace (prefixWord ++ tailWord_6422248) baseStart_6422248 baseEnd_6422248 := by
    simpa [prefixWord, tailWord_6422248, baseEnd_6422248] using wordTrace_append hprefix tailTrace_6422248
  have hstable : (prefixWord ++ tailWord_6422248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422248).length < 2 ^ (prefixWord ++ tailWord_6422248).sum := by decide
  have hdescent : baseEnd_6422248 < baseStart_6422248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422255 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 3, 2, 2]
def baseStart_6422255 : Nat := 118140960795 + 6422255 * 2 ^ 59
def prefixEnd_6422255 : Nat := 4983230072969 + 3 ^ 40 * 6422255 * 2
def baseEnd_6422255 : Nat := 3297703700740875631477093

theorem tailTrace_6422255 : CollatzResearch.WordTrace tailWord_6422255 prefixEnd_6422255 3297703700740875631477093 := by
  unfold tailWord_6422255
  simp only [CollatzResearch.WordTrace]
  refine ⟨234238883348274443675708219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156159255565516295783805479 234238883348274443675708219)
  ·
    refine ⟨351358325022411665513562329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234238883348274443675708219 351358325022411665513562329)
    ·
      refine ⟨263518743766808749135171747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351358325022411665513562329 263518743766808749135171747)
      ·
        refine ⟨395278115650213123702757621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263518743766808749135171747 395278115650213123702757621)
        ·
          refine ⟨37057323342207480347133527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 395278115650213123702757621 37057323342207480347133527)
          ·
            refine ⟨55585985013311220520700291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37057323342207480347133527 55585985013311220520700291)
            ·
              refine ⟨83378977519966830781050437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55585985013311220520700291 83378977519966830781050437)
              ·
                refine ⟨15633558284993780771446957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83378977519966830781050437 15633558284993780771446957)
                ·
                  refine ⟨5862584356872667789292609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15633558284993780771446957 5862584356872667789292609)
                  ·
                    refine ⟨4396938267654500841969457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5862584356872667789292609 4396938267654500841969457)
                    ·
                      refine ⟨3297703700740875631477093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4396938267654500841969457 3297703700740875631477093)
                      ·
                        rfl

theorem cell23_6422255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 2, 2].length) (baseStart_6422255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422255 prefixEnd_6422255 := by exact prefixLift 6422255
  have htrace : WordTrace (prefixWord ++ tailWord_6422255) baseStart_6422255 baseEnd_6422255 := by
    simpa [prefixWord, tailWord_6422255, baseEnd_6422255] using wordTrace_append hprefix tailTrace_6422255
  have hstable : (prefixWord ++ tailWord_6422255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422255).length < 2 ^ (prefixWord ++ tailWord_6422255).sum := by decide
  have hdescent : baseEnd_6422255 < baseStart_6422255 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422362 : List Nat := [3, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2]
def baseStart_6422362 : Nat := 118140960795 + 6422362 * 2 ^ 59
def prefixEnd_6422362 : Nat := 4983230072969 + 3 ^ 40 * 6422362 * 2
def baseEnd_6422362 : Nat := 3297758643170906712839101

theorem tailTrace_6422362 : CollatzResearch.WordTrace tailWord_6422362 prefixEnd_6422362 3297758643170906712839101 := by
  unfold tailWord_6422362
  simp only [CollatzResearch.WordTrace]
  refine ⟨58560696489721700237463335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156161857305924533966568893 58560696489721700237463335)
  ·
    refine ⟨87841044734582550356195003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58560696489721700237463335 87841044734582550356195003)
    ·
      refine ⟨131761567101873825534292505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87841044734582550356195003 131761567101873825534292505)
      ·
        refine ⟨98821175326405369150719379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131761567101873825534292505 98821175326405369150719379)
        ·
          refine ⟨148231762989608053726079069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98821175326405369150719379 148231762989608053726079069)
          ·
            refine ⟨55586911121103020147279651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148231762989608053726079069 55586911121103020147279651)
            ·
              refine ⟨83380366681654530220919477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55586911121103020147279651 83380366681654530220919477)
              ·
                refine ⟨7816909376405112208211201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83380366681654530220919477 7816909376405112208211201)
                ·
                  refine ⟨5862682032303834156158401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7816909376405112208211201 5862682032303834156158401)
                  ·
                    refine ⟨4397011524227875617118801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5862682032303834156158401 4397011524227875617118801)
                    ·
                      refine ⟨3297758643170906712839101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4397011524227875617118801 3297758643170906712839101)
                      ·
                        rfl

theorem cell23_6422362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_6422362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422362 prefixEnd_6422362 := by exact prefixLift 6422362
  have htrace : WordTrace (prefixWord ++ tailWord_6422362) baseStart_6422362 baseEnd_6422362 := by
    simpa [prefixWord, tailWord_6422362, baseEnd_6422362] using wordTrace_append hprefix tailTrace_6422362
  have hstable : (prefixWord ++ tailWord_6422362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422362).length < 2 ^ (prefixWord ++ tailWord_6422362).sum := by decide
  have hdescent : baseEnd_6422362 < baseStart_6422362 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422368 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 7]
def baseStart_6422368 : Nat := 118140960795 + 6422368 * 2 ^ 59
def prefixEnd_6422368 : Nat := 4983230072969 + 3 ^ 40 * 6422368 * 2
def baseEnd_6422368 : Nat := 366417969339425965484897

theorem tailTrace_6422368 : CollatzResearch.WordTrace tailWord_6422368 prefixEnd_6422368 366417969339425965484897 := by
  unfold tailWord_6422368
  simp only [CollatzResearch.WordTrace]
  refine ⟨117121502398432531987285879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156162003197910042649714505 117121502398432531987285879)
  ·
    refine ⟨175682253597648797980928819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117121502398432531987285879 175682253597648797980928819)
    ·
      refine ⟨263523380396473196971393229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175682253597648797980928819 263523380396473196971393229)
      ·
        refine ⟨98821267648677448864272461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263523380396473196971393229 98821267648677448864272461)
        ·
          refine ⟨37057975368254043324102173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98821267648677448864272461 37057975368254043324102173)
          ·
            refine ⟨13896740763095266246538315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37057975368254043324102173 13896740763095266246538315)
            ·
              refine ⟨20845111144642899369807473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13896740763095266246538315 20845111144642899369807473)
              ·
                refine ⟨15633833358482174527355605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20845111144642899369807473 15633833358482174527355605)
                ·
                  refine ⟨366417969339425965484897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15633833358482174527355605 366417969339425965484897)
                  ·
                    rfl

theorem cell23_6422368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 7].length) (baseStart_6422368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422368 prefixEnd_6422368 := by exact prefixLift 6422368
  have htrace : WordTrace (prefixWord ++ tailWord_6422368) baseStart_6422368 baseEnd_6422368 := by
    simpa [prefixWord, tailWord_6422368, baseEnd_6422368] using wordTrace_append hprefix tailTrace_6422368
  have hstable : (prefixWord ++ tailWord_6422368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422368).length < 2 ^ (prefixWord ++ tailWord_6422368).sum := by decide
  have hdescent : baseEnd_6422368 < baseStart_6422368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422385 : List Nat := [1, 2, 2, 2, 1, 3, 4, 3, 5]
def baseStart_6422385 : Nat := 118140960795 + 6422385 * 2 ^ 59
def prefixEnd_6422385 : Nat := 4983230072969 + 3 ^ 40 * 6422385 * 2
def baseEnd_6422385 : Nat := 366418939247328902539055

theorem tailTrace_6422385 : CollatzResearch.WordTrace tailWord_6422385 prefixEnd_6422385 366418939247328902539055 := by
  unfold tailWord_6422385
  simp only [CollatzResearch.WordTrace]
  refine ⟨234243624837803475877940609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156162416558535650585293739 234243624837803475877940609)
  ·
    refine ⟨175682718628352606908455457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234243624837803475877940609 175682718628352606908455457)
    ·
      refine ⟨131762038971264455181341593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175682718628352606908455457 131762038971264455181341593)
      ·
        refine ⟨98821529228448341386006195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131762038971264455181341593 98821529228448341386006195)
        ·
          refine ⟨148232293842672512079009293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98821529228448341386006195 148232293842672512079009293)
          ·
            refine ⟨55587110191002192029628485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148232293842672512079009293 55587110191002192029628485)
            ·
              refine ⟨10422583160812911005555341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55587110191002192029628485 10422583160812911005555341)
              ·
                refine ⟨3908468685304841627083253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10422583160812911005555341 3908468685304841627083253)
                ·
                  refine ⟨366418939247328902539055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3908468685304841627083253 366418939247328902539055)
                  ·
                    rfl

theorem cell23_6422385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 3, 5].length) (baseStart_6422385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422385 prefixEnd_6422385 := by exact prefixLift 6422385
  have htrace : WordTrace (prefixWord ++ tailWord_6422385) baseStart_6422385 baseEnd_6422385 := by
    simpa [prefixWord, tailWord_6422385, baseEnd_6422385] using wordTrace_append hprefix tailTrace_6422385
  have hstable : (prefixWord ++ tailWord_6422385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422385).length < 2 ^ (prefixWord ++ tailWord_6422385).sum := by decide
  have hdescent : baseEnd_6422385 < baseStart_6422385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422462 : List Nat := [4, 2, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_6422462 : Nat := 118140960795 + 6422462 * 2 ^ 59
def prefixEnd_6422462 : Nat := 4983230072969 + 3 ^ 40 * 6422462 * 2
def baseEnd_6422462 : Nat := 1099269997078785440529547

theorem tailTrace_6422462 : CollatzResearch.WordTrace tailWord_6422462 prefixEnd_6422462 1099269997078785440529547 := by
  unfold tailWord_6422462
  simp only [CollatzResearch.WordTrace]
  refine ⟨29280804157315564753561705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156164288839016345352329093 29280804157315564753561705)
  ·
    refine ⟨21960603117986673565171279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29280804157315564753561705 21960603117986673565171279)
    ·
      refine ⟨32940904676980010347756919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21960603117986673565171279 32940904676980010347756919)
      ·
        refine ⟨49411357015470015521635379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32940904676980010347756919 49411357015470015521635379)
        ·
          refine ⟨74117035523205023282453069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49411357015470015521635379 74117035523205023282453069)
          ·
            refine ⟨27793888321201883730919901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74117035523205023282453069 27793888321201883730919901)
            ·
              refine ⟨10422708120450706399094963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27793888321201883730919901 10422708120450706399094963)
              ·
                refine ⟨15634062180676059598642445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10422708120450706399094963 15634062180676059598642445)
                ·
                  refine ⟨5862773317753522349490917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15634062180676059598642445 5862773317753522349490917)
                  ·
                    refine ⟨1099269997078785440529547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5862773317753522349490917 1099269997078785440529547)
                    ·
                      rfl

theorem cell23_6422462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_6422462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422462 prefixEnd_6422462 := by exact prefixLift 6422462
  have htrace : WordTrace (prefixWord ++ tailWord_6422462) baseStart_6422462 baseEnd_6422462 := by
    simpa [prefixWord, tailWord_6422462, baseEnd_6422462] using wordTrace_append hprefix tailTrace_6422462
  have hstable : (prefixWord ++ tailWord_6422462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422462).length < 2 ^ (prefixWord ++ tailWord_6422462).sum := by decide
  have hdescent : baseEnd_6422462 < baseStart_6422462 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422509 : List Nat := [1, 5, 1, 4, 1, 1, 2, 2, 6]
def baseStart_6422509 : Nat := 118140960795 + 6422509 * 2 ^ 59
def prefixEnd_6422509 : Nat := 4983230072969 + 3 ^ 40 * 6422509 * 2
def baseEnd_6422509 : Nat := 366426013869679737522325

theorem tailTrace_6422509 : CollatzResearch.WordTrace tailWord_6422509 prefixEnd_6422509 366426013869679737522325 := by
  unfold tailWord_6422509
  simp only [CollatzResearch.WordTrace]
  refine ⟨234248147489354245055454581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156165431659569496703636387 234248147489354245055454581)
  ·
    refine ⟨21960763827126960473948867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234248147489354245055454581 21960763827126960473948867)
    ·
      refine ⟨32941145740690440710923301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21960763827126960473948867 32941145740690440710923301)
      ·
        refine ⟨6176464826379457633298119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32941145740690440710923301 6176464826379457633298119)
        ·
          refine ⟨9264697239569186449947179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6176464826379457633298119 9264697239569186449947179)
          ·
            refine ⟨13897045859353779674920769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9264697239569186449947179 13897045859353779674920769)
            ·
              refine ⟨10422784394515334756190577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13897045859353779674920769 10422784394515334756190577)
              ·
                refine ⟨7817088295886501067142933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10422784394515334756190577 7817088295886501067142933)
                ·
                  refine ⟨366426013869679737522325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7817088295886501067142933 366426013869679737522325)
                  ·
                    rfl

theorem cell23_6422509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_6422509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422509 prefixEnd_6422509 := by exact prefixLift 6422509
  have htrace : WordTrace (prefixWord ++ tailWord_6422509) baseStart_6422509 baseEnd_6422509 := by
    simpa [prefixWord, tailWord_6422509, baseEnd_6422509] using wordTrace_append hprefix tailTrace_6422509
  have hstable : (prefixWord ++ tailWord_6422509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422509).length < 2 ^ (prefixWord ++ tailWord_6422509).sum := by decide
  have hdescent : baseEnd_6422509 < baseStart_6422509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422512 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 2, 3, 2]
def baseStart_6422512 : Nat := 118140960795 + 6422512 * 2 ^ 59
def prefixEnd_6422512 : Nat := 4983230072969 + 3 ^ 40 * 6422512 * 2
def baseEnd_6422512 : Nat := 3297835665269081125963411

theorem tailTrace_6422512 : CollatzResearch.WordTrace tailWord_6422512 prefixEnd_6422512 3297835665269081125963411 := by
  unfold tailWord_6422512
  simp only [CollatzResearch.WordTrace]
  refine ⟨117124128454171688283906895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156165504605562251045209193 117124128454171688283906895)
  ·
    refine ⟨175686192681257532425860343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117124128454171688283906895 175686192681257532425860343)
    ·
      refine ⟨263529289021886298638790515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175686192681257532425860343 263529289021886298638790515)
      ·
        refine ⟨395293933532829447958185773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263529289021886298638790515 395293933532829447958185773)
        ·
          refine ⟨148235225074811042984319665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395293933532829447958185773 148235225074811042984319665)
          ·
            refine ⟨111176418806108282238239749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148235225074811042984319665 111176418806108282238239749)
            ·
              refine ⟨20845578526145302919669953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111176418806108282238239749 20845578526145302919669953)
              ·
                refine ⟨15634183894608977189752465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20845578526145302919669953 15634183894608977189752465)
                ·
                  refine ⟨11725637920956732892314349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15634183894608977189752465 11725637920956732892314349)
                  ·
                    refine ⟨4397114220358774834617881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11725637920956732892314349 4397114220358774834617881)
                    ·
                      refine ⟨3297835665269081125963411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4397114220358774834617881 3297835665269081125963411)
                      ·
                        rfl

theorem cell23_6422512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 2, 3, 2].length) (baseStart_6422512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422512 prefixEnd_6422512 := by exact prefixLift 6422512
  have htrace : WordTrace (prefixWord ++ tailWord_6422512) baseStart_6422512 baseEnd_6422512 := by
    simpa [prefixWord, tailWord_6422512, baseEnd_6422512] using wordTrace_append hprefix tailTrace_6422512
  have hstable : (prefixWord ++ tailWord_6422512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422512).length < 2 ^ (prefixWord ++ tailWord_6422512).sum := by decide
  have hdescent : baseEnd_6422512 < baseStart_6422512 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422513 : List Nat := [1, 2, 2, 2, 6, 1, 2, 2, 1, 4]
def baseStart_6422513 : Nat := 118140960795 + 6422513 * 2 ^ 59
def prefixEnd_6422513 : Nat := 4983230072969 + 3 ^ 40 * 6422513 * 2
def baseEnd_6422513 : Nat := 1099278726249911874016969

theorem tailTrace_6422513 : CollatzResearch.WordTrace tailWord_6422513 prefixEnd_6422513 1099278726249911874016969 := by
  unfold tailWord_6422513
  simp only [CollatzResearch.WordTrace]
  refine ⟨234248293381339753738600193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156165528920893169159066795 234248293381339753738600193)
  ·
    refine ⟨175686220036004815303950145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234248293381339753738600193 175686220036004815303950145)
    ·
      refine ⟨131764665027003611477962609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175686220036004815303950145 131764665027003611477962609)
      ·
        refine ⟨98823498770252708608471957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131764665027003611477962609 98823498770252708608471957)
        ·
          refine ⟨4632351504855595716022123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98823498770252708608471957 4632351504855595716022123)
          ·
            refine ⟨6948527257283393574033185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4632351504855595716022123 6948527257283393574033185)
            ·
              refine ⟨5211395442962545180524889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6948527257283393574033185 5211395442962545180524889)
              ·
                refine ⟨3908546582221908885393667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5211395442962545180524889 3908546582221908885393667)
                ·
                  refine ⟨5862819873332863328090501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3908546582221908885393667 5862819873332863328090501)
                  ·
                    refine ⟨1099278726249911874016969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5862819873332863328090501 1099278726249911874016969)
                    ·
                      rfl

theorem cell23_6422513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 1, 4].length) (baseStart_6422513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422513 prefixEnd_6422513 := by exact prefixLift 6422513
  have htrace : WordTrace (prefixWord ++ tailWord_6422513) baseStart_6422513 baseEnd_6422513 := by
    simpa [prefixWord, tailWord_6422513, baseEnd_6422513] using wordTrace_append hprefix tailTrace_6422513
  have hstable : (prefixWord ++ tailWord_6422513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422513).length < 2 ^ (prefixWord ++ tailWord_6422513).sum := by decide
  have hdescent : baseEnd_6422513 < baseStart_6422513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422525 : List Nat := [1, 4, 1, 1, 1, 2, 3, 2, 3, 1, 4]
def baseStart_6422525 : Nat := 118140960795 + 6422525 * 2 ^ 59
def prefixEnd_6422525 : Nat := 4983230072969 + 3 ^ 40 * 6422525 * 2
def baseEnd_6422525 : Nat := 3297842340517589575100851

theorem tailTrace_6422525 : CollatzResearch.WordTrace tailWord_6422525 prefixEnd_6422525 3297842340517589575100851 := by
  unfold tailWord_6422525
  simp only [CollatzResearch.WordTrace]
  refine ⟨234248731057296279788037029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156165820704864186525358019 234248731057296279788037029)
  ·
    refine ⟨43921637073243052460256943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234248731057296279788037029 43921637073243052460256943)
    ·
      refine ⟨65882455609864578690385415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43921637073243052460256943 65882455609864578690385415)
      ·
        refine ⟨98823683414796868035578123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65882455609864578690385415 98823683414796868035578123)
        ·
          refine ⟨148235525122195302053367185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98823683414796868035578123 148235525122195302053367185)
          ·
            refine ⟨111176643841646476540025389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148235525122195302053367185 111176643841646476540025389)
            ·
              refine ⟨41691241440617428702509521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111176643841646476540025389 41691241440617428702509521)
              ·
                refine ⟨31268431080463071526882141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41691241440617428702509521 31268431080463071526882141)
                ·
                  refine ⟨11725661655173651822580803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31268431080463071526882141 11725661655173651822580803)
                  ·
                    refine ⟨17588492482760477733871205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11725661655173651822580803 17588492482760477733871205)
                    ·
                      refine ⟨3297842340517589575100851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17588492482760477733871205 3297842340517589575100851)
                      ·
                        rfl

theorem cell23_6422525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_6422525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422525 prefixEnd_6422525 := by exact prefixLift 6422525
  have htrace : WordTrace (prefixWord ++ tailWord_6422525) baseStart_6422525 baseEnd_6422525 := by
    simpa [prefixWord, tailWord_6422525, baseEnd_6422525] using wordTrace_append hprefix tailTrace_6422525
  have hstable : (prefixWord ++ tailWord_6422525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422525).length < 2 ^ (prefixWord ++ tailWord_6422525).sum := by decide
  have hdescent : baseEnd_6422525 < baseStart_6422525 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422535 : List Nat := [1, 1, 4, 3, 1, 2, 1, 3, 1, 6]
def baseStart_6422535 : Nat := 118140960795 + 6422535 * 2 ^ 59
def prefixEnd_6422535 : Nat := 4983230072969 + 3 ^ 40 * 6422535 * 2
def baseEnd_6422535 : Nat := 1099282491774711511991935

theorem tailTrace_6422535 : CollatzResearch.WordTrace tailWord_6422535 prefixEnd_6422535 1099282491774711511991935 := by
  unfold tailWord_6422535
  simp only [CollatzResearch.WordTrace]
  refine ⟨234249095787260051495901059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156166063858173367663934039 234249095787260051495901059)
  ·
    refine ⟨351373643680890077243851589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234249095787260051495901059 351373643680890077243851589)
    ·
      refine ⟨65882558190166889483222173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 351373643680890077243851589 65882558190166889483222173)
      ·
        refine ⟨24705959321312583556208315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65882558190166889483222173 24705959321312583556208315)
        ·
          refine ⟨37058938981968875334312473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24705959321312583556208315 37058938981968875334312473)
          ·
            refine ⟨27794204236476656500734355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37058938981968875334312473 27794204236476656500734355)
            ·
              refine ⟨41691306354714984751101533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27794204236476656500734355 41691306354714984751101533)
              ·
                refine ⟨15634239883018119281663075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41691306354714984751101533 15634239883018119281663075)
                ·
                  refine ⟨23451359824527178922494613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15634239883018119281663075 23451359824527178922494613)
                  ·
                    refine ⟨1099282491774711511991935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23451359824527178922494613 1099282491774711511991935)
                    ·
                      rfl

theorem cell23_6422535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_6422535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422535 prefixEnd_6422535 := by exact prefixLift 6422535
  have htrace : WordTrace (prefixWord ++ tailWord_6422535) baseStart_6422535 baseEnd_6422535 := by
    simpa [prefixWord, tailWord_6422535, baseEnd_6422535] using wordTrace_append hprefix tailTrace_6422535
  have hstable : (prefixWord ++ tailWord_6422535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422535).length < 2 ^ (prefixWord ++ tailWord_6422535).sum := by decide
  have hdescent : baseEnd_6422535 < baseStart_6422535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422542 : List Nat := [4, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4]
def baseStart_6422542 : Nat := 118140960795 + 6422542 * 2 ^ 59
def prefixEnd_6422542 : Nat := 4983230072969 + 3 ^ 40 * 6422542 * 2
def baseEnd_6422542 : Nat := 3297851069688716008588273

theorem tailTrace_6422542 : CollatzResearch.WordTrace tailWord_6422542 prefixEnd_6422542 3297851069688716008588273 := by
  unfold tailWord_6422542
  simp only [CollatzResearch.WordTrace]
  refine ⟨29281168887279336461425735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156166234065489794460937253 29281168887279336461425735)
  ·
    refine ⟨43921753330919004692138603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29281168887279336461425735 43921753330919004692138603)
    ·
      refine ⟨65882629996378507038207905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43921753330919004692138603 65882629996378507038207905)
      ·
        refine ⟨49411972497283880278655929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65882629996378507038207905 49411972497283880278655929)
        ·
          refine ⟨37058979372962910208991947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49411972497283880278655929 37058979372962910208991947)
          ·
            refine ⟨55588469059444365313487921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37058979372962910208991947 55588469059444365313487921)
            ·
              refine ⟨41691351794583273985115941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55588469059444365313487921 41691351794583273985115941)
              ·
                refine ⟨7817128461484363872209239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41691351794583273985115941 7817128461484363872209239)
                ·
                  refine ⟨11725692692226545808313859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7817128461484363872209239 11725692692226545808313859)
                  ·
                    refine ⟨17588539038339818712470789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11725692692226545808313859 17588539038339818712470789)
                    ·
                      refine ⟨3297851069688716008588273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17588539038339818712470789 3297851069688716008588273)
                      ·
                        rfl

theorem cell23_6422542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_6422542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422542 prefixEnd_6422542 := by exact prefixLift 6422542
  have htrace : WordTrace (prefixWord ++ tailWord_6422542) baseStart_6422542 baseEnd_6422542 := by
    simpa [prefixWord, tailWord_6422542, baseEnd_6422542] using wordTrace_append hprefix tailTrace_6422542
  have hstable : (prefixWord ++ tailWord_6422542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422542).length < 2 ^ (prefixWord ++ tailWord_6422542).sum := by decide
  have hdescent : baseEnd_6422542 < baseStart_6422542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422576 : List Nat := [2, 1, 1, 1, 2, 5, 2, 4, 1, 2, 2]
def baseStart_6422576 : Nat := 118140960795 + 6422576 * 2 ^ 59
def prefixEnd_6422576 : Nat := 4983230072969 + 3 ^ 40 * 6422576 * 2
def baseEnd_6422576 : Nat := 3297868528030968875563117

theorem tailTrace_6422576 : CollatzResearch.WordTrace tailWord_6422576 prefixEnd_6422576 3297868528030968875563117 := by
  unfold tailWord_6422576
  simp only [CollatzResearch.WordTrace]
  refine ⟨117125295590055757749071791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156167060786741010332095721 117125295590055757749071791)
  ·
    refine ⟨175687943385083636623607687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117125295590055757749071791 175687943385083636623607687)
    ·
      refine ⟨263531915077625454935411531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175687943385083636623607687 263531915077625454935411531)
      ·
        refine ⟨395297872616438182403117297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263531915077625454935411531 395297872616438182403117297)
        ·
          refine ⟨296473404462328636802337973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395297872616438182403117297 296473404462328636802337973)
          ·
            refine ⟨27794381668343309700219185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 296473404462328636802337973 27794381668343309700219185)
            ·
              refine ⟨20845786251257482275164389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27794381668343309700219185 20845786251257482275164389)
              ·
                refine ⟨3908584922110777926593323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20845786251257482275164389 3908584922110777926593323)
                ·
                  refine ⟨5862877383166166889889985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3908584922110777926593323 5862877383166166889889985)
                  ·
                    refine ⟨4397158037374625167417489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5862877383166166889889985 4397158037374625167417489)
                    ·
                      refine ⟨3297868528030968875563117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4397158037374625167417489 3297868528030968875563117)
                      ·
                        rfl

theorem cell23_6422576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 1, 2, 2].length) (baseStart_6422576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422576 prefixEnd_6422576 := by exact prefixLift 6422576
  have htrace : WordTrace (prefixWord ++ tailWord_6422576) baseStart_6422576 baseEnd_6422576 := by
    simpa [prefixWord, tailWord_6422576, baseEnd_6422576] using wordTrace_append hprefix tailTrace_6422576
  have hstable : (prefixWord ++ tailWord_6422576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422576).length < 2 ^ (prefixWord ++ tailWord_6422576).sum := by decide
  have hdescent : baseEnd_6422576 < baseStart_6422576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422592 : List Nat := [2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 3]
def baseStart_6422592 : Nat := 118140960795 + 6422592 * 2 ^ 59
def prefixEnd_6422592 : Nat := 4983230072969 + 3 ^ 40 * 6422592 * 2
def baseEnd_6422592 : Nat := 3297876743721440812963043

theorem tailTrace_6422592 : CollatzResearch.WordTrace tailWord_6422592 prefixEnd_6422592 3297876743721440812963043 := by
  unfold tailWord_6422592
  simp only [CollatzResearch.WordTrace]
  refine ⟨117125587374026775115363015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156167449832035700153817353 117125587374026775115363015)
  ·
    refine ⟨175688381061040162673044523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117125587374026775115363015 175688381061040162673044523)
    ·
      refine ⟨263532571591560244009566785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175688381061040162673044523 263532571591560244009566785)
      ·
        refine ⟨197649428693670183007175089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263532571591560244009566785 197649428693670183007175089)
        ·
          refine ⟨148237071520252637255381317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197649428693670183007175089 148237071520252637255381317)
          ·
            refine ⟨27794450910047369485383997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148237071520252637255381317 27794450910047369485383997)
            ·
              refine ⟨10422919091267763557018999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27794450910047369485383997 10422919091267763557018999)
              ·
                refine ⟨15634378636901645335528499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10422919091267763557018999 15634378636901645335528499)
                ·
                  refine ⟨23451567955352468003292749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15634378636901645335528499 23451567955352468003292749)
                  ·
                    refine ⟨8794337983257175501234781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23451567955352468003292749 8794337983257175501234781)
                    ·
                      refine ⟨3297876743721440812963043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8794337983257175501234781 3297876743721440812963043)
                      ·
                        rfl

theorem cell23_6422592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 1, 1, 3, 3].length) (baseStart_6422592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422592 prefixEnd_6422592 := by exact prefixLift 6422592
  have htrace : WordTrace (prefixWord ++ tailWord_6422592) baseStart_6422592 baseEnd_6422592 := by
    simpa [prefixWord, tailWord_6422592, baseEnd_6422592] using wordTrace_append hprefix tailTrace_6422592
  have hstable : (prefixWord ++ tailWord_6422592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422592).length < 2 ^ (prefixWord ++ tailWord_6422592).sum := by decide
  have hdescent : baseEnd_6422592 < baseStart_6422592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422610 : List Nat := [3, 2, 2, 1, 4, 2, 1, 3, 1, 2, 2]
def baseStart_6422610 : Nat := 118140960795 + 6422610 * 2 ^ 59
def prefixEnd_6422610 : Nat := 4983230072969 + 3 ^ 40 * 6422610 * 2
def baseEnd_6422610 : Nat := 3297885986373221742537961

theorem tailTrace_6422610 : CollatzResearch.WordTrace tailWord_6422610 prefixEnd_6422610 3297885986373221742537961 := by
  unfold tailWord_6422610
  simp only [CollatzResearch.WordTrace]
  refine ⟨58562957815497084826220321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156167887507992226203254189 58562957815497084826220321)
  ·
    refine ⟨43922218361622813619665241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58562957815497084826220321 43922218361622813619665241)
    ·
      refine ⟨32941663771217110214748931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43922218361622813619665241 32941663771217110214748931)
      ·
        refine ⟨49412495656825665322123397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32941663771217110214748931 49412495656825665322123397)
        ·
          refine ⟨9264842935654812247898137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49412495656825665322123397 9264842935654812247898137)
          ·
            refine ⟨6948632201741109185923603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9264842935654812247898137 6948632201741109185923603)
            ·
              refine ⟨10422948302611663778885405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6948632201741109185923603 10422948302611663778885405)
              ·
                refine ⟨3908605613479373917082027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10422948302611663778885405 3908605613479373917082027)
                ·
                  refine ⟨5862908420219060875623041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3908605613479373917082027 5862908420219060875623041)
                  ·
                    refine ⟨4397181315164295656717281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5862908420219060875623041 4397181315164295656717281)
                    ·
                      refine ⟨3297885986373221742537961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4397181315164295656717281 3297885986373221742537961)
                      ·
                        rfl

theorem cell23_6422610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_6422610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422610 prefixEnd_6422610 := by exact prefixLift 6422610
  have htrace : WordTrace (prefixWord ++ tailWord_6422610) baseStart_6422610 baseEnd_6422610 := by
    simpa [prefixWord, tailWord_6422610, baseEnd_6422610] using wordTrace_append hprefix tailTrace_6422610
  have hstable : (prefixWord ++ tailWord_6422610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422610).length < 2 ^ (prefixWord ++ tailWord_6422610).sum := by decide
  have hdescent : baseEnd_6422610 < baseStart_6422610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422672 : List Nat := [2, 1, 1, 1, 1, 1, 6, 5, 5]
def baseStart_6422672 : Nat := 118140960795 + 6422672 * 2 ^ 59
def prefixEnd_6422672 : Nat := 4983230072969 + 3 ^ 40 * 6422672 * 2
def baseEnd_6422672 : Nat := 366435313574866722218075

theorem tailTrace_6422672 : CollatzResearch.WordTrace tailWord_6422672 prefixEnd_6422672 366435313574866722218075 := by
  unfold tailWord_6422672
  simp only [CollatzResearch.WordTrace]
  refine ⟨117127046293881861946819135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156169395058509149262425513 117127046293881861946819135)
  ·
    refine ⟨175690569440822792920228703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117127046293881861946819135 175690569440822792920228703)
    ·
      refine ⟨263535854161234189380343055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175690569440822792920228703 263535854161234189380343055)
      ·
        refine ⟨395303781241851284070514583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263535854161234189380343055 395303781241851284070514583)
        ·
          refine ⟨592955671862776926105771875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395303781241851284070514583 592955671862776926105771875)
          ·
            refine ⟨889433507794165389158657813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592955671862776926105771875 889433507794165389158657813)
            ·
              refine ⟨41692195677851502616812085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 889433507794165389158657813 41692195677851502616812085)
              ·
                refine ⟨3908643344798578370326133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41692195677851502616812085 3908643344798578370326133)
                ·
                  refine ⟨366435313574866722218075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3908643344798578370326133 366435313574866722218075)
                  ·
                    rfl

theorem cell23_6422672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 5, 5].length) (baseStart_6422672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422672 prefixEnd_6422672 := by exact prefixLift 6422672
  have htrace : WordTrace (prefixWord ++ tailWord_6422672) baseStart_6422672 baseEnd_6422672 := by
    simpa [prefixWord, tailWord_6422672, baseEnd_6422672] using wordTrace_append hprefix tailTrace_6422672
  have hstable : (prefixWord ++ tailWord_6422672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422672).length < 2 ^ (prefixWord ++ tailWord_6422672).sum := by decide
  have hdescent : baseEnd_6422672 < baseStart_6422672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422678 : List Nat := [5, 3, 2, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_6422678 : Nat := 118140960795 + 6422678 * 2 ^ 59
def prefixEnd_6422678 : Nat := 4983230072969 + 3 ^ 40 * 6422678 * 2
def baseEnd_6422678 : Nat := 3297920903057727476487649

theorem tailTrace_6422678 : CollatzResearch.WordTrace tailWord_6422678 prefixEnd_6422678 3297920903057727476487649 := by
  unfold tailWord_6422678
  simp only [CollatzResearch.WordTrace]
  refine ⟨14640894464108874182397293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156169540950494657945571125 14640894464108874182397293)
  ·
    refine ⟨5490335424040827818398985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14640894464108874182397293 5490335424040827818398985)
    ·
      refine ⟨4117751568030620863799239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5490335424040827818398985 4117751568030620863799239)
      ·
        refine ⟨6176627352045931295698859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4117751568030620863799239 6176627352045931295698859)
        ·
          refine ⟨9264941028068896943548289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6176627352045931295698859 9264941028068896943548289)
          ·
            refine ⟨6948705771051672707661217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9264941028068896943548289 6948705771051672707661217)
            ·
              refine ⟨5211529328288754530745913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6948705771051672707661217 5211529328288754530745913)
              ·
                refine ⟨3908646996216565898059435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5211529328288754530745913 3908646996216565898059435)
                ·
                  refine ⟨5862970494324848847089153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3908646996216565898059435 5862970494324848847089153)
                  ·
                    refine ⟨4397227870743636635316865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5862970494324848847089153 4397227870743636635316865)
                    ·
                      refine ⟨3297920903057727476487649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4397227870743636635316865 3297920903057727476487649)
                      ·
                        rfl

theorem cell23_6422678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_6422678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422678 prefixEnd_6422678 := by exact prefixLift 6422678
  have htrace : WordTrace (prefixWord ++ tailWord_6422678) baseStart_6422678 baseEnd_6422678 := by
    simpa [prefixWord, tailWord_6422678, baseEnd_6422678] using wordTrace_append hprefix tailTrace_6422678
  have hstable : (prefixWord ++ tailWord_6422678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422678).length < 2 ^ (prefixWord ++ tailWord_6422678).sum := by decide
  have hdescent : baseEnd_6422678 < baseStart_6422678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422689 : List Nat := [1, 2, 3, 3, 1, 3, 1, 4, 5]
def baseStart_6422689 : Nat := 118140960795 + 6422689 * 2 ^ 59
def prefixEnd_6422689 : Nat := 4983230072969 + 3 ^ 40 * 6422689 * 2
def baseEnd_6422689 : Nat := 366436283482769659272233

theorem tailTrace_6422689 : CollatzResearch.WordTrace tailWord_6422689 prefixEnd_6422689 366436283482769659272233 := by
  unfold tailWord_6422689
  simp only [CollatzResearch.WordTrace]
  refine ⟨234254712628702135797007121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156169808419134757198004747 234254712628702135797007121)
  ·
    refine ⟨175691034471526601847755341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234254712628702135797007121 175691034471526601847755341)
    ·
      refine ⟨65884137926822475692908253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175691034471526601847755341 65884137926822475692908253)
      ·
        refine ⟨24706551722558428384840595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65884137926822475692908253 24706551722558428384840595)
        ·
          refine ⟨37059827583837642577260893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24706551722558428384840595 37059827583837642577260893)
          ·
            refine ⟨13897435343939115966472835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37059827583837642577260893 13897435343939115966472835)
            ·
              refine ⟨20846153015908673949709253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13897435343939115966472835 20846153015908673949709253)
              ·
                refine ⟨3908653690482876365570485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20846153015908673949709253 3908653690482876365570485)
                ·
                  refine ⟨366436283482769659272233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3908653690482876365570485 366436283482769659272233)
                  ·
                    rfl

theorem cell23_6422689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 4, 5].length) (baseStart_6422689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422689 prefixEnd_6422689 := by exact prefixLift 6422689
  have htrace : WordTrace (prefixWord ++ tailWord_6422689) baseStart_6422689 baseEnd_6422689 := by
    simpa [prefixWord, tailWord_6422689, baseEnd_6422689] using wordTrace_append hprefix tailTrace_6422689
  have hstable : (prefixWord ++ tailWord_6422689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422689).length < 2 ^ (prefixWord ++ tailWord_6422689).sum := by decide
  have hdescent : baseEnd_6422689 < baseStart_6422689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422735 : List Nat := [1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 6]
def baseStart_6422735 : Nat := 118140960795 + 6422735 * 2 ^ 59
def prefixEnd_6422735 : Nat := 4983230072969 + 3 ^ 40 * 6422735 * 2
def baseEnd_6422735 : Nat := 3297950171455033753474885

theorem tailTrace_6422735 : CollatzResearch.WordTrace tailWord_6422735 prefixEnd_6422735 3297950171455033753474885 := by
  unfold tailWord_6422735
  simp only [CollatzResearch.WordTrace]
  refine ⟨234256390386535485653181659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156170926924356990435454439 234256390386535485653181659)
  ·
    refine ⟨351384585579803228479772489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234256390386535485653181659 351384585579803228479772489)
    ·
      refine ⟨263538439184852421359829367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351384585579803228479772489 263538439184852421359829367)
      ·
        refine ⟨395307658777278632039744051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263538439184852421359829367 395307658777278632039744051)
        ·
          refine ⟨592961488165917948059616077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395307658777278632039744051 592961488165917948059616077)
          ·
            refine ⟨222360558062219230522356029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 592961488165917948059616077 222360558062219230522356029)
            ·
              refine ⟨83385209273332211445883511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 222360558062219230522356029 83385209273332211445883511)
              ·
                refine ⟨125077813909998317168825267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83385209273332211445883511 125077813909998317168825267)
                ·
                  refine ⟨187616720864997475753237901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125077813909998317168825267 187616720864997475753237901)
                  ·
                    refine ⟨70356270324374053407464213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 187616720864997475753237901 70356270324374053407464213)
                    ·
                      refine ⟨3297950171455033753474885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70356270324374053407464213 3297950171455033753474885)
                      ·
                        rfl

theorem cell23_6422735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 1, 3, 6].length) (baseStart_6422735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422735 prefixEnd_6422735 := by exact prefixLift 6422735
  have htrace : WordTrace (prefixWord ++ tailWord_6422735) baseStart_6422735 baseEnd_6422735 := by
    simpa [prefixWord, tailWord_6422735, baseEnd_6422735] using wordTrace_append hprefix tailTrace_6422735
  have hstable : (prefixWord ++ tailWord_6422735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422735).length < 2 ^ (prefixWord ++ tailWord_6422735).sum := by decide
  have hdescent : baseEnd_6422735 < baseStart_6422735 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422759 : List Nat := [1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_6422759 : Nat := 118140960795 + 6422759 * 2 ^ 59
def prefixEnd_6422759 : Nat := 4983230072969 + 3 ^ 40 * 6422759 * 2
def baseEnd_6422759 : Nat := 3297962494990741659574775

theorem tailTrace_6422759 : CollatzResearch.WordTrace tailWord_6422759 prefixEnd_6422759 3297962494990741659574775 := by
  unfold tailWord_6422759
  simp only [CollatzResearch.WordTrace]
  refine ⟨234257265738448537752055331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156171510492299025168036887 234257265738448537752055331)
  ·
    refine ⟨351385898607672806628082997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234257265738448537752055331 351385898607672806628082997)
    ·
      refine ⟨32942427994469325621382781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 351385898607672806628082997 32942427994469325621382781)
      ·
        refine ⟨12353410497925997108018543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32942427994469325621382781 12353410497925997108018543)
        ·
          refine ⟨18530115746888995662027815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12353410497925997108018543 18530115746888995662027815)
          ·
            refine ⟨27795173620333493493041723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18530115746888995662027815 27795173620333493493041723)
            ·
              refine ⟨41692760430500240239562585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27795173620333493493041723 41692760430500240239562585)
              ·
                refine ⟨31269570322875180179671939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41692760430500240239562585 31269570322875180179671939)
                ·
                  refine ⟨46904355484312770269507909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31269570322875180179671939 46904355484312770269507909)
                  ·
                    refine ⟨8794566653308644425532733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46904355484312770269507909 8794566653308644425532733)
                    ·
                      refine ⟨3297962494990741659574775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8794566653308644425532733 3297962494990741659574775)
                      ·
                        rfl

theorem cell23_6422759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_6422759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422759 prefixEnd_6422759 := by exact prefixLift 6422759
  have htrace : WordTrace (prefixWord ++ tailWord_6422759) baseStart_6422759 baseEnd_6422759 := by
    simpa [prefixWord, tailWord_6422759, baseEnd_6422759] using wordTrace_append hprefix tailTrace_6422759
  have hstable : (prefixWord ++ tailWord_6422759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422759).length < 2 ^ (prefixWord ++ tailWord_6422759).sum := by decide
  have hdescent : baseEnd_6422759 < baseStart_6422759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422812 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 2, 5, 4]
def baseStart_6422812 : Nat := 118140960795 + 6422812 * 2 ^ 59
def prefixEnd_6422812 : Nat := 4983230072969 + 3 ^ 40 * 6422812 * 2
def baseEnd_6422812 : Nat := 3297989709465429952212031

theorem tailTrace_6422812 : CollatzResearch.WordTrace tailWord_6422812 prefixEnd_6422812 3297989709465429952212031 := by
  unfold tailWord_6422812
  simp only [CollatzResearch.WordTrace]
  refine ⟨117129599403628263901867345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156172799204837685202489793 117129599403628263901867345)
  ·
    refine ⟨87847199552721197926400509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117129599403628263901867345 87847199552721197926400509)
    ·
      refine ⟨32942699832270449222400191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87847199552721197926400509 32942699832270449222400191)
      ·
        refine ⟨49414049748405673833600287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32942699832270449222400191 49414049748405673833600287)
        ·
          refine ⟨74121074622608510750400431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49414049748405673833600287 74121074622608510750400431)
          ·
            refine ⟨111181611933912766125600647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74121074622608510750400431 111181611933912766125600647)
            ·
              refine ⟨166772417900869149188400971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111181611933912766125600647 166772417900869149188400971)
              ·
                refine ⟨250158626851303723782601457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166772417900869149188400971 250158626851303723782601457)
                ·
                  refine ⟨187618970138477792836951093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250158626851303723782601457 187618970138477792836951093)
                  ·
                    refine ⟨17589278450482293078464165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 187618970138477792836951093 17589278450482293078464165)
                    ·
                      refine ⟨3297989709465429952212031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17589278450482293078464165 3297989709465429952212031)
                      ·
                        rfl

theorem cell23_6422812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_6422812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422812 prefixEnd_6422812 := by exact prefixLift 6422812
  have htrace : WordTrace (prefixWord ++ tailWord_6422812) baseStart_6422812 baseEnd_6422812 := by
    simpa [prefixWord, tailWord_6422812, baseEnd_6422812] using wordTrace_append hprefix tailTrace_6422812
  have hstable : (prefixWord ++ tailWord_6422812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422812).length < 2 ^ (prefixWord ++ tailWord_6422812).sum := by decide
  have hdescent : baseEnd_6422812 < baseStart_6422812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422813 : List Nat := [1, 4, 2, 3, 2, 2, 2, 1, 6]
def baseStart_6422813 : Nat := 118140960795 + 6422813 * 2 ^ 59
def prefixEnd_6422813 : Nat := 4983230072969 + 3 ^ 40 * 6422813 * 2
def baseEnd_6422813 : Nat := 366443358105120494255503

theorem tailTrace_6422813 : CollatzResearch.WordTrace tailWord_6422813 prefixEnd_6422813 366443358105120494255503 := by
  unfold tailWord_6422813
  simp only [CollatzResearch.WordTrace]
  refine ⟨234259235280252904974521093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156172823520168603316347395 234259235280252904974521093)
  ·
    refine ⟨43923606615047419682722705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234259235280252904974521093 43923606615047419682722705)
    ·
      refine ⟨32942704961285564762042029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43923606615047419682722705 32942704961285564762042029)
      ·
        refine ⟨12353514360482086785765761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32942704961285564762042029 12353514360482086785765761)
        ·
          refine ⟨9265135770361565089324321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12353514360482086785765761 9265135770361565089324321)
          ·
            refine ⟨6948851827771173816993241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9265135770361565089324321 6948851827771173816993241)
            ·
              refine ⟨5211638870828380362744931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6948851827771173816993241 5211638870828380362744931)
              ·
                refine ⟨7817458306242570544117397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5211638870828380362744931 7817458306242570544117397)
                ·
                  refine ⟨366443358105120494255503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7817458306242570544117397 366443358105120494255503)
                  ·
                    rfl

theorem cell23_6422813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 6].length) (baseStart_6422813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422813 prefixEnd_6422813 := by exact prefixLift 6422813
  have htrace : WordTrace (prefixWord ++ tailWord_6422813) baseStart_6422813 baseEnd_6422813 := by
    simpa [prefixWord, tailWord_6422813, baseEnd_6422813] using wordTrace_append hprefix tailTrace_6422813
  have hstable : (prefixWord ++ tailWord_6422813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422813).length < 2 ^ (prefixWord ++ tailWord_6422813).sum := by decide
  have hdescent : baseEnd_6422813 < baseStart_6422813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422826 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 3, 5]
def baseStart_6422826 : Nat := 118140960795 + 6422826 * 2 ^ 59
def prefixEnd_6422826 : Nat := 4983230072969 + 3 ^ 40 * 6422826 * 2
def baseEnd_6422826 : Nat := 1099332299398197632478989

theorem tailTrace_6422826 : CollatzResearch.WordTrace tailWord_6422826 prefixEnd_6422826 1099332299398197632478989 := by
  unfold tailWord_6422826
  simp only [CollatzResearch.WordTrace]
  refine ⟨58564927357301452048686083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156173139619470538796496221 58564927357301452048686083)
  ·
    refine ⟨87847391035952178073029125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58564927357301452048686083 87847391035952178073029125)
    ·
      refine ⟨16471385819241033388692961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87847391035952178073029125 16471385819241033388692961)
      ·
        refine ⟨12353539364430775041519721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16471385819241033388692961 12353539364430775041519721)
        ·
          refine ⟨9265154523323081281139791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12353539364430775041519721 9265154523323081281139791)
          ·
            refine ⟨13897731784984621921709687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9265154523323081281139791 13897731784984621921709687)
            ·
              refine ⟨20846597677476932882564531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13897731784984621921709687 20846597677476932882564531)
              ·
                refine ⟨31269896516215399323846797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20846597677476932882564531 31269896516215399323846797)
                ·
                  refine ⟨11726211193580774746442549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31269896516215399323846797 11726211193580774746442549)
                  ·
                    refine ⟨1099332299398197632478989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11726211193580774746442549 1099332299398197632478989)
                    ·
                      rfl

theorem cell23_6422826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_6422826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422826 prefixEnd_6422826 := by exact prefixLift 6422826
  have htrace : WordTrace (prefixWord ++ tailWord_6422826) baseStart_6422826 baseEnd_6422826 := by
    simpa [prefixWord, tailWord_6422826, baseEnd_6422826] using wordTrace_append hprefix tailTrace_6422826
  have hstable : (prefixWord ++ tailWord_6422826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422826).length < 2 ^ (prefixWord ++ tailWord_6422826).sum := by decide
  have hdescent : baseEnd_6422826 < baseStart_6422826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422833 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 2, 3, 2]
def baseStart_6422833 : Nat := 118140960795 + 6422833 * 2 ^ 59
def prefixEnd_6422833 : Nat := 4983230072969 + 3 ^ 40 * 6422833 * 2
def baseEnd_6422833 : Nat := 3298000492559174370049435

theorem tailTrace_6422833 : CollatzResearch.WordTrace tailWord_6422833 prefixEnd_6422833 3298000492559174370049435 := by
  unfold tailWord_6422833
  simp only [CollatzResearch.WordTrace]
  refine ⟨234259964740180448390249153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156173309826786965593499435 234259964740180448390249153)
  ·
    refine ⟨175694973555135336292686865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234259964740180448390249153 175694973555135336292686865)
    ·
      refine ⟨131771230166351502219515149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175694973555135336292686865 131771230166351502219515149)
      ·
        refine ⟨49414211312381813332318181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131771230166351502219515149 49414211312381813332318181)
        ·
          refine ⟨9265164621071589999809659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49414211312381813332318181 9265164621071589999809659)
          ·
            refine ⟨13897746931607384999714489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9265164621071589999809659 13897746931607384999714489)
            ·
              refine ⟨10423310198705538749785867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13897746931607384999714489 10423310198705538749785867)
              ·
                refine ⟨15634965298058308124678801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10423310198705538749785867 15634965298058308124678801)
                ·
                  refine ⟨11726223973543731093509101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15634965298058308124678801 11726223973543731093509101)
                  ·
                    refine ⟨4397333990078899160065913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11726223973543731093509101 4397333990078899160065913)
                    ·
                      refine ⟨3298000492559174370049435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4397333990078899160065913 3298000492559174370049435)
                      ·
                        rfl

theorem cell23_6422833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 3, 2].length) (baseStart_6422833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422833 prefixEnd_6422833 := by exact prefixLift 6422833
  have htrace : WordTrace (prefixWord ++ tailWord_6422833) baseStart_6422833 baseEnd_6422833 := by
    simpa [prefixWord, tailWord_6422833, baseEnd_6422833] using wordTrace_append hprefix tailTrace_6422833
  have hstable : (prefixWord ++ tailWord_6422833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422833).length < 2 ^ (prefixWord ++ tailWord_6422833).sum := by decide
  have hdescent : baseEnd_6422833 < baseStart_6422833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422862 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_6422862 : Nat := 118140960795 + 6422862 * 2 ^ 59
def prefixEnd_6422862 : Nat := 4983230072969 + 3 ^ 40 * 6422862 * 2
def baseEnd_6422862 : Nat := 3298015383498154756586801

theorem tailTrace_6422862 : CollatzResearch.WordTrace tailWord_6422862 prefixEnd_6422862 3298015383498154756586801 := by
  unfold tailWord_6422862
  simp only [CollatzResearch.WordTrace]
  refine ⟨29282627807134423292881855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156174014971383590895369893 29282627807134423292881855)
  ·
    refine ⟨43923941710701634939322783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29282627807134423292881855 43923941710701634939322783)
    ·
      refine ⟨65885912566052452408984175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43923941710701634939322783 65885912566052452408984175)
      ·
        refine ⟨98828868849078678613476263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65885912566052452408984175 98828868849078678613476263)
        ·
          refine ⟨148243303273618017920214395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98828868849078678613476263 148243303273618017920214395)
          ·
            refine ⟨222364954910427026880321593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148243303273618017920214395 222364954910427026880321593)
            ·
              refine ⟨166773716182820270160241195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222364954910427026880321593 166773716182820270160241195)
              ·
                refine ⟨250160574274230405240361793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166773716182820270160241195 250160574274230405240361793)
                ·
                  refine ⟨187620430705672803930271345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 250160574274230405240361793 187620430705672803930271345)
                  ·
                    refine ⟨140715323029254602947703509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 187620430705672803930271345 140715323029254602947703509)
                    ·
                      refine ⟨3298015383498154756586801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 140715323029254602947703509 3298015383498154756586801)
                      ·
                        rfl

theorem cell23_6422862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_6422862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422862 prefixEnd_6422862 := by exact prefixLift 6422862
  have htrace : WordTrace (prefixWord ++ tailWord_6422862) baseStart_6422862 baseEnd_6422862 := by
    simpa [prefixWord, tailWord_6422862, baseEnd_6422862] using wordTrace_append hprefix tailTrace_6422862
  have hstable : (prefixWord ++ tailWord_6422862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422862).length < 2 ^ (prefixWord ++ tailWord_6422862).sum := by decide
  have hdescent : baseEnd_6422862 < baseStart_6422862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422879 : List Nat := [1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 3]
def baseStart_6422879 : Nat := 118140960795 + 6422879 * 2 ^ 59
def prefixEnd_6422879 : Nat := 4983230072969 + 3 ^ 40 * 6422879 * 2
def baseEnd_6422879 : Nat := 3298024112669281190074223

theorem tailTrace_6422879 : CollatzResearch.WordTrace tailWord_6422879 prefixEnd_6422879 3298024112669281190074223 := by
  unfold tailWord_6422879
  simp only [CollatzResearch.WordTrace]
  refine ⟨234261642498013798246423691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156174428332009198830949127 234261642498013798246423691)
  ·
    refine ⟨351392463747020697369635537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234261642498013798246423691 351392463747020697369635537)
    ·
      refine ⟨263544347810265523027226653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351392463747020697369635537 263544347810265523027226653)
      ·
        refine ⟨98829130428849571135209995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263544347810265523027226653 98829130428849571135209995)
        ·
          refine ⟨148243695643274356702814993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98829130428849571135209995 148243695643274356702814993)
          ·
            refine ⟨111182771732455767527111245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148243695643274356702814993 111182771732455767527111245)
            ·
              refine ⟨41693539399670912822666717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111182771732455767527111245 41693539399670912822666717)
              ·
                refine ⟨15635077274876592308500019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41693539399670912822666717 15635077274876592308500019)
                ·
                  refine ⟨23452615912314888462750029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15635077274876592308500019 23452615912314888462750029)
                  ·
                    refine ⟨8794730967118083173531261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23452615912314888462750029 8794730967118083173531261)
                    ·
                      refine ⟨3298024112669281190074223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8794730967118083173531261 3298024112669281190074223)
                      ·
                        rfl

theorem cell23_6422879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_6422879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422879 prefixEnd_6422879 := by exact prefixLift 6422879
  have htrace : WordTrace (prefixWord ++ tailWord_6422879) baseStart_6422879 baseEnd_6422879 := by
    simpa [prefixWord, tailWord_6422879, baseEnd_6422879] using wordTrace_append hprefix tailTrace_6422879
  have hstable : (prefixWord ++ tailWord_6422879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422879).length < 2 ^ (prefixWord ++ tailWord_6422879).sum := by decide
  have hdescent : baseEnd_6422879 < baseStart_6422879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422913 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 4, 1, 3]
def baseStart_6422913 : Nat := 118140960795 + 6422913 * 2 ^ 59
def prefixEnd_6422913 : Nat := 4983230072969 + 3 ^ 40 * 6422913 * 2
def baseEnd_6422913 : Nat := 3298041571011534057049067

theorem tailTrace_6422913 : CollatzResearch.WordTrace tailWord_6422913 prefixEnd_6422913 3298041571011534057049067 := by
  unfold tailWord_6422913
  simp only [CollatzResearch.WordTrace]
  refine ⟨234262882579890622053161393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156175255053260414702107595 234262882579890622053161393)
  ·
    refine ⟨175697161934917966539871045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234262882579890622053161393 175697161934917966539871045)
    ·
      refine ⟨32943217862797118726225821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175697161934917966539871045 32943217862797118726225821)
      ·
        refine ⟨12353706698548919522334683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32943217862797118726225821 12353706698548919522334683)
        ·
          refine ⟨18530560047823379283502025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12353706698548919522334683 18530560047823379283502025)
          ·
            refine ⟨13897920035867534462626519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18530560047823379283502025 13897920035867534462626519)
            ·
              refine ⟨20846880053801301693939779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13897920035867534462626519 20846880053801301693939779)
              ·
                refine ⟨31270320080701952540909669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20846880053801301693939779 31270320080701952540909669)
                ·
                  refine ⟨5863185015131616101420563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31270320080701952540909669 5863185015131616101420563)
                  ·
                    refine ⟨8794777522697424152130845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5863185015131616101420563 8794777522697424152130845)
                    ·
                      refine ⟨3298041571011534057049067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8794777522697424152130845 3298041571011534057049067)
                      ·
                        rfl

theorem cell23_6422913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_6422913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422913 prefixEnd_6422913 := by exact prefixLift 6422913
  have htrace : WordTrace (prefixWord ++ tailWord_6422913) baseStart_6422913 baseEnd_6422913 := by
    simpa [prefixWord, tailWord_6422913, baseEnd_6422913] using wordTrace_append hprefix tailTrace_6422913
  have hstable : (prefixWord ++ tailWord_6422913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422913).length < 2 ^ (prefixWord ++ tailWord_6422913).sum := by decide
  have hdescent : baseEnd_6422913 < baseStart_6422913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6422934 : List Nat := [5, 3, 1, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_6422934 : Nat := 118140960795 + 6422934 * 2 ^ 59
def prefixEnd_6422934 : Nat := 4983230072969 + 3 ^ 40 * 6422934 * 2
def baseEnd_6422934 : Nat := 3298052354105278474886471

theorem tailTrace_6422934 : CollatzResearch.WordTrace tailWord_6422934 prefixEnd_6422934 3298052354105278474886471 := by
  unfold tailWord_6422934
  simp only [CollatzResearch.WordTrace]
  refine ⟨14641478032050908914979741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 156175765675209695093117237 14641478032050908914979741)
  ·
    refine ⟨5490554262019090843117403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14641478032050908914979741 5490554262019090843117403)
    ·
      refine ⟨8235831393028636264676105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5490554262019090843117403 8235831393028636264676105)
      ·
        refine ⟨6176873544771477198507079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8235831393028636264676105 6176873544771477198507079)
        ·
          refine ⟨9265310317157215797760619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6176873544771477198507079 9265310317157215797760619)
          ·
            refine ⟨13897965475735823696640929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9265310317157215797760619 13897965475735823696640929)
            ·
              refine ⟨10423474106801867772480697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13897965475735823696640929 10423474106801867772480697)
              ·
                refine ⟨7817605580101400829360523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10423474106801867772480697 7817605580101400829360523)
                ·
                  refine ⟨11726408370152101244040785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7817605580101400829360523 11726408370152101244040785)
                  ·
                    refine ⟨8794806277614075933030589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11726408370152101244040785 8794806277614075933030589)
                    ·
                      refine ⟨3298052354105278474886471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8794806277614075933030589 3298052354105278474886471)
                      ·
                        rfl

theorem cell23_6422934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_6422934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6422934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6422934 prefixEnd_6422934 := by exact prefixLift 6422934
  have htrace : WordTrace (prefixWord ++ tailWord_6422934) baseStart_6422934 baseEnd_6422934 := by
    simpa [prefixWord, tailWord_6422934, baseEnd_6422934] using wordTrace_append hprefix tailTrace_6422934
  have hstable : (prefixWord ++ tailWord_6422934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6422934).length < 2 ^ (prefixWord ++ tailWord_6422934).sum := by decide
  have hdescent : baseEnd_6422934 < baseStart_6422934 := by decide
  rcases family_descends (prefixWord ++ tailWord_6422934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423036 : List Nat := [2, 2, 2, 1, 2, 1, 1, 5, 3, 4]
def baseStart_6423036 : Nat := 118140960795 + 6423036 * 2 ^ 59
def prefixEnd_6423036 : Nat := 4983230072969 + 3 ^ 40 * 6423036 * 2
def baseEnd_6423036 : Nat := 1099368243044012358603667

theorem tailTrace_6423036 : CollatzResearch.WordTrace tailWord_6423036 prefixEnd_6423036 1099368243044012358603667 := by
  unfold tailWord_6423036
  simp only [CollatzResearch.WordTrace]
  refine ⟨117133684379222507029944481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156178245838963342706592641 117133684379222507029944481)
  ·
    refine ⟨87850263284416880272458361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117133684379222507029944481 87850263284416880272458361)
    ·
      refine ⟨65887697463312660204343771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87850263284416880272458361 65887697463312660204343771)
      ·
        refine ⟨98831546194968990306515657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65887697463312660204343771 98831546194968990306515657)
        ·
          refine ⟨74123659646226742729886743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98831546194968990306515657 74123659646226742729886743)
          ·
            refine ⟨111185489469340114094830115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74123659646226742729886743 111185489469340114094830115)
            ·
              refine ⟨166778234204010171142245173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111185489469340114094830115 166778234204010171142245173)
              ·
                refine ⟨15635459456625953544585485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166778234204010171142245173 15635459456625953544585485)
                ·
                  refine ⟨5863297296234732579219557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15635459456625953544585485 5863297296234732579219557)
                  ·
                    refine ⟨1099368243044012358603667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5863297296234732579219557 1099368243044012358603667)
                    ·
                      rfl

theorem cell23_6423036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 5, 3, 4].length) (baseStart_6423036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423036 prefixEnd_6423036 := by exact prefixLift 6423036
  have htrace : WordTrace (prefixWord ++ tailWord_6423036) baseStart_6423036 baseEnd_6423036 := by
    simpa [prefixWord, tailWord_6423036, baseEnd_6423036] using wordTrace_append hprefix tailTrace_6423036
  have hstable : (prefixWord ++ tailWord_6423036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423036).length < 2 ^ (prefixWord ++ tailWord_6423036).sum := by decide
  have hdescent : baseEnd_6423036 < baseStart_6423036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423060 : List Nat := [2, 4, 3, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_6423060 : Nat := 118140960795 + 6423060 * 2 ^ 59
def prefixEnd_6423060 : Nat := 4983230072969 + 3 ^ 40 * 6423060 * 2
def baseEnd_6423060 : Nat := 3298117052667744981910891

theorem tailTrace_6423060 : CollatzResearch.WordTrace tailWord_6423060 prefixEnd_6423060 3298117052667744981910891 := by
  unfold tailWord_6423060
  simp only [CollatzResearch.WordTrace]
  refine ⟨117134122055179033079381317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156178829406905377439175089 117134122055179033079381317)
  ·
    refine ⟨21962647885346068702383997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117134122055179033079381317 21962647885346068702383997)
    ·
      refine ⟨8235992957004775763393999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21962647885346068702383997 8235992957004775763393999)
      ·
        refine ⟨12353989435507163645090999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8235992957004775763393999 12353989435507163645090999)
        ·
          refine ⟨18530984153260745467636499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12353989435507163645090999 18530984153260745467636499)
          ·
            refine ⟨27796476229891118201454749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18530984153260745467636499 27796476229891118201454749)
            ·
              refine ⟨10423678586209169325545531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27796476229891118201454749 10423678586209169325545531)
              ·
                refine ⟨15635517879313753988318297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10423678586209169325545531 15635517879313753988318297)
                ·
                  refine ⟨11726638409485315491238723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15635517879313753988318297 11726638409485315491238723)
                  ·
                    refine ⟨17589957614227973236858085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11726638409485315491238723 17589957614227973236858085)
                    ·
                      refine ⟨3298117052667744981910891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17589957614227973236858085 3298117052667744981910891)
                      ·
                        rfl

theorem cell23_6423060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_6423060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423060 prefixEnd_6423060 := by exact prefixLift 6423060
  have htrace : WordTrace (prefixWord ++ tailWord_6423060) baseStart_6423060 baseEnd_6423060 := by
    simpa [prefixWord, tailWord_6423060, baseEnd_6423060] using wordTrace_append hprefix tailTrace_6423060
  have hstable : (prefixWord ++ tailWord_6423060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423060).length < 2 ^ (prefixWord ++ tailWord_6423060).sum := by decide
  have hdescent : baseEnd_6423060 < baseStart_6423060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423136 : List Nat := [2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 5]
def baseStart_6423136 : Nat := 118140960795 + 6423136 * 2 ^ 59
def prefixEnd_6423136 : Nat := 4983230072969 + 3 ^ 40 * 6423136 * 2
def baseEnd_6423136 : Nat := 3298156077197486684560541

theorem tailTrace_6423136 : CollatzResearch.WordTrace tailWord_6423136 prefixEnd_6423136 3298156077197486684560541 := by
  unfold tailWord_6423136
  simp only [CollatzResearch.WordTrace]
  refine ⟨117135508029041365569264631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156180677372055154092352841 117135508029041365569264631)
  ·
    refine ⟨175703262043562048353896947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117135508029041365569264631 175703262043562048353896947)
    ·
      refine ⟨263554893065343072530845421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175703262043562048353896947 263554893065343072530845421)
      ·
        refine ⟨98833084899503652199067033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263554893065343072530845421 98833084899503652199067033)
        ·
          refine ⟨74124813674627739149300275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98833084899503652199067033 74124813674627739149300275)
          ·
            refine ⟨111187220511941608723950413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74124813674627739149300275 111187220511941608723950413)
            ·
              refine ⟨41695207691978103271481405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111187220511941608723950413 41695207691978103271481405)
              ·
                refine ⟨15635702884491788726805527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41695207691978103271481405 15635702884491788726805527)
                ·
                  refine ⟨23453554326737683090208291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15635702884491788726805527 23453554326737683090208291)
                  ·
                    refine ⟨35180331490106524635312437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23453554326737683090208291 35180331490106524635312437)
                    ·
                      refine ⟨3298156077197486684560541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35180331490106524635312437 3298156077197486684560541)
                      ·
                        rfl

theorem cell23_6423136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_6423136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423136 prefixEnd_6423136 := by exact prefixLift 6423136
  have htrace : WordTrace (prefixWord ++ tailWord_6423136) baseStart_6423136 baseEnd_6423136 := by
    simpa [prefixWord, tailWord_6423136, baseEnd_6423136] using wordTrace_append hprefix tailTrace_6423136
  have hstable : (prefixWord ++ tailWord_6423136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423136).length < 2 ^ (prefixWord ++ tailWord_6423136).sum := by decide
  have hdescent : baseEnd_6423136 < baseStart_6423136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423143 : List Nat := [1, 1, 5, 1, 1, 1, 1, 6, 2, 4]
def baseStart_6423143 : Nat := 118140960795 + 6423143 * 2 ^ 59
def prefixEnd_6423143 : Nat := 4983230072969 + 3 ^ 40 * 6423143 * 2
def baseEnd_6423143 : Nat := 1099386557187356052391003

theorem tailTrace_6423143 : CollatzResearch.WordTrace tailWord_6423143 prefixEnd_6423143 1099386557187356052391003 := by
  unfold tailWord_6423143
  simp only [CollatzResearch.WordTrace]
  refine ⟨234271271369057371334034083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156180847579371580889356055 234271271369057371334034083)
  ·
    refine ⟨351406907053586057001051125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234271271369057371334034083 351406907053586057001051125)
    ·
      refine ⟨32944397536273692843848543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 351406907053586057001051125 32944397536273692843848543)
      ·
        refine ⟨49416596304410539265772815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32944397536273692843848543 49416596304410539265772815)
        ·
          refine ⟨74124894456615808898659223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49416596304410539265772815 74124894456615808898659223)
          ·
            refine ⟨111187341684923713347988835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74124894456615808898659223 111187341684923713347988835)
            ·
              refine ⟨166781012527385570021983253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111187341684923713347988835 166781012527385570021983253)
              ·
                refine ⟨7817859962221198594780465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 166781012527385570021983253 7817859962221198594780465)
                ·
                  refine ⟨5863394971665898946085349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7817859962221198594780465 5863394971665898946085349)
                  ·
                    refine ⟨1099386557187356052391003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5863394971665898946085349 1099386557187356052391003)
                    ·
                      rfl

theorem cell23_6423143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_6423143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423143 prefixEnd_6423143 := by exact prefixLift 6423143
  have htrace : WordTrace (prefixWord ++ tailWord_6423143) baseStart_6423143 baseEnd_6423143 := by
    simpa [prefixWord, tailWord_6423143, baseEnd_6423143] using wordTrace_append hprefix tailTrace_6423143
  have hstable : (prefixWord ++ tailWord_6423143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423143).length < 2 ^ (prefixWord ++ tailWord_6423143).sum := by decide
  have hdescent : baseEnd_6423143 < baseStart_6423143 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423144 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 3, 1, 3]
def baseStart_6423144 : Nat := 118140960795 + 6423144 * 2 ^ 59
def prefixEnd_6423144 : Nat := 4983230072969 + 3 ^ 40 * 6423144 * 2
def baseEnd_6423144 : Nat := 3298160185042722653260505

theorem tailTrace_6423144 : CollatzResearch.WordTrace tailWord_6423144 prefixEnd_6423144 3298160185042722653260505 := by
  unfold tailWord_6423144
  simp only [CollatzResearch.WordTrace]
  refine ⟨117135653921026874252410243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156180871894702499003213657 117135653921026874252410243)
  ·
    refine ⟨175703480881540311378615365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117135653921026874252410243 175703480881540311378615365)
    ·
      refine ⟨32944402665288808383490381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175703480881540311378615365 32944402665288808383490381)
      ·
        refine ⟨12354150999483303143808893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32944402665288808383490381 12354150999483303143808893)
        ·
          refine ⟨4632806624806238678928335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12354150999483303143808893 4632806624806238678928335)
          ·
            refine ⟨6949209937209358018392503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4632806624806238678928335 6949209937209358018392503)
            ·
              refine ⟨10423814905814037027588755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6949209937209358018392503 10423814905814037027588755)
              ·
                refine ⟨15635722358721055541383133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10423814905814037027588755 15635722358721055541383133)
                ·
                  refine ⟨5863395884520395828018675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15635722358721055541383133 5863395884520395828018675)
                  ·
                    refine ⟨8795093826780593742028013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5863395884520395828018675 8795093826780593742028013)
                    ·
                      refine ⟨3298160185042722653260505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8795093826780593742028013 3298160185042722653260505)
                      ·
                        rfl

theorem cell23_6423144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_6423144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423144 prefixEnd_6423144 := by exact prefixLift 6423144
  have htrace : WordTrace (prefixWord ++ tailWord_6423144) baseStart_6423144 baseEnd_6423144 := by
    simpa [prefixWord, tailWord_6423144, baseEnd_6423144] using wordTrace_append hprefix tailTrace_6423144
  have hstable : (prefixWord ++ tailWord_6423144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423144).length < 2 ^ (prefixWord ++ tailWord_6423144).sum := by decide
  have hdescent : baseEnd_6423144 < baseStart_6423144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423146 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_6423146 : Nat := 118140960795 + 6423146 * 2 ^ 59
def prefixEnd_6423146 : Nat := 4983230072969 + 3 ^ 40 * 6423146 * 2
def baseEnd_6423146 : Nat := 3298161212004031645435495

theorem tailTrace_6423146 : CollatzResearch.WordTrace tailWord_6423146 prefixEnd_6423146 3298161212004031645435495 := by
  unfold tailWord_6423146
  simp only [CollatzResearch.WordTrace]
  refine ⟨58567845197011625711598323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156180920525364335230928861 58567845197011625711598323)
  ·
    refine ⟨87851767795517438567397485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58567845197011625711598323 87851767795517438567397485)
    ·
      refine ⟨32944412923319039462774057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87851767795517438567397485 32944412923319039462774057)
      ·
        refine ⟨24708309692489279597080543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32944412923319039462774057 24708309692489279597080543)
        ·
          refine ⟨37062464538733919395620815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24708309692489279597080543 37062464538733919395620815)
          ·
            refine ⟨55593696808100879093431223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37062464538733919395620815 55593696808100879093431223)
            ·
              refine ⟨83390545212151318640146835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55593696808100879093431223 83390545212151318640146835)
              ·
                refine ⟨125085817818226977960220253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83390545212151318640146835 125085817818226977960220253)
                ·
                  refine ⟨46907181681835116735082595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 125085817818226977960220253 46907181681835116735082595)
                  ·
                    refine ⟨70360772522752675102623893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46907181681835116735082595 70360772522752675102623893)
                    ·
                      refine ⟨3298161212004031645435495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 70360772522752675102623893 3298161212004031645435495)
                      ·
                        rfl

theorem cell23_6423146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_6423146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423146 prefixEnd_6423146 := by exact prefixLift 6423146
  have htrace : WordTrace (prefixWord ++ tailWord_6423146) baseStart_6423146 baseEnd_6423146 := by
    simpa [prefixWord, tailWord_6423146, baseEnd_6423146] using wordTrace_append hprefix tailTrace_6423146
  have hstable : (prefixWord ++ tailWord_6423146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423146).length < 2 ^ (prefixWord ++ tailWord_6423146).sum := by decide
  have hdescent : baseEnd_6423146 < baseStart_6423146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423207 : List Nat := [1, 1, 6, 3, 2, 1, 1, 8]
def baseStart_6423207 : Nat := 118140960795 + 6423207 * 2 ^ 59
def prefixEnd_6423207 : Nat := 4983230072969 + 3 ^ 40 * 6423207 * 2
def baseEnd_6423207 : Nat := 122155279049035403954545

theorem tailTrace_6423207 : CollatzResearch.WordTrace tailWord_6423207 prefixEnd_6423207 122155279049035403954545 := by
  unfold tailWord_6423207
  simp only [CollatzResearch.WordTrace]
  refine ⟨234273605640825510264363875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156182403760550340176242583 234273605640825510264363875)
  ·
    refine ⟨351410408461238265396545813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234273605640825510264363875 351410408461238265396545813)
    ·
      refine ⟨16472362896620543690463085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 351410408461238265396545813 16472362896620543690463085)
      ·
        refine ⟨6177136086232703883923657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16472362896620543690463085 6177136086232703883923657)
        ·
          refine ⟨4632852064674527912942743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6177136086232703883923657 4632852064674527912942743)
          ·
            refine ⟨6949278097011791869414115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4632852064674527912942743 6949278097011791869414115)
            ·
              refine ⟨10423917145517687804121173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6949278097011791869414115 10423917145517687804121173)
              ·
                refine ⟨122155279049035403954545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10423917145517687804121173 122155279049035403954545)
                ·
                  rfl

theorem cell23_6423207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 8].length) (baseStart_6423207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423207 prefixEnd_6423207 := by exact prefixLift 6423207
  have htrace : WordTrace (prefixWord ++ tailWord_6423207) baseStart_6423207 baseEnd_6423207 := by
    simpa [prefixWord, tailWord_6423207, baseEnd_6423207] using wordTrace_append hprefix tailTrace_6423207
  have hstable : (prefixWord ++ tailWord_6423207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423207).length < 2 ^ (prefixWord ++ tailWord_6423207).sum := by decide
  have hdescent : baseEnd_6423207 < baseStart_6423207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423217 : List Nat := [1, 2, 2, 6, 1, 1, 2, 1, 1, 3, 3]
def baseStart_6423217 : Nat := 118140960795 + 6423217 * 2 ^ 59
def prefixEnd_6423217 : Nat := 4983230072969 + 3 ^ 40 * 6423217 * 2
def baseEnd_6423217 : Nat := 3298197669130500867647669

theorem tailTrace_6423217 : CollatzResearch.WordTrace tailWord_6423217 prefixEnd_6423217 3298197669130500867647669 := by
  unfold tailWord_6423217
  simp only [CollatzResearch.WordTrace]
  refine ⟨234273970370789281972227905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156182646913859521314818603 234273970370789281972227905)
  ·
    refine ⟨175705477778091961479170929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234273970370789281972227905 175705477778091961479170929)
    ·
      refine ⟨131779108333568971109378197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175705477778091961479170929 131779108333568971109378197)
      ·
        refine ⟨6177145703136045520752103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 131779108333568971109378197 6177145703136045520752103)
        ·
          refine ⟨9265718554704068281128155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6177145703136045520752103 9265718554704068281128155)
          ·
            refine ⟨13898577832056102421692233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9265718554704068281128155 13898577832056102421692233)
            ·
              refine ⟨10423933374042076816269175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13898577832056102421692233 10423933374042076816269175)
              ·
                refine ⟨15635900061063115224403763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10423933374042076816269175 15635900061063115224403763)
                ·
                  refine ⟨23453850091594672836605645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15635900061063115224403763 23453850091594672836605645)
                  ·
                    refine ⟨8795193784348002313727117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23453850091594672836605645 8795193784348002313727117)
                    ·
                      refine ⟨3298197669130500867647669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8795193784348002313727117 3298197669130500867647669)
                      ·
                        rfl

theorem cell23_6423217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_6423217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423217 prefixEnd_6423217 := by exact prefixLift 6423217
  have htrace : WordTrace (prefixWord ++ tailWord_6423217) baseStart_6423217 baseEnd_6423217 := by
    simpa [prefixWord, tailWord_6423217, baseEnd_6423217] using wordTrace_append hprefix tailTrace_6423217
  have hstable : (prefixWord ++ tailWord_6423217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423217).length < 2 ^ (prefixWord ++ tailWord_6423217).sum := by decide
  have hdescent : baseEnd_6423217 < baseStart_6423217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423238 : List Nat := [6, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_6423238 : Nat := 118140960795 + 6423238 * 2 ^ 59
def prefixEnd_6423238 : Nat := 4983230072969 + 3 ^ 40 * 6423238 * 2
def baseEnd_6423238 : Nat := 3298208452224245285485073

theorem tailTrace_6423238 : CollatzResearch.WordTrace tailWord_6423238 prefixEnd_6423238 3298208452224245285485073 := by
  unfold tailWord_6423238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7321085509491037579960699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 156183157535808801705828245 7321085509491037579960699)
  ·
    refine ⟨10981628264236556369941049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7321085509491037579960699 10981628264236556369941049)
    ·
      refine ⟨8236221198177417277455787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10981628264236556369941049 8236221198177417277455787)
      ·
        refine ⟨12354331797266125916183681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8236221198177417277455787 12354331797266125916183681)
        ·
          refine ⟨9265748847949594437137761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12354331797266125916183681 9265748847949594437137761)
          ·
            refine ⟨6949311635962195827853321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9265748847949594437137761 6949311635962195827853321)
            ·
              refine ⟨5211983726971646870889991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6949311635962195827853321 5211983726971646870889991)
              ·
                refine ⟨7817975590457470306334987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5211983726971646870889991 7817975590457470306334987)
                ·
                  refine ⟨11726963385686205459502481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7817975590457470306334987 11726963385686205459502481)
                  ·
                    refine ⟨8795222539264654094626861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11726963385686205459502481 8795222539264654094626861)
                    ·
                      refine ⟨3298208452224245285485073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8795222539264654094626861 3298208452224245285485073)
                      ·
                        rfl

theorem cell23_6423238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_6423238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423238 prefixEnd_6423238 := by exact prefixLift 6423238
  have htrace : WordTrace (prefixWord ++ tailWord_6423238) baseStart_6423238 baseEnd_6423238 := by
    simpa [prefixWord, tailWord_6423238, baseEnd_6423238] using wordTrace_append hprefix tailTrace_6423238
  have hstable : (prefixWord ++ tailWord_6423238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423238).length < 2 ^ (prefixWord ++ tailWord_6423238).sum := by decide
  have hdescent : baseEnd_6423238 < baseStart_6423238 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423240 : List Nat := [2, 1, 3, 1, 2, 3, 2, 2, 1, 4, 2]
def baseStart_6423240 : Nat := 118140960795 + 6423240 * 2 ^ 59
def prefixEnd_6423240 : Nat := 4983230072969 + 3 ^ 40 * 6423240 * 2
def baseEnd_6423240 : Nat := 3298209479185554277660063

theorem tailTrace_6423240 : CollatzResearch.WordTrace tailWord_6423240 prefixEnd_6423240 3298209479185554277660063 := by
  unfold tailWord_6423240
  simp only [CollatzResearch.WordTrace]
  refine ⟨117137404624852978450157587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156183206166470637933543449 117137404624852978450157587)
  ·
    refine ⟨175706106937279467675236381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117137404624852978450157587 175706106937279467675236381)
    ·
      refine ⟨65889790101479800378213643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175706106937279467675236381 65889790101479800378213643)
      ·
        refine ⟨98834685152219700567320465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65889790101479800378213643 98834685152219700567320465)
        ·
          refine ⟨74126013864164775425490349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98834685152219700567320465 74126013864164775425490349)
          ·
            refine ⟨27797255199061790784558881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74126013864164775425490349 27797255199061790784558881)
            ·
              refine ⟨20847941399296343088419161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27797255199061790784558881 20847941399296343088419161)
              ·
                refine ⟨15635956049472257316314371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20847941399296343088419161 15635956049472257316314371)
                ·
                  refine ⟨23453934074208385974471557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15635956049472257316314371 23453934074208385974471557)
                  ·
                    refine ⟨4397612638914072370213417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23453934074208385974471557 4397612638914072370213417)
                    ·
                      refine ⟨3298209479185554277660063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4397612638914072370213417 3298209479185554277660063)
                      ·
                        rfl

theorem cell23_6423240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_6423240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423240 prefixEnd_6423240 := by exact prefixLift 6423240
  have htrace : WordTrace (prefixWord ++ tailWord_6423240) baseStart_6423240 baseEnd_6423240 := by
    simpa [prefixWord, tailWord_6423240, baseEnd_6423240] using wordTrace_append hprefix tailTrace_6423240
  have hstable : (prefixWord ++ tailWord_6423240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423240).length < 2 ^ (prefixWord ++ tailWord_6423240).sum := by decide
  have hdescent : baseEnd_6423240 < baseStart_6423240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423244 : List Nat := [2, 2, 1, 5, 1, 1, 4, 1, 1, 3, 2]
def baseStart_6423244 : Nat := 118140960795 + 6423244 * 2 ^ 59
def prefixEnd_6423244 : Nat := 4983230072969 + 3 ^ 40 * 6423244 * 2
def baseEnd_6423244 : Nat := 3298211533108172262010045

theorem tailTrace_6423244 : CollatzResearch.WordTrace tailWord_6423244 prefixEnd_6423244 3298211533108172262010045 := by
  unfold tailWord_6423244
  simp only [CollatzResearch.WordTrace]
  refine ⟨117137477570845732791730393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156183303427794310388973857 117137477570845732791730393)
  ·
    refine ⟨87853108178134299593797795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117137477570845732791730393 87853108178134299593797795)
    ·
      refine ⟨131779662267201449390696693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87853108178134299593797795 131779662267201449390696693)
      ·
        refine ⟨12354343337550135880377815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131779662267201449390696693 12354343337550135880377815)
        ·
          refine ⟨18531515006325203820566723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12354343337550135880377815 18531515006325203820566723)
          ·
            refine ⟨27797272509487805730850085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18531515006325203820566723 27797272509487805730850085)
            ·
              refine ⟨5211988595528963574534391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27797272509487805730850085 5211988595528963574534391)
              ·
                refine ⟨7817982893293445361801587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5211988595528963574534391 7817982893293445361801587)
                ·
                  refine ⟨11726974339940168042702381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7817982893293445361801587 11726974339940168042702381)
                  ·
                    refine ⟨4397615377477563016013393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11726974339940168042702381 4397615377477563016013393)
                    ·
                      refine ⟨3298211533108172262010045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4397615377477563016013393 3298211533108172262010045)
                      ·
                        rfl

theorem cell23_6423244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_6423244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423244 prefixEnd_6423244 := by exact prefixLift 6423244
  have htrace : WordTrace (prefixWord ++ tailWord_6423244) baseStart_6423244 baseEnd_6423244 := by
    simpa [prefixWord, tailWord_6423244, baseEnd_6423244] using wordTrace_append hprefix tailTrace_6423244
  have hstable : (prefixWord ++ tailWord_6423244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423244).length < 2 ^ (prefixWord ++ tailWord_6423244).sum := by decide
  have hdescent : baseEnd_6423244 < baseStart_6423244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423263 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 7]
def baseStart_6423263 : Nat := 118140960795 + 6423263 * 2 ^ 59
def prefixEnd_6423263 : Nat := 4983230072969 + 3 ^ 40 * 6423263 * 2
def baseEnd_6423263 : Nat := 366469032137845298630273

theorem tailTrace_6423263 : CollatzResearch.WordTrace tailWord_6423263 prefixEnd_6423263 366469032137845298630273 := by
  unfold tailWord_6423263
  simp only [CollatzResearch.WordTrace]
  refine ⟨234275648128622631828402443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156183765419081754552268295 234275648128622631828402443)
  ·
    refine ⟨351413472192933947742603665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234275648128622631828402443 351413472192933947742603665)
    ·
      refine ⟨263560104144700460806952749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351413472192933947742603665 263560104144700460806952749)
      ·
        refine ⟨98835039054262672802607281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263560104144700460806952749 98835039054262672802607281)
        ·
          refine ⟨74126279290697004601955461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98835039054262672802607281 74126279290697004601955461)
          ·
            refine ⟨13898677367005688362866649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74126279290697004601955461 13898677367005688362866649)
            ·
              refine ⟨10424008025254266272149987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13898677367005688362866649 10424008025254266272149987)
              ·
                refine ⟨15636012037881399408224981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10424008025254266272149987 15636012037881399408224981)
                ·
                  refine ⟨366469032137845298630273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15636012037881399408224981 366469032137845298630273)
                  ·
                    rfl

theorem cell23_6423263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 7].length) (baseStart_6423263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423263 prefixEnd_6423263 := by exact prefixLift 6423263
  have htrace : WordTrace (prefixWord ++ tailWord_6423263) baseStart_6423263 baseEnd_6423263 := by
    simpa [prefixWord, tailWord_6423263, baseEnd_6423263] using wordTrace_append hprefix tailTrace_6423263
  have hstable : (prefixWord ++ tailWord_6423263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423263).length < 2 ^ (prefixWord ++ tailWord_6423263).sum := by decide
  have hdescent : baseEnd_6423263 < baseStart_6423263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423273 : List Nat := [1, 2, 1, 1, 1, 2, 6, 1, 2, 3, 3]
def baseStart_6423273 : Nat := 118140960795 + 6423273 * 2 ^ 59
def prefixEnd_6423273 : Nat := 4983230072969 + 3 ^ 40 * 6423273 * 2
def baseEnd_6423273 : Nat := 3298226424047152648547411

theorem tailTrace_6423273 : CollatzResearch.WordTrace tailWord_6423273 prefixEnd_6423273 3298226424047152648547411 := by
  unfold tailWord_6423273
  simp only [CollatzResearch.WordTrace]
  refine ⟨234276012858586403536266473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156184008572390935690844315 234276012858586403536266473)
  ·
    refine ⟨175707009643939802652199855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234276012858586403536266473 175707009643939802652199855)
    ·
      refine ⟨263560514465909703978299783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175707009643939802652199855 263560514465909703978299783)
      ·
        refine ⟨395340771698864555967449675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263560514465909703978299783 395340771698864555967449675)
        ·
          refine ⟨593011157548296833951174513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395340771698864555967449675 593011157548296833951174513)
          ·
            refine ⟨444758368161222625463380885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593011157548296833951174513 444758368161222625463380885)
            ·
              refine ⟨20848048507557310568595979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 444758368161222625463380885 20848048507557310568595979)
              ·
                refine ⟨31272072761335965852893969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20848048507557310568595979 31272072761335965852893969)
                ·
                  refine ⟨23454054571001974389670477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31272072761335965852893969 23454054571001974389670477)
                  ·
                    refine ⟨8795270464125740396126429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23454054571001974389670477 8795270464125740396126429)
                    ·
                      refine ⟨3298226424047152648547411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8795270464125740396126429 3298226424047152648547411)
                      ·
                        rfl

theorem cell23_6423273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 1, 2, 3, 3].length) (baseStart_6423273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423273 prefixEnd_6423273 := by exact prefixLift 6423273
  have htrace : WordTrace (prefixWord ++ tailWord_6423273) baseStart_6423273 baseEnd_6423273 := by
    simpa [prefixWord, tailWord_6423273, baseEnd_6423273] using wordTrace_append hprefix tailTrace_6423273
  have hstable : (prefixWord ++ tailWord_6423273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423273).length < 2 ^ (prefixWord ++ tailWord_6423273).sum := by decide
  have hdescent : baseEnd_6423273 < baseStart_6423273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423293 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 2, 5]
def baseStart_6423293 : Nat := 118140960795 + 6423293 * 2 ^ 59
def prefixEnd_6423293 : Nat := 4983230072969 + 3 ^ 40 * 6423293 * 2
def baseEnd_6423293 : Nat := 1099412231220080856765773

theorem tailTrace_6423293 : CollatzResearch.WordTrace tailWord_6423293 prefixEnd_6423293 1099412231220080856765773 := by
  unfold tailWord_6423293
  simp only [CollatzResearch.WordTrace]
  refine ⟨234276742318513946951994533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156184494879009297967996355 234276742318513946951994533)
  ·
    refine ⟨43926889184721365053498975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234276742318513946951994533 43926889184721365053498975)
    ·
      refine ⟨65890333777082047580248463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43926889184721365053498975 65890333777082047580248463)
      ·
        refine ⟨98835500665623071370372695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65890333777082047580248463 98835500665623071370372695)
        ·
          refine ⟨148253250998434607055559043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98835500665623071370372695 148253250998434607055559043)
          ·
            refine ⟨222379876497651910583338565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148253250998434607055559043 222379876497651910583338565)
            ·
              refine ⟨41696226843309733234375981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 222379876497651910583338565 41696226843309733234375981)
              ·
                refine ⟨15636085066241149962890993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41696226843309733234375981 15636085066241149962890993)
                ·
                  refine ⟨11727063799680862472168245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15636085066241149962890993 11727063799680862472168245)
                  ·
                    refine ⟨1099412231220080856765773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11727063799680862472168245 1099412231220080856765773)
                    ·
                      rfl

theorem cell23_6423293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 5].length) (baseStart_6423293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423293 prefixEnd_6423293 := by exact prefixLift 6423293
  have htrace : WordTrace (prefixWord ++ tailWord_6423293) baseStart_6423293 baseEnd_6423293 := by
    simpa [prefixWord, tailWord_6423293, baseEnd_6423293] using wordTrace_append hprefix tailTrace_6423293
  have hstable : (prefixWord ++ tailWord_6423293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423293).length < 2 ^ (prefixWord ++ tailWord_6423293).sum := by decide
  have hdescent : baseEnd_6423293 < baseStart_6423293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423313 : List Nat := [1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 4]
def baseStart_6423313 : Nat := 118140960795 + 6423313 * 2 ^ 59
def prefixEnd_6423313 : Nat := 4983230072969 + 3 ^ 40 * 6423313 * 2
def baseEnd_6423313 : Nat := 3298246963273332492047227

theorem tailTrace_6423313 : CollatzResearch.WordTrace tailWord_6423313 prefixEnd_6423313 3298246963273332492047227 := by
  unfold tailWord_6423313
  simp only [CollatzResearch.WordTrace]
  refine ⟨234277471778441490367722593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156184981185627660245148395 234277471778441490367722593)
  ·
    refine ⟨175708103833831117775791945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234277471778441490367722593 175708103833831117775791945)
    ·
      refine ⟨131781077875373338331843959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175708103833831117775791945 131781077875373338331843959)
      ·
        refine ⟨197671616813060007497765939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131781077875373338331843959 197671616813060007497765939)
        ·
          refine ⟨296507425219590011246648909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197671616813060007497765939 296507425219590011246648909)
          ·
            refine ⟨111190284457346254217493341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296507425219590011246648909 111190284457346254217493341)
            ·
              refine ⟨41696356671504845331560003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111190284457346254217493341 41696356671504845331560003)
              ·
                refine ⟨62544535007257267997340005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41696356671504845331560003 62544535007257267997340005)
                ·
                  refine ⟨11727100313860737749501251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62544535007257267997340005 11727100313860737749501251)
                  ·
                    refine ⟨17590650470791106624251877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11727100313860737749501251 17590650470791106624251877)
                    ·
                      refine ⟨3298246963273332492047227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17590650470791106624251877 3298246963273332492047227)
                      ·
                        rfl

theorem cell23_6423313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_6423313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423313 prefixEnd_6423313 := by exact prefixLift 6423313
  have htrace : WordTrace (prefixWord ++ tailWord_6423313) baseStart_6423313 baseEnd_6423313 := by
    simpa [prefixWord, tailWord_6423313, baseEnd_6423313] using wordTrace_append hprefix tailTrace_6423313
  have hstable : (prefixWord ++ tailWord_6423313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423313).length < 2 ^ (prefixWord ++ tailWord_6423313).sum := by decide
  have hdescent : baseEnd_6423313 < baseStart_6423313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423314 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 7]
def baseStart_6423314 : Nat := 118140960795 + 6423314 * 2 ^ 59
def prefixEnd_6423314 : Nat := 4983230072969 + 3 ^ 40 * 6423314 * 2
def baseEnd_6423314 : Nat := 366471941861554109792747

theorem tailTrace_6423314 : CollatzResearch.WordTrace tailWord_6423314 prefixEnd_6423314 366471941861554109792747 := by
  unfold tailWord_6423314
  simp only [CollatzResearch.WordTrace]
  refine ⟨58569377062859466884627249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156185005500958578359005997 58569377062859466884627249)
  ·
    refine ⟨43927032797144600163470437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58569377062859466884627249 43927032797144600163470437)
    ·
      refine ⟨8236318649464612530650707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43927032797144600163470437 8236318649464612530650707)
      ·
        refine ⟨12354477974196918795976061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8236318649464612530650707 12354477974196918795976061)
        ·
          refine ⟨4632929240323844548491023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12354477974196918795976061 4632929240323844548491023)
          ·
            refine ⟨6949393860485766822736535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4632929240323844548491023 6949393860485766822736535)
            ·
              refine ⟨10424090790728650234104803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6949393860485766822736535 10424090790728650234104803)
              ·
                refine ⟨15636136186092975351157205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10424090790728650234104803 15636136186092975351157205)
                ·
                  refine ⟨366471941861554109792747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15636136186092975351157205 366471941861554109792747)
                  ·
                    rfl

theorem cell23_6423314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 7].length) (baseStart_6423314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423314 prefixEnd_6423314 := by exact prefixLift 6423314
  have htrace : WordTrace (prefixWord ++ tailWord_6423314) baseStart_6423314 baseEnd_6423314 := by
    simpa [prefixWord, tailWord_6423314, baseEnd_6423314] using wordTrace_append hprefix tailTrace_6423314
  have hstable : (prefixWord ++ tailWord_6423314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423314).length < 2 ^ (prefixWord ++ tailWord_6423314).sum := by decide
  have hdescent : baseEnd_6423314 < baseStart_6423314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423325 : List Nat := [1, 4, 2, 4, 2, 1, 2, 1, 2, 2, 2]
def baseStart_6423325 : Nat := 118140960795 + 6423325 * 2 ^ 59
def prefixEnd_6423325 : Nat := 4983230072969 + 3 ^ 40 * 6423325 * 2
def baseEnd_6423325 : Nat := 3298253125041186445097173

theorem tailTrace_6423325 : CollatzResearch.WordTrace tailWord_6423325 prefixEnd_6423325 3298253125041186445097173 := by
  unfold tailWord_6423325
  simp only [CollatzResearch.WordTrace]
  refine ⟨234277909454398016417159429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156185272969598677611439619 234277909454398016417159429)
  ·
    refine ⟨43927108022699628078217393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234277909454398016417159429 43927108022699628078217393)
    ·
      refine ⟨32945331017024721058663045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43927108022699628078217393 32945331017024721058663045)
      ·
        refine ⟨6177249565692135198499321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32945331017024721058663045 6177249565692135198499321)
        ·
          refine ⟨4632937174269101398874491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6177249565692135198499321 4632937174269101398874491)
          ·
            refine ⟨6949405761403652098311737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4632937174269101398874491 6949405761403652098311737)
            ·
              refine ⟨5212054321052739073733803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6949405761403652098311737 5212054321052739073733803)
              ·
                refine ⟨7818081481579108610600705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5212054321052739073733803 7818081481579108610600705)
                ·
                  refine ⟨5863561111184331457950529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7818081481579108610600705 5863561111184331457950529)
                  ·
                    refine ⟨4397670833388248593462897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5863561111184331457950529 4397670833388248593462897)
                    ·
                      refine ⟨3298253125041186445097173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4397670833388248593462897 3298253125041186445097173)
                      ·
                        rfl

theorem cell23_6423325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_6423325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423325 prefixEnd_6423325 := by exact prefixLift 6423325
  have htrace : WordTrace (prefixWord ++ tailWord_6423325) baseStart_6423325 baseEnd_6423325 := by
    simpa [prefixWord, tailWord_6423325, baseEnd_6423325] using wordTrace_append hprefix tailTrace_6423325
  have hstable : (prefixWord ++ tailWord_6423325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423325).length < 2 ^ (prefixWord ++ tailWord_6423325).sum := by decide
  have hdescent : baseEnd_6423325 < baseStart_6423325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423400 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 3, 5]
def baseStart_6423400 : Nat := 118140960795 + 6423400 * 2 ^ 59
def prefixEnd_6423400 : Nat := 4983230072969 + 3 ^ 40 * 6423400 * 2
def baseEnd_6423400 : Nat := 1099430545363424550553109

theorem tailTrace_6423400 : CollatzResearch.WordTrace tailWord_6423400 prefixEnd_6423400 1099430545363424550553109 := by
  unfold tailWord_6423400
  simp only [CollatzResearch.WordTrace]
  refine ⟨117140322464563152113069827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156187096619417536150759769 117140322464563152113069827)
  ·
    refine ⟨175710483696844728169604741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117140322464563152113069827 175710483696844728169604741)
    ·
      refine ⟨32945715693158386531800889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175710483696844728169604741 32945715693158386531800889)
      ·
        refine ⟨24709286769868789898850667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32945715693158386531800889 24709286769868789898850667)
        ·
          refine ⟨37063930154803184848276001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24709286769868789898850667 37063930154803184848276001)
          ·
            refine ⟨27797947616102388636207001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37063930154803184848276001 27797947616102388636207001)
            ·
              refine ⟨20848460712076791477155251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27797947616102388636207001 20848460712076791477155251)
              ·
                refine ⟨31272691068115187215732877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20848460712076791477155251 31272691068115187215732877)
                ·
                  refine ⟨11727259150543195205899829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31272691068115187215732877 11727259150543195205899829)
                  ·
                    refine ⟨1099430545363424550553109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11727259150543195205899829 1099430545363424550553109)
                    ·
                      rfl

theorem cell23_6423400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_6423400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423400 prefixEnd_6423400 := by exact prefixLift 6423400
  have htrace : WordTrace (prefixWord ++ tailWord_6423400) baseStart_6423400 baseEnd_6423400 := by
    simpa [prefixWord, tailWord_6423400, baseEnd_6423400] using wordTrace_append hprefix tailTrace_6423400
  have hstable : (prefixWord ++ tailWord_6423400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423400).length < 2 ^ (prefixWord ++ tailWord_6423400).sum := by decide
  have hdescent : baseEnd_6423400 < baseStart_6423400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423417 : List Nat := [1, 2, 1, 3, 2, 3, 4, 1, 1, 5]
def baseStart_6423417 : Nat := 118140960795 + 6423417 * 2 ^ 59
def prefixEnd_6423417 : Nat := 4983230072969 + 3 ^ 40 * 6423417 * 2
def baseEnd_6423417 : Nat := 1099433455087133361715583

theorem tailTrace_6423417 : CollatzResearch.WordTrace tailWord_6423417 prefixEnd_6423417 1099433455087133361715583 := by
  unfold tailWord_6423417
  simp only [CollatzResearch.WordTrace]
  refine ⟨234281264970064716129508505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156187509980043144086339003 234281264970064716129508505)
  ·
    refine ⟨175710948727548537097131379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234281264970064716129508505 175710948727548537097131379)
    ·
      refine ⟨263566423091322805645697069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175710948727548537097131379 263566423091322805645697069)
      ·
        refine ⟨98837408659246052117136401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263566423091322805645697069 98837408659246052117136401)
        ·
          refine ⟨74128056494434539087852301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98837408659246052117136401 74128056494434539087852301)
          ·
            refine ⟨27798021185412952157944613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74128056494434539087852301 27798021185412952157944613)
            ·
              refine ⟨5212128972264928529614615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27798021185412952157944613 5212128972264928529614615)
              ·
                refine ⟨7818193458397392794421923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5212128972264928529614615 7818193458397392794421923)
                ·
                  refine ⟨11727290187596089191632885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7818193458397392794421923 11727290187596089191632885)
                  ·
                    refine ⟨1099433455087133361715583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11727290187596089191632885 1099433455087133361715583)
                    ·
                      rfl

theorem cell23_6423417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 1, 5].length) (baseStart_6423417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423417 prefixEnd_6423417 := by exact prefixLift 6423417
  have htrace : WordTrace (prefixWord ++ tailWord_6423417) baseStart_6423417 baseEnd_6423417 := by
    simpa [prefixWord, tailWord_6423417, baseEnd_6423417] using wordTrace_append hprefix tailTrace_6423417
  have hstable : (prefixWord ++ tailWord_6423417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423417).length < 2 ^ (prefixWord ++ tailWord_6423417).sum := by decide
  have hdescent : baseEnd_6423417 < baseStart_6423417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423420 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 1, 8, 2]
def baseStart_6423420 : Nat := 118140960795 + 6423420 * 2 ^ 59
def prefixEnd_6423420 : Nat := 4983230072969 + 3 ^ 40 * 6423420 * 2
def baseEnd_6423420 : Nat := 3298301905703363573409235

theorem tailTrace_6423420 : CollatzResearch.WordTrace tailWord_6423420 prefixEnd_6423420 3298301905703363573409235 := by
  unfold tailWord_6423420
  simp only [CollatzResearch.WordTrace]
  refine ⟨117140687194526923820933857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156187582926035898427911809 117140687194526923820933857)
  ·
    refine ⟨87855515395895192865700393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117140687194526923820933857 87855515395895192865700393)
    ·
      refine ⟨65891636546921394649275295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87855515395895192865700393 65891636546921394649275295)
      ·
        refine ⟨98837454820382091973912943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65891636546921394649275295 98837454820382091973912943)
        ·
          refine ⟨148256182230573137960869415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98837454820382091973912943 148256182230573137960869415)
          ·
            refine ⟨222384273345859706941304123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148256182230573137960869415 222384273345859706941304123)
            ·
              refine ⟨333576410018789560411956185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222384273345859706941304123 333576410018789560411956185)
              ·
                refine ⟨250182307514092170308967139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333576410018789560411956185 250182307514092170308967139)
                ·
                  refine ⟨375273461271138255463450709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 250182307514092170308967139 375273461271138255463450709)
                  ·
                    refine ⟨4397735874271151431212313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 375273461271138255463450709 4397735874271151431212313)
                    ·
                      refine ⟨3298301905703363573409235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4397735874271151431212313 3298301905703363573409235)
                      ·
                        rfl

theorem cell23_6423420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 8, 2].length) (baseStart_6423420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423420 prefixEnd_6423420 := by exact prefixLift 6423420
  have htrace : WordTrace (prefixWord ++ tailWord_6423420) baseStart_6423420 baseEnd_6423420 := by
    simpa [prefixWord, tailWord_6423420, baseEnd_6423420] using wordTrace_append hprefix tailTrace_6423420
  have hstable : (prefixWord ++ tailWord_6423420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423420).length < 2 ^ (prefixWord ++ tailWord_6423420).sum := by decide
  have hdescent : baseEnd_6423420 < baseStart_6423420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423483 : List Nat := [1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 5]
def baseStart_6423483 : Nat := 118140960795 + 6423483 * 2 ^ 59
def prefixEnd_6423483 : Nat := 4983230072969 + 3 ^ 40 * 6423483 * 2
def baseEnd_6423483 : Nat := 3298334254984596826921445

theorem tailTrace_6423483 : CollatzResearch.WordTrace tailWord_6423483 prefixEnd_6423483 3298334254984596826921445 := by
  unfold tailWord_6423483
  simp only [CollatzResearch.WordTrace]
  refine ⟨234283672187825609401411103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156189114791883739600940735 234283672187825609401411103)
  ·
    refine ⟨351425508281738414102116655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234283672187825609401411103 351425508281738414102116655)
    ·
      refine ⟨527138262422607621153174983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351425508281738414102116655 527138262422607621153174983)
      ·
        refine ⟨790707393633911431729762475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527138262422607621153174983 790707393633911431729762475)
        ·
          refine ⟨1186061090450867147594643713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 790707393633911431729762475 1186061090450867147594643713)
          ·
            refine ⟨889545817838150360695982785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1186061090450867147594643713 889545817838150360695982785)
            ·
              refine ⟨667159363378612770521987089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 889545817838150360695982785 667159363378612770521987089)
              ·
                refine ⟨500369522533959577891490317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 667159363378612770521987089 500369522533959577891490317)
                ·
                  refine ⟨187638570950234841709308869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 500369522533959577891490317 187638570950234841709308869)
                  ·
                    refine ⟨35182232053169032820495413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 187638570950234841709308869 35182232053169032820495413)
                    ·
                      refine ⟨3298334254984596826921445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35182232053169032820495413 3298334254984596826921445)
                      ·
                        rfl

theorem cell23_6423483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 4, 5].length) (baseStart_6423483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423483 prefixEnd_6423483 := by exact prefixLift 6423483
  have htrace : WordTrace (prefixWord ++ tailWord_6423483) baseStart_6423483 baseEnd_6423483 := by
    simpa [prefixWord, tailWord_6423483, baseEnd_6423483] using wordTrace_append hprefix tailTrace_6423483
  have hstable : (prefixWord ++ tailWord_6423483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423483).length < 2 ^ (prefixWord ++ tailWord_6423483).sum := by decide
  have hdescent : baseEnd_6423483 < baseStart_6423483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423488 : List Nat := [2, 1, 1, 2, 3, 4, 3, 2, 1, 2, 2]
def baseStart_6423488 : Nat := 118140960795 + 6423488 * 2 ^ 59
def prefixEnd_6423488 : Nat := 4983230072969 + 3 ^ 40 * 6423488 * 2
def baseEnd_6423488 : Nat := 3298336822387869307358923

theorem tailTrace_6423488 : CollatzResearch.WordTrace tailWord_6423488 prefixEnd_6423488 3298336822387869307358923 := by
  unfold tailWord_6423488
  simp only [CollatzResearch.WordTrace]
  refine ⟨117141927276403747627671559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156189236368538330170228745 117141927276403747627671559)
  ·
    refine ⟨175712890914605621441507339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117141927276403747627671559 175712890914605621441507339)
    ·
      refine ⟨263569336371908432162261009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175712890914605621441507339 263569336371908432162261009)
      ·
        refine ⟨197677002278931324121695757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263569336371908432162261009 197677002278931324121695757)
        ·
          refine ⟨74128875854599246545635909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197677002278931324121695757 74128875854599246545635909)
          ·
            refine ⟨13899164222737358727306733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74128875854599246545635909 13899164222737358727306733)
            ·
              refine ⟨5212186583526509522740025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13899164222737358727306733 5212186583526509522740025)
              ·
                refine ⟨3909139937644882142055019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5212186583526509522740025 3909139937644882142055019)
                ·
                  refine ⟨5863709906467323213082529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3909139937644882142055019 5863709906467323213082529)
                  ·
                    refine ⟨4397782429850492409811897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5863709906467323213082529 4397782429850492409811897)
                    ·
                      refine ⟨3298336822387869307358923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4397782429850492409811897 3298336822387869307358923)
                      ·
                        rfl

theorem cell23_6423488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 1, 2, 2].length) (baseStart_6423488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423488 prefixEnd_6423488 := by exact prefixLift 6423488
  have htrace : WordTrace (prefixWord ++ tailWord_6423488) baseStart_6423488 baseEnd_6423488 := by
    simpa [prefixWord, tailWord_6423488, baseEnd_6423488] using wordTrace_append hprefix tailTrace_6423488
  have hstable : (prefixWord ++ tailWord_6423488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423488).length < 2 ^ (prefixWord ++ tailWord_6423488).sum := by decide
  have hdescent : baseEnd_6423488 < baseStart_6423488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423493 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 10]
def baseStart_6423493 : Nat := 118140960795 + 6423493 * 2 ^ 59
def prefixEnd_6423493 : Nat := 4983230072969 + 3 ^ 40 * 6423493 * 2
def baseEnd_6423493 : Nat := 3298339389791141787796399

theorem tailTrace_6423493 : CollatzResearch.WordTrace tailWord_6423493 prefixEnd_6423493 3298339389791141787796399 := by
  unfold tailWord_6423493
  simp only [CollatzResearch.WordTrace]
  refine ⟨234284036917789381109275133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156189357945192920739516755 234284036917789381109275133)
  ·
    refine ⟨87856513844171017915978175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234284036917789381109275133 87856513844171017915978175)
    ·
      refine ⟨131784770766256526873967263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87856513844171017915978175 131784770766256526873967263)
      ·
        refine ⟨197677156149384790310950895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131784770766256526873967263 197677156149384790310950895)
        ·
          refine ⟨296515734224077185466426343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197677156149384790310950895 296515734224077185466426343)
          ·
            refine ⟨444773601336115778199639515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296515734224077185466426343 444773601336115778199639515)
            ·
              refine ⟨667160402004173667299459273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 444773601336115778199639515 667160402004173667299459273)
              ·
                refine ⟨500370301503130250474594455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 667160402004173667299459273 500370301503130250474594455)
                ·
                  refine ⟨750555452254695375711891683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 500370301503130250474594455 750555452254695375711891683)
                  ·
                    refine ⟨1125833178382043063567837525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 750555452254695375711891683 1125833178382043063567837525)
                    ·
                      refine ⟨3298339389791141787796399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1125833178382043063567837525 3298339389791141787796399)
                      ·
                        rfl

theorem cell23_6423493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_6423493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423493 prefixEnd_6423493 := by exact prefixLift 6423493
  have htrace : WordTrace (prefixWord ++ tailWord_6423493) baseStart_6423493 baseEnd_6423493 := by
    simpa [prefixWord, tailWord_6423493, baseEnd_6423493] using wordTrace_append hprefix tailTrace_6423493
  have hstable : (prefixWord ++ tailWord_6423493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423493).length < 2 ^ (prefixWord ++ tailWord_6423493).sum := by decide
  have hdescent : baseEnd_6423493 < baseStart_6423493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423514 : List Nat := [3, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2]
def baseStart_6423514 : Nat := 118140960795 + 6423514 * 2 ^ 59
def prefixEnd_6423514 : Nat := 4983230072969 + 3 ^ 40 * 6423514 * 2
def baseEnd_6423514 : Nat := 3298350172884886205633803

theorem tailTrace_6423514 : CollatzResearch.WordTrace tailWord_6423514 prefixEnd_6423514 3298350172884886205633803 := by
  unfold tailWord_6423514
  simp only [CollatzResearch.WordTrace]
  refine ⟨58571200712678325423947399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156189868567142201130526397 58571200712678325423947399)
  ·
    refine ⟨87856801069017488135921099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58571200712678325423947399 87856801069017488135921099)
    ·
      refine ⟨131785201603526232203881649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87856801069017488135921099 131785201603526232203881649)
      ·
        refine ⟨98838901202644674152911237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131785201603526232203881649 98838901202644674152911237)
        ·
          refine ⟨18532293975495876403670857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98838901202644674152911237 18532293975495876403670857)
          ·
            refine ⟨13899220481621907302753143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18532293975495876403670857 13899220481621907302753143)
            ·
              refine ⟨20848830722432860954129715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13899220481621907302753143 20848830722432860954129715)
              ·
                refine ⟨31273246083649291431194573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20848830722432860954129715 31273246083649291431194573)
                ·
                  refine ⟨11727467281368484286697965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31273246083649291431194573 11727467281368484286697965)
                  ·
                    refine ⟨4397800230513181607511737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11727467281368484286697965 4397800230513181607511737)
                    ·
                      refine ⟨3298350172884886205633803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4397800230513181607511737 3298350172884886205633803)
                      ·
                        rfl

theorem cell23_6423514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_6423514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423514 prefixEnd_6423514 := by exact prefixLift 6423514
  have htrace : WordTrace (prefixWord ++ tailWord_6423514) baseStart_6423514 baseEnd_6423514 := by
    simpa [prefixWord, tailWord_6423514, baseEnd_6423514] using wordTrace_append hprefix tailTrace_6423514
  have hstable : (prefixWord ++ tailWord_6423514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423514).length < 2 ^ (prefixWord ++ tailWord_6423514).sum := by decide
  have hdescent : baseEnd_6423514 < baseStart_6423514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423538 : List Nat := [3, 2, 1, 5, 1, 1, 2, 2, 2, 1, 3]
def baseStart_6423538 : Nat := 118140960795 + 6423538 * 2 ^ 59
def prefixEnd_6423538 : Nat := 4983230072969 + 3 ^ 40 * 6423538 * 2
def baseEnd_6423538 : Nat := 3298362496420594111733693

theorem tailTrace_6423538 : CollatzResearch.WordTrace tailWord_6423538 prefixEnd_6423538 3298362496420594111733693 := by
  unfold tailWord_6423538
  simp only [CollatzResearch.WordTrace]
  refine ⟨58571419550656588448665817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156190452135084235863108845 58571419550656588448665817)
  ·
    refine ⟨43928564662992441336499363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58571419550656588448665817 43928564662992441336499363)
    ·
      refine ⟨65892846994488662004749045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43928564662992441336499363 65892846994488662004749045)
      ·
        refine ⟨6177454405733312062945223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65892846994488662004749045 6177454405733312062945223)
        ·
          refine ⟨9266181608599968094417835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6177454405733312062945223 9266181608599968094417835)
          ·
            refine ⟨13899272412899952141626753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9266181608599968094417835 13899272412899952141626753)
            ·
              refine ⟨10424454309674964106220065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13899272412899952141626753 10424454309674964106220065)
              ·
                refine ⟨7818340732256223079665049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10424454309674964106220065 7818340732256223079665049)
                ·
                  refine ⟨5863755549192167309748787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7818340732256223079665049 5863755549192167309748787)
                  ·
                    refine ⟨8795633323788250964623181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5863755549192167309748787 8795633323788250964623181)
                    ·
                      refine ⟨3298362496420594111733693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8795633323788250964623181 3298362496420594111733693)
                      ·
                        rfl

theorem cell23_6423538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_6423538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423538 prefixEnd_6423538 := by exact prefixLift 6423538
  have htrace : WordTrace (prefixWord ++ tailWord_6423538) baseStart_6423538 baseEnd_6423538 := by
    simpa [prefixWord, tailWord_6423538, baseEnd_6423538] using wordTrace_append hprefix tailTrace_6423538
  have hstable : (prefixWord ++ tailWord_6423538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423538).length < 2 ^ (prefixWord ++ tailWord_6423538).sum := by decide
  have hdescent : baseEnd_6423538 < baseStart_6423538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423637 : List Nat := [1, 3, 2, 2, 1, 2, 1, 3, 1, 4, 3]
def baseStart_6423637 : Nat := 118140960795 + 6423637 * 2 ^ 59
def prefixEnd_6423637 : Nat := 4983230072969 + 3 ^ 40 * 6423637 * 2
def baseEnd_6423637 : Nat := 3298413331005389224395737

theorem tailTrace_6423637 : CollatzResearch.WordTrace tailWord_6423637 prefixEnd_6423637 3298413331005389224395737 := by
  unfold tailWord_6423637
  simp only [CollatzResearch.WordTrace]
  refine ⟨234289289029267693702517165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156192859352845129135011443 234289289029267693702517165)
  ·
    refine ⟨87858483385975385138443937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234289289029267693702517165 87858483385975385138443937)
    ·
      refine ⟨65893862539481538853832953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87858483385975385138443937 65893862539481538853832953)
      ·
        refine ⟨49420396904611154140374715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65893862539481538853832953 49420396904611154140374715)
        ·
          refine ⟨74130595356916731210562073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49420396904611154140374715 74130595356916731210562073)
          ·
            refine ⟨55597946517687548407921555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74130595356916731210562073 55597946517687548407921555)
            ·
              refine ⟨83396919776531322611882333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55597946517687548407921555 83396919776531322611882333)
              ·
                refine ⟨31273844916199245979455875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83396919776531322611882333 31273844916199245979455875)
                ·
                  refine ⟨46910767374298868969183813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31273844916199245979455875 46910767374298868969183813)
                  ·
                    refine ⟨8795768882681037931721965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46910767374298868969183813 8795768882681037931721965)
                    ·
                      refine ⟨3298413331005389224395737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8795768882681037931721965 3298413331005389224395737)
                      ·
                        rfl

theorem cell23_6423637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 4, 3].length) (baseStart_6423637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423637 prefixEnd_6423637 := by exact prefixLift 6423637
  have htrace : WordTrace (prefixWord ++ tailWord_6423637) baseStart_6423637 baseEnd_6423637 := by
    simpa [prefixWord, tailWord_6423637, baseEnd_6423637] using wordTrace_append hprefix tailTrace_6423637
  have hstable : (prefixWord ++ tailWord_6423637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423637).length < 2 ^ (prefixWord ++ tailWord_6423637).sum := by decide
  have hdescent : baseEnd_6423637 < baseStart_6423637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423640 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 10]
def baseStart_6423640 : Nat := 118140960795 + 6423640 * 2 ^ 59
def prefixEnd_6423640 : Nat := 4983230072969 + 3 ^ 40 * 6423640 * 2
def baseEnd_6423640 : Nat := 366490541271928079184247

theorem tailTrace_6423640 : CollatzResearch.WordTrace tailWord_6423640 prefixEnd_6423640 366490541271928079184247 := by
  unfold tailWord_6423640
  simp only [CollatzResearch.WordTrace]
  refine ⟨117144699224128412607438187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156192932298837883476584249 117144699224128412607438187)
  ·
    refine ⟨175717048836192618911157281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117144699224128412607438187 175717048836192618911157281)
    ·
      refine ⟨131787786627144464183367961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175717048836192618911157281 131787786627144464183367961)
      ·
        refine ⟨98840839970358348137525971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131787786627144464183367961 98840839970358348137525971)
        ·
          refine ⟨148261259955537522206288957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98840839970358348137525971 148261259955537522206288957)
          ·
            refine ⟨55597972483326570827358359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148261259955537522206288957 55597972483326570827358359)
            ·
              refine ⟨83396958724989856241037539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55597972483326570827358359 83396958724989856241037539)
              ·
                refine ⟨125095438087484784361556309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83396958724989856241037539 125095438087484784361556309)
                ·
                  refine ⟨366490541271928079184247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 125095438087484784361556309 366490541271928079184247)
                  ·
                    rfl

theorem cell23_6423640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 10].length) (baseStart_6423640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423640 prefixEnd_6423640 := by exact prefixLift 6423640
  have htrace : WordTrace (prefixWord ++ tailWord_6423640) baseStart_6423640 baseEnd_6423640 := by
    simpa [prefixWord, tailWord_6423640, baseEnd_6423640] using wordTrace_append hprefix tailTrace_6423640
  have hstable : (prefixWord ++ tailWord_6423640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423640).length < 2 ^ (prefixWord ++ tailWord_6423640).sum := by decide
  have hdescent : baseEnd_6423640 < baseStart_6423640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423661 : List Nat := [1, 5, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_6423661 : Nat := 118140960795 + 6423661 * 2 ^ 59
def prefixEnd_6423661 : Nat := 4983230072969 + 3 ^ 40 * 6423661 * 2
def baseEnd_6423661 : Nat := 1099475218180365710165209

theorem tailTrace_6423661 : CollatzResearch.WordTrace tailWord_6423661 prefixEnd_6423661 1099475218180365710165209 := by
  unfold tailWord_6423661
  simp only [CollatzResearch.WordTrace]
  refine ⟨234290164381180745801390837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156193442920787163867593891 234290164381180745801390837)
  ·
    refine ⟨21964702910735694918880391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 234290164381180745801390837 21964702910735694918880391)
    ·
      refine ⟨32947054366103542378320587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21964702910735694918880391 32947054366103542378320587)
      ·
        refine ⟨49420581549155313567480881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32947054366103542378320587 49420581549155313567480881)
        ·
          refine ⟨37065436161866485175610661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49420581549155313567480881 37065436161866485175610661)
          ·
            refine ⟨6949769280349965970426999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37065436161866485175610661 6949769280349965970426999)
            ·
              refine ⟨10424653920524948955640499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6949769280349965970426999 10424653920524948955640499)
              ·
                refine ⟨15636980880787423433460749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10424653920524948955640499 15636980880787423433460749)
                ·
                  refine ⟨5863867830295283787547781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15636980880787423433460749 5863867830295283787547781)
                  ·
                    refine ⟨1099475218180365710165209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5863867830295283787547781 1099475218180365710165209)
                    ·
                      rfl

theorem cell23_6423661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_6423661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423661 prefixEnd_6423661 := by exact prefixLift 6423661
  have htrace : WordTrace (prefixWord ++ tailWord_6423661) baseStart_6423661 baseEnd_6423661 := by
    simpa [prefixWord, tailWord_6423661, baseEnd_6423661] using wordTrace_append hprefix tailTrace_6423661
  have hstable : (prefixWord ++ tailWord_6423661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423661).length < 2 ^ (prefixWord ++ tailWord_6423661).sum := by decide
  have hdescent : baseEnd_6423661 < baseStart_6423661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423727 : List Nat := [1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 5]
def baseStart_6423727 : Nat := 118140960795 + 6423727 * 2 ^ 59
def prefixEnd_6423727 : Nat := 4983230072969 + 3 ^ 40 * 6423727 * 2
def baseEnd_6423727 : Nat := 3298459544264293872270323

theorem tailTrace_6423727 : CollatzResearch.WordTrace tailWord_6423727 prefixEnd_6423727 3298459544264293872270323 := by
  unfold tailWord_6423727
  simp only [CollatzResearch.WordTrace]
  refine ⟨234292571598941639073293435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156195047732627759382195623 234292571598941639073293435)
  ·
    refine ⟨351438857398412458609940153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234292571598941639073293435 351438857398412458609940153)
    ·
      refine ⟨263579143048809343957455115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 351438857398412458609940153 263579143048809343957455115)
      ·
        refine ⟨395368714573214015936182673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263579143048809343957455115 395368714573214015936182673)
        ·
          refine ⟨296526535929910511952137005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395368714573214015936182673 296526535929910511952137005)
          ·
            refine ⟨111197450973716441982051377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 296526535929910511952137005 111197450973716441982051377)
            ·
              refine ⟨83398088230287331486538533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111197450973716441982051377 83398088230287331486538533)
              ·
                refine ⟨15637141543178874653725975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83398088230287331486538533 15637141543178874653725975)
                ·
                  refine ⟨23455712314768311980588963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15637141543178874653725975 23455712314768311980588963)
                  ·
                    refine ⟨35183568472152467970883445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23455712314768311980588963 35183568472152467970883445)
                    ·
                      refine ⟨3298459544264293872270323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35183568472152467970883445 3298459544264293872270323)
                      ·
                        rfl

theorem cell23_6423727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_6423727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423727 prefixEnd_6423727 := by exact prefixLift 6423727
  have htrace : WordTrace (prefixWord ++ tailWord_6423727) baseStart_6423727 baseEnd_6423727 := by
    simpa [prefixWord, tailWord_6423727, baseEnd_6423727] using wordTrace_append hprefix tailTrace_6423727
  have hstable : (prefixWord ++ tailWord_6423727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423727).length < 2 ^ (prefixWord ++ tailWord_6423727).sum := by decide
  have hdescent : baseEnd_6423727 < baseStart_6423727 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423741 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 5, 2, 2]
def baseStart_6423741 : Nat := 118140960795 + 6423741 * 2 ^ 59
def prefixEnd_6423741 : Nat := 4983230072969 + 3 ^ 40 * 6423741 * 2
def baseEnd_6423741 : Nat := 3298466732993456817495259

theorem tailTrace_6423741 : CollatzResearch.WordTrace tailWord_6423741 prefixEnd_6423741 3298466732993456817495259 := by
  unfold tailWord_6423741
  simp only [CollatzResearch.WordTrace]
  refine ⟨234293082220890919464303077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156195388147260612976202051 234293082220890919464303077)
  ·
    refine ⟨43929952916417047399556827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 234293082220890919464303077 43929952916417047399556827)
    ·
      refine ⟨65894929374625571099335241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43929952916417047399556827 65894929374625571099335241)
      ·
        refine ⟨49421197030969178324501431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65894929374625571099335241 49421197030969178324501431)
        ·
          refine ⟨74131795546453767486752147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49421197030969178324501431 74131795546453767486752147)
          ·
            refine ⟨111197693319680651230128221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74131795546453767486752147 111197693319680651230128221)
            ·
              refine ⟨41699134994880244211298083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111197693319680651230128221 41699134994880244211298083)
              ·
                refine ⟨62548702492320366316947125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41699134994880244211298083 62548702492320366316947125)
                ·
                  refine ⟨5863940858655034342213793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62548702492320366316947125 5863940858655034342213793)
                  ·
                    refine ⟨4397955643991275756660345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5863940858655034342213793 4397955643991275756660345)
                    ·
                      refine ⟨3298466732993456817495259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4397955643991275756660345 3298466732993456817495259)
                      ·
                        rfl

theorem cell23_6423741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_6423741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423741 prefixEnd_6423741 := by exact prefixLift 6423741
  have htrace : WordTrace (prefixWord ++ tailWord_6423741) baseStart_6423741 baseEnd_6423741 := by
    simpa [prefixWord, tailWord_6423741, baseEnd_6423741] using wordTrace_append hprefix tailTrace_6423741
  have hstable : (prefixWord ++ tailWord_6423741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423741).length < 2 ^ (prefixWord ++ tailWord_6423741).sum := by decide
  have hdescent : baseEnd_6423741 < baseStart_6423741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423745 : List Nat := [1, 2, 6, 1, 1, 3, 1, 1, 2, 3, 2]
def baseStart_6423745 : Nat := 118140960795 + 6423745 * 2 ^ 59
def prefixEnd_6423745 : Nat := 4983230072969 + 3 ^ 40 * 6423745 * 2
def baseEnd_6423745 : Nat := 3298468786916074801845241

theorem tailTrace_6423745 : CollatzResearch.WordTrace tailWord_6423745 prefixEnd_6423745 3298468786916074801845241 := by
  unfold tailWord_6423745
  simp only [CollatzResearch.WordTrace]
  refine ⟨234293228112876428147448689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156195485408584285431632459 234293228112876428147448689)
  ·
    refine ⟨175719921084657321110586517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234293228112876428147448689 175719921084657321110586517)
    ·
      refine ⟨8236871300843311927058743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 175719921084657321110586517 8236871300843311927058743)
      ·
        refine ⟨12355306951264967890588115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8236871300843311927058743 12355306951264967890588115)
        ·
          refine ⟨18532960426897451835882173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12355306951264967890588115 18532960426897451835882173)
          ·
            refine ⟨6949860160086544438455815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18532960426897451835882173 6949860160086544438455815)
            ·
              refine ⟨10424790240129816657683723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6949860160086544438455815 10424790240129816657683723)
              ·
                refine ⟨15637185360194724986525585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10424790240129816657683723 15637185360194724986525585)
                ·
                  refine ⟨11727889020146043739894189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15637185360194724986525585 11727889020146043739894189)
                  ·
                    refine ⟨4397958382554766402460321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11727889020146043739894189 4397958382554766402460321)
                    ·
                      refine ⟨3298468786916074801845241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4397958382554766402460321 3298468786916074801845241)
                      ·
                        rfl

theorem cell23_6423745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 3, 2].length) (baseStart_6423745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423745 prefixEnd_6423745 := by exact prefixLift 6423745
  have htrace : WordTrace (prefixWord ++ tailWord_6423745) baseStart_6423745 baseEnd_6423745 := by
    simpa [prefixWord, tailWord_6423745, baseEnd_6423745] using wordTrace_append hprefix tailTrace_6423745
  have hstable : (prefixWord ++ tailWord_6423745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423745).length < 2 ^ (prefixWord ++ tailWord_6423745).sum := by decide
  have hdescent : baseEnd_6423745 < baseStart_6423745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423754 : List Nat := [3, 1, 2, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_6423754 : Nat := 118140960795 + 6423754 * 2 ^ 59
def prefixEnd_6423754 : Nat := 4983230072969 + 3 ^ 40 * 6423754 * 2
def baseEnd_6423754 : Nat := 3298473408241965266632699

theorem tailTrace_6423754 : CollatzResearch.WordTrace tailWord_6423754 prefixEnd_6423754 3298473408241965266632699 := by
  unfold tailWord_6423754
  simp only [CollatzResearch.WordTrace]
  refine ⟨58573389092460955671131579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156195704246562548456350877 58573389092460955671131579)
  ·
    refine ⟨87860083638691433506697369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58573389092460955671131579 87860083638691433506697369)
    ·
      refine ⟨65895062729018575130023027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87860083638691433506697369 65895062729018575130023027)
      ·
        refine ⟨98842594093527862695034541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65895062729018575130023027 98842594093527862695034541)
        ·
          refine ⟨37065972785072948510637953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98842594093527862695034541 37065972785072948510637953)
          ·
            refine ⟨27799479588804711382978465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37065972785072948510637953 27799479588804711382978465)
            ·
              refine ⟨20849609691603533537233849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27799479588804711382978465 20849609691603533537233849)
              ·
                refine ⟨15637207268702650152925387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20849609691603533537233849 15637207268702650152925387)
                ·
                  refine ⟨23455810903053975229388081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15637207268702650152925387 23455810903053975229388081)
                  ·
                    refine ⟨17591858177290481422041061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23455810903053975229388081 17591858177290481422041061)
                    ·
                      refine ⟨3298473408241965266632699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17591858177290481422041061 3298473408241965266632699)
                      ·
                        rfl

theorem cell23_6423754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_6423754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423754 prefixEnd_6423754 := by exact prefixLift 6423754
  have htrace : WordTrace (prefixWord ++ tailWord_6423754) baseStart_6423754 baseEnd_6423754 := by
    simpa [prefixWord, tailWord_6423754, baseEnd_6423754] using wordTrace_append hprefix tailTrace_6423754
  have hstable : (prefixWord ++ tailWord_6423754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423754).length < 2 ^ (prefixWord ++ tailWord_6423754).sum := by decide
  have hdescent : baseEnd_6423754 < baseStart_6423754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423768 : List Nat := [2, 1, 2, 2, 5, 2, 1, 2, 2, 4]
def baseStart_6423768 : Nat := 118140960795 + 6423768 * 2 ^ 59
def prefixEnd_6423768 : Nat := 4983230072969 + 3 ^ 40 * 6423768 * 2
def baseEnd_6423768 : Nat := 1099493532323709403952545

theorem tailTrace_6423768 : CollatzResearch.WordTrace tailWord_6423768 prefixEnd_6423768 1099493532323709403952545 := by
  unfold tailWord_6423768
  simp only [CollatzResearch.WordTrace]
  refine ⟨117147033495896551537767979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156196044661195402050357305 117147033495896551537767979)
  ·
    refine ⟨175720550243844827306651969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117147033495896551537767979 175720550243844827306651969)
    ·
      refine ⟨131790412682883620479988977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175720550243844827306651969 131790412682883620479988977)
      ·
        refine ⟨98842809512162715359991733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131790412682883620479988977 98842809512162715359991733)
        ·
          refine ⟨9266513391765254564999225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98842809512162715359991733 9266513391765254564999225)
          ·
            refine ⟨6949885043823940923749419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9266513391765254564999225 6949885043823940923749419)
            ·
              refine ⟨10424827565735911385624129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6949885043823940923749419 10424827565735911385624129)
              ·
                refine ⟨7818620674301933539218097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10424827565735911385624129 7818620674301933539218097)
                ·
                  refine ⟨5863965505726450154413573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7818620674301933539218097 5863965505726450154413573)
                  ·
                    refine ⟨1099493532323709403952545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5863965505726450154413573 1099493532323709403952545)
                    ·
                      rfl

theorem cell23_6423768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 2, 2, 4].length) (baseStart_6423768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423768 prefixEnd_6423768 := by exact prefixLift 6423768
  have htrace : WordTrace (prefixWord ++ tailWord_6423768) baseStart_6423768 baseEnd_6423768 := by
    simpa [prefixWord, tailWord_6423768, baseEnd_6423768] using wordTrace_append hprefix tailTrace_6423768
  have hstable : (prefixWord ++ tailWord_6423768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423768).length < 2 ^ (prefixWord ++ tailWord_6423768).sum := by decide
  have hdescent : baseEnd_6423768 < baseStart_6423768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423826 : List Nat := [3, 2, 4, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_6423826 : Nat := 118140960795 + 6423826 * 2 ^ 59
def prefixEnd_6423826 : Nat := 4983230072969 + 3 ^ 40 * 6423826 * 2
def baseEnd_6423826 : Nat := 3298510378849088984932369

theorem tailTrace_6423826 : CollatzResearch.WordTrace tailWord_6423826 prefixEnd_6423826 3298510378849088984932369 := by
  unfold tailWord_6423826
  simp only [CollatzResearch.WordTrace]
  refine ⟨58574045606395744745286833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156197454950388652654098221 58574045606395744745286833)
  ·
    refine ⟨43930534204796808558965125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58574045606395744745286833 43930534204796808558965125)
    ·
      refine ⟨8236975163399401604805961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43930534204796808558965125 8236975163399401604805961)
      ·
        refine ⟨6177731372549551203604471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8236975163399401604805961 6177731372549551203604471)
        ·
          refine ⟨9266597058824326805406707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6177731372549551203604471 9266597058824326805406707)
          ·
            refine ⟨13899895588236490208110061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9266597058824326805406707 13899895588236490208110061)
            ·
              refine ⟨5212460845588683828041273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13899895588236490208110061 5212460845588683828041273)
              ·
                refine ⟨3909345634191512871030955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5212460845588683828041273 3909345634191512871030955)
                ·
                  refine ⟨5864018451287269306546433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3909345634191512871030955 5864018451287269306546433)
                  ·
                    refine ⟨4398013838465451979909825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5864018451287269306546433 4398013838465451979909825)
                    ·
                      refine ⟨3298510378849088984932369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4398013838465451979909825 3298510378849088984932369)
                      ·
                        rfl

theorem cell23_6423826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_6423826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423826 prefixEnd_6423826 := by exact prefixLift 6423826
  have htrace : WordTrace (prefixWord ++ tailWord_6423826) baseStart_6423826 baseEnd_6423826 := by
    simpa [prefixWord, tailWord_6423826, baseEnd_6423826] using wordTrace_append hprefix tailTrace_6423826
  have hstable : (prefixWord ++ tailWord_6423826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423826).length < 2 ^ (prefixWord ++ tailWord_6423826).sum := by decide
  have hdescent : baseEnd_6423826 < baseStart_6423826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423842 : List Nat := [3, 3, 1, 1, 4, 2, 2, 1, 2, 1, 3]
def baseStart_6423842 : Nat := 118140960795 + 6423842 * 2 ^ 59
def prefixEnd_6423842 : Nat := 4983230072969 + 3 ^ 40 * 6423842 * 2
def baseEnd_6423842 : Nat := 3298518594539560922332295

theorem tailTrace_6423842 : CollatzResearch.WordTrace tailWord_6423842 prefixEnd_6423842 3298518594539560922332295 := by
  unfold tailWord_6423842
  simp only [CollatzResearch.WordTrace]
  refine ⟨58574191498381253428432445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156197843995683342475819853 58574191498381253428432445)
  ·
    refine ⟨21965321811892970035662167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58574191498381253428432445 21965321811892970035662167)
    ·
      refine ⟨32947982717839455053493251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21965321811892970035662167 32947982717839455053493251)
      ·
        refine ⟨49421974076759182580239877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32947982717839455053493251 49421974076759182580239877)
        ·
          refine ⟨9266620139392346733794977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49421974076759182580239877 9266620139392346733794977)
          ·
            refine ⟨6949965104544260050346233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9266620139392346733794977 6949965104544260050346233)
            ·
              refine ⟨5212473828408195037759675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6949965104544260050346233 5212473828408195037759675)
              ·
                refine ⟨7818710742612292556639513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5212473828408195037759675 7818710742612292556639513)
                ·
                  refine ⟨5864033056959219417479635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7818710742612292556639513 5864033056959219417479635)
                  ·
                    refine ⟨8796049585438829126219453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5864033056959219417479635 8796049585438829126219453)
                    ·
                      refine ⟨3298518594539560922332295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8796049585438829126219453 3298518594539560922332295)
                      ·
                        rfl

theorem cell23_6423842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_6423842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423842 prefixEnd_6423842 := by exact prefixLift 6423842
  have htrace : WordTrace (prefixWord ++ tailWord_6423842) baseStart_6423842 baseEnd_6423842 := by
    simpa [prefixWord, tailWord_6423842, baseEnd_6423842] using wordTrace_append hprefix tailTrace_6423842
  have hstable : (prefixWord ++ tailWord_6423842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423842).length < 2 ^ (prefixWord ++ tailWord_6423842).sum := by decide
  have hdescent : baseEnd_6423842 < baseStart_6423842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423844 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_6423844 : Nat := 118140960795 + 6423844 * 2 ^ 59
def prefixEnd_6423844 : Nat := 4983230072969 + 3 ^ 40 * 6423844 * 2
def baseEnd_6423844 : Nat := 3298519621500869914507285

theorem tailTrace_6423844 : CollatzResearch.WordTrace tailWord_6423844 prefixEnd_6423844 3298519621500869914507285 := by
  unfold tailWord_6423844
  simp only [CollatzResearch.WordTrace]
  refine ⟨117148419469758884027651293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156197892626345178703535057 117148419469758884027651293)
  ·
    refine ⟨43930657301159581510369235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117148419469758884027651293 43930657301159581510369235)
    ·
      refine ⟨65895985951739372265553853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43930657301159581510369235 65895985951739372265553853)
      ·
        refine ⟨24710994731902264599582695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65895985951739372265553853 24710994731902264599582695)
        ·
          refine ⟨37066492097853396899374043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24710994731902264599582695 37066492097853396899374043)
          ·
            refine ⟨55599738146780095349061065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37066492097853396899374043 55599738146780095349061065)
            ·
              refine ⟨41699803610085071511795799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55599738146780095349061065 41699803610085071511795799)
              ·
                refine ⟨62549705415127607267693699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41699803610085071511795799 62549705415127607267693699)
                ·
                  refine ⟨93824558122691410901540549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62549705415127607267693699 93824558122691410901540549)
                  ·
                    refine ⟨17592104648004639544038853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 93824558122691410901540549 17592104648004639544038853)
                    ·
                      refine ⟨3298519621500869914507285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17592104648004639544038853 3298519621500869914507285)
                      ·
                        rfl

theorem cell23_6423844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_6423844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423844 prefixEnd_6423844 := by exact prefixLift 6423844
  have htrace : WordTrace (prefixWord ++ tailWord_6423844) baseStart_6423844 baseEnd_6423844 := by
    simpa [prefixWord, tailWord_6423844, baseEnd_6423844] using wordTrace_append hprefix tailTrace_6423844
  have hstable : (prefixWord ++ tailWord_6423844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423844).length < 2 ^ (prefixWord ++ tailWord_6423844).sum := by decide
  have hdescent : baseEnd_6423844 < baseStart_6423844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423864 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 4, 3, 3]
def baseStart_6423864 : Nat := 118140960795 + 6423864 * 2 ^ 59
def prefixEnd_6423864 : Nat := 4983230072969 + 3 ^ 40 * 6423864 * 2
def baseEnd_6423864 : Nat := 3298529891113959836257193

theorem tailTrace_6423864 : CollatzResearch.WordTrace tailWord_6423864 prefixEnd_6423864 3298529891113959836257193 := by
  unfold tailWord_6423864
  simp only [CollatzResearch.WordTrace]
  refine ⟨117148784199722655735515323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156198378932963540980687097 117148784199722655735515323)
  ·
    refine ⟨175723176299583983603272985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117148784199722655735515323 175723176299583983603272985)
    ·
      refine ⟨131792382224687987702454739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175723176299583983603272985 131792382224687987702454739)
      ·
        refine ⟨197688573337031981553682109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131792382224687987702454739 197688573337031981553682109)
        ·
          refine ⟨74133215001386993082630791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197688573337031981553682109 74133215001386993082630791)
          ·
            refine ⟨111199822502080489623946187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74133215001386993082630791 111199822502080489623946187)
            ·
              refine ⟨166799733753120734435919281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111199822502080489623946187 166799733753120734435919281)
              ·
                refine ⟨125099800314840550826939461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166799733753120734435919281 125099800314840550826939461)
                ·
                  refine ⟨23456212559032603280051149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 125099800314840550826939461 23456212559032603280051149)
                  ·
                    refine ⟨8796079709637226230019181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23456212559032603280051149 8796079709637226230019181)
                    ·
                      refine ⟨3298529891113959836257193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8796079709637226230019181 3298529891113959836257193)
                      ·
                        rfl

theorem cell23_6423864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_6423864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423864 prefixEnd_6423864 := by exact prefixLift 6423864
  have htrace : WordTrace (prefixWord ++ tailWord_6423864) baseStart_6423864 baseEnd_6423864 := by
    simpa [prefixWord, tailWord_6423864, baseEnd_6423864] using wordTrace_append hprefix tailTrace_6423864
  have hstable : (prefixWord ++ tailWord_6423864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423864).length < 2 ^ (prefixWord ++ tailWord_6423864).sum := by decide
  have hdescent : baseEnd_6423864 < baseStart_6423864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423867 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 7, 7]
def baseStart_6423867 : Nat := 118140960795 + 6423867 * 2 ^ 59
def prefixEnd_6423867 : Nat := 4983230072969 + 3 ^ 40 * 6423867 * 2
def baseEnd_6423867 : Nat := 1099510477185307774839893

theorem tailTrace_6423867 : CollatzResearch.WordTrace tailWord_6423867 prefixEnd_6423867 1099510477185307774839893 := by
  unfold tailWord_6423867
  simp only [CollatzResearch.WordTrace]
  refine ⟨234297677818434442983389855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156198451878956295322259903 234297677818434442983389855)
  ·
    refine ⟨351446516727651664475084783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234297677818434442983389855 351446516727651664475084783)
    ·
      refine ⟨527169775091477496712627175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351446516727651664475084783 527169775091477496712627175)
      ·
        refine ⟨790754662637216245068940763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 527169775091477496712627175 790754662637216245068940763)
        ·
          refine ⟨1186131993955824367603411145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 790754662637216245068940763 1186131993955824367603411145)
          ·
            refine ⟨889598995466868275702558359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1186131993955824367603411145 889598995466868275702558359)
            ·
              refine ⟨1334398493200302413553837539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889598995466868275702558359 1334398493200302413553837539)
              ·
                refine ⟨2001597739800453620330756309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1334398493200302413553837539 2001597739800453620330756309)
                ·
                  refine ⟨46912447026573131726502101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2001597739800453620330756309 46912447026573131726502101)
                  ·
                    refine ⟨1099510477185307774839893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46912447026573131726502101 1099510477185307774839893)
                    ·
                      rfl

theorem cell23_6423867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 7].length) (baseStart_6423867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423867 prefixEnd_6423867 := by exact prefixLift 6423867
  have htrace : WordTrace (prefixWord ++ tailWord_6423867) baseStart_6423867 baseEnd_6423867 := by
    simpa [prefixWord, tailWord_6423867, baseEnd_6423867] using wordTrace_append hprefix tailTrace_6423867
  have hstable : (prefixWord ++ tailWord_6423867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423867).length < 2 ^ (prefixWord ++ tailWord_6423867).sum := by decide
  have hdescent : baseEnd_6423867 < baseStart_6423867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423918 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 1, 7]
def baseStart_6423918 : Nat := 118140960795 + 6423918 * 2 ^ 59
def prefixEnd_6423918 : Nat := 4983230072969 + 3 ^ 40 * 6423918 * 2
def baseEnd_6423918 : Nat := 1099519206356434208327315

theorem tailTrace_6423918 : CollatzResearch.WordTrace tailWord_6423918 prefixEnd_6423918 1099519206356434208327315 := by
  unfold tailWord_6423918
  simp only [CollatzResearch.WordTrace]
  refine ⟨29287442242656209836687051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 156199691960833119128997605 29287442242656209836687051)
  ·
    refine ⟨43931163363984314755030577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29287442242656209836687051 43931163363984314755030577)
    ·
      refine ⟨32948372522988236066272933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43931163363984314755030577 32948372522988236066272933)
      ·
        refine ⟨6177819848060294262426175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32948372522988236066272933 6177819848060294262426175)
        ·
          refine ⟨9266729772090441393639263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6177819848060294262426175 9266729772090441393639263)
          ·
            refine ⟨13900094658135662090458895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9266729772090441393639263 13900094658135662090458895)
            ·
              refine ⟨20850141987203493135688343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13900094658135662090458895 20850141987203493135688343)
              ·
                refine ⟨31275212980805239703532515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20850141987203493135688343 31275212980805239703532515)
                ·
                  refine ⟨46912819471207859555298773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31275212980805239703532515 46912819471207859555298773)
                  ·
                    refine ⟨1099519206356434208327315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46912819471207859555298773 1099519206356434208327315)
                    ·
                      rfl

theorem cell23_6423918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_6423918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423918 prefixEnd_6423918 := by exact prefixLift 6423918
  have htrace : WordTrace (prefixWord ++ tailWord_6423918) baseStart_6423918 baseEnd_6423918 := by
    simpa [prefixWord, tailWord_6423918, baseEnd_6423918] using wordTrace_append hprefix tailTrace_6423918
  have hstable : (prefixWord ++ tailWord_6423918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423918).length < 2 ^ (prefixWord ++ tailWord_6423918).sum := by decide
  have hdescent : baseEnd_6423918 < baseStart_6423918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423921 : List Nat := [1, 2, 2, 2, 1, 2, 5, 1, 2, 1, 4]
def baseStart_6423921 : Nat := 118140960795 + 6423921 * 2 ^ 59
def prefixEnd_6423921 : Nat := 4983230072969 + 3 ^ 40 * 6423921 * 2
def baseEnd_6423921 : Nat := 3298559159511266113244431

theorem tailTrace_6423921 : CollatzResearch.WordTrace tailWord_6423921 prefixEnd_6423921 3298559159511266113244431 := by
  unfold tailWord_6423921
  simp only [CollatzResearch.WordTrace]
  refine ⟨234299647360238810205855617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156199764906825873470570411 234299647360238810205855617)
  ·
    refine ⟨175724735520179107654391713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234299647360238810205855617 175724735520179107654391713)
    ·
      refine ⟨131793551640134330740793785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175724735520179107654391713 131793551640134330740793785)
      ·
        refine ⟨98845163730100748055595339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131793551640134330740793785 98845163730100748055595339)
        ·
          refine ⟨148267745595151122083393009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98845163730100748055595339 148267745595151122083393009)
          ·
            refine ⟨111200809196363341562544757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148267745595151122083393009 111200809196363341562544757)
            ·
              refine ⟨10425075862159063271488571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111200809196363341562544757 10425075862159063271488571)
              ·
                refine ⟨15637613793238594907232857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10425075862159063271488571 15637613793238594907232857)
                ·
                  refine ⟨11728210344928946180424643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15637613793238594907232857 11728210344928946180424643)
                  ·
                    refine ⟨17592315517393419270636965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11728210344928946180424643 17592315517393419270636965)
                    ·
                      refine ⟨3298559159511266113244431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17592315517393419270636965 3298559159511266113244431)
                      ·
                        rfl

theorem cell23_6423921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_6423921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423921 prefixEnd_6423921 := by exact prefixLift 6423921
  have htrace : WordTrace (prefixWord ++ tailWord_6423921) baseStart_6423921 baseEnd_6423921 := by
    simpa [prefixWord, tailWord_6423921, baseEnd_6423921] using wordTrace_append hprefix tailTrace_6423921
  have hstable : (prefixWord ++ tailWord_6423921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423921).length < 2 ^ (prefixWord ++ tailWord_6423921).sum := by decide
  have hdescent : baseEnd_6423921 < baseStart_6423921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423941 : List Nat := [1, 3, 1, 1, 3, 1, 2, 4, 2, 2, 3]
def baseStart_6423941 : Nat := 118140960795 + 6423941 * 2 ^ 59
def prefixEnd_6423941 : Nat := 4983230072969 + 3 ^ 40 * 6423941 * 2
def baseEnd_6423941 : Nat := 3298569429124356034994339

theorem tailTrace_6423941 : CollatzResearch.WordTrace tailWord_6423941 prefixEnd_6423941 3298569429124356034994339 := by
  unfold tailWord_6423941
  simp only [CollatzResearch.WordTrace]
  refine ⟨234300376820166353621583677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156200251213444235747722451 234300376820166353621583677)
  ·
    refine ⟨87862641307562382608093879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234300376820166353621583677 87862641307562382608093879)
    ·
      refine ⟨131793961961343573912140819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87862641307562382608093879 131793961961343573912140819)
      ·
        refine ⟨197690942942015360868211229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131793961961343573912140819 197690942942015360868211229)
        ·
          refine ⟨74134103603255760325579211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197690942942015360868211229 74134103603255760325579211)
          ·
            refine ⟨111201155404883640488368817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74134103603255760325579211 111201155404883640488368817)
            ·
              refine ⟨83400866553662730366276613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111201155404883640488368817 83400866553662730366276613)
              ·
                refine ⟨15637662478811761943676865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83400866553662730366276613 15637662478811761943676865)
                ·
                  refine ⟨11728246859108821457757649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15637662478811761943676865 11728246859108821457757649)
                  ·
                    refine ⟨8796185144331616093318237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11728246859108821457757649 8796185144331616093318237)
                    ·
                      refine ⟨3298569429124356034994339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8796185144331616093318237 3298569429124356034994339)
                      ·
                        rfl

theorem cell23_6423941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_6423941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423941 prefixEnd_6423941 := by exact prefixLift 6423941
  have htrace : WordTrace (prefixWord ++ tailWord_6423941) baseStart_6423941 baseEnd_6423941 := by
    simpa [prefixWord, tailWord_6423941, baseEnd_6423941] using wordTrace_append hprefix tailTrace_6423941
  have hstable : (prefixWord ++ tailWord_6423941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423941).length < 2 ^ (prefixWord ++ tailWord_6423941).sum := by decide
  have hdescent : baseEnd_6423941 < baseStart_6423941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423948 : List Nat := [2, 2, 1, 2, 1, 3, 1, 6, 1, 4]
def baseStart_6423948 : Nat := 118140960795 + 6423948 * 2 ^ 59
def prefixEnd_6423948 : Nat := 4983230072969 + 3 ^ 40 * 6423948 * 2
def baseEnd_6423948 : Nat := 1099524341162979169202269

theorem tailTrace_6423948 : CollatzResearch.WordTrace tailWord_6423948 prefixEnd_6423948 1099524341162979169202269 := by
  unfold tailWord_6423948
  simp only [CollatzResearch.WordTrace]
  refine ⟨117150316065570496908544249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156200421420760662544725665 117150316065570496908544249)
  ·
    refine ⟨87862737049177872681408187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117150316065570496908544249 87862737049177872681408187)
    ·
      refine ⟨131794105573766809022112281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87862737049177872681408187 131794105573766809022112281)
      ·
        refine ⟨98845579180325106766584211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131794105573766809022112281 98845579180325106766584211)
        ·
          refine ⟨148268368770487660149876317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98845579180325106766584211 148268368770487660149876317)
          ·
            refine ⟨55600638288932872556203619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148268368770487660149876317 55600638288932872556203619)
            ·
              refine ⟨83400957433399308834305429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55600638288932872556203619 83400957433399308834305429)
              ·
                refine ⟨3909419879690592601608067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83400957433399308834305429 3909419879690592601608067)
                ·
                  refine ⟨5864129819535888902412101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3909419879690592601608067 5864129819535888902412101)
                  ·
                    refine ⟨1099524341162979169202269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5864129819535888902412101 1099524341162979169202269)
                    ·
                      rfl

theorem cell23_6423948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 6, 1, 4].length) (baseStart_6423948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423948 prefixEnd_6423948 := by exact prefixLift 6423948
  have htrace : WordTrace (prefixWord ++ tailWord_6423948) baseStart_6423948 baseEnd_6423948 := by
    simpa [prefixWord, tailWord_6423948, baseEnd_6423948] using wordTrace_append hprefix tailTrace_6423948
  have hstable : (prefixWord ++ tailWord_6423948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423948).length < 2 ^ (prefixWord ++ tailWord_6423948).sum := by decide
  have hdescent : baseEnd_6423948 < baseStart_6423948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6423991 : List Nat := [1, 1, 3, 1, 3, 2, 1, 5, 1, 5]
def baseStart_6423991 : Nat := 118140960795 + 6423991 * 2 ^ 59
def prefixEnd_6423991 : Nat := 4983230072969 + 3 ^ 40 * 6423991 * 2
def baseEnd_6423991 : Nat := 1099531701052360279789703

theorem tailTrace_6423991 : CollatzResearch.WordTrace tailWord_6423991 prefixEnd_6423991 1099531701052360279789703 := by
  unfold tailWord_6423991
  simp only [CollatzResearch.WordTrace]
  refine ⟨234302200469985212160903827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156201466979990141440602551 234302200469985212160903827)
  ·
    refine ⟨351453300704977818241355741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234302200469985212160903827 351453300704977818241355741)
    ·
      refine ⟨131794987764366681840508403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 351453300704977818241355741 131794987764366681840508403)
      ·
        refine ⟨197692481646550022760762605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131794987764366681840508403 197692481646550022760762605)
        ·
          refine ⟨74134680617456258535285977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197692481646550022760762605 74134680617456258535285977)
          ·
            refine ⟨55601010463092193901464483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74134680617456258535285977 55601010463092193901464483)
            ·
              refine ⟨83401515694638290852196725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55601010463092193901464483 83401515694638290852196725)
              ·
                refine ⟨7818892096372339767393443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 83401515694638290852196725 7818892096372339767393443)
                ·
                  refine ⟨11728338144558509651090165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7818892096372339767393443 11728338144558509651090165)
                  ·
                    refine ⟨1099531701052360279789703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11728338144558509651090165 1099531701052360279789703)
                    ·
                      rfl

theorem cell23_6423991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_6423991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6423991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6423991 prefixEnd_6423991 := by exact prefixLift 6423991
  have htrace : WordTrace (prefixWord ++ tailWord_6423991) baseStart_6423991 baseEnd_6423991 := by
    simpa [prefixWord, tailWord_6423991, baseEnd_6423991] using wordTrace_append hprefix tailTrace_6423991
  have hstable : (prefixWord ++ tailWord_6423991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6423991).length < 2 ^ (prefixWord ++ tailWord_6423991).sum := by decide
  have hdescent : baseEnd_6423991 < baseStart_6423991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6423991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424021 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 1, 6]
def baseStart_6424021 : Nat := 118140960795 + 6424021 * 2 ^ 59
def prefixEnd_6424021 : Nat := 4983230072969 + 3 ^ 40 * 6424021 * 2
def baseEnd_6424021 : Nat := 1099536835858905240664657

theorem tailTrace_6424021 : CollatzResearch.WordTrace tailWord_6424021 prefixEnd_6424021 1099536835858905240664657 := by
  unfold tailWord_6424021
  simp only [CollatzResearch.WordTrace]
  refine ⟨234303294659876527284495917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156202196439917684856330611 234303294659876527284495917)
  ·
    refine ⟨87863735497453697731685969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 234303294659876527284495917 87863735497453697731685969)
    ·
      refine ⟨65897801623090273298764477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87863735497453697731685969 65897801623090273298764477)
      ·
        refine ⟨24711675608658852487036679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65897801623090273298764477 24711675608658852487036679)
        ·
          refine ⟨37067513412988278730555019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24711675608658852487036679 37067513412988278730555019)
          ·
            refine ⟨55601270119482418095832529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37067513412988278730555019 55601270119482418095832529)
            ·
              refine ⟨41700952589611813571874397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55601270119482418095832529 41700952589611813571874397)
              ·
                refine ⟨15637857221104430089452899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41700952589611813571874397 15637857221104430089452899)
                ·
                  refine ⟨23456785831656645134179349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15637857221104430089452899 23456785831656645134179349)
                  ·
                    refine ⟨1099536835858905240664657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23456785831656645134179349 1099536835858905240664657)
                    ·
                      rfl

theorem cell23_6424021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_6424021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424021 prefixEnd_6424021 := by exact prefixLift 6424021
  have htrace : WordTrace (prefixWord ++ tailWord_6424021) baseStart_6424021 baseEnd_6424021 := by
    simpa [prefixWord, tailWord_6424021, baseEnd_6424021] using wordTrace_append hprefix tailTrace_6424021
  have hstable : (prefixWord ++ tailWord_6424021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424021).length < 2 ^ (prefixWord ++ tailWord_6424021).sum := by decide
  have hdescent : baseEnd_6424021 < baseStart_6424021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424048 : List Nat := [2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 5]
def baseStart_6424048 : Nat := 118140960795 + 6424048 * 2 ^ 59
def prefixEnd_6424048 : Nat := 4983230072969 + 3 ^ 40 * 6424048 * 2
def baseEnd_6424048 : Nat := 3298624371554387116356347

theorem tailTrace_6424048 : CollatzResearch.WordTrace tailWord_6424048 prefixEnd_6424048 3298624371554387116356347 := by
  unfold tailWord_6424048
  simp only [CollatzResearch.WordTrace]
  refine ⟨117152139715389355447864399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156202852953852473930485865 117152139715389355447864399)
  ·
    refine ⟨175728209573084033171796599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117152139715389355447864399 175728209573084033171796599)
    ·
      refine ⟨263592314359626049757694899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175728209573084033171796599 263592314359626049757694899)
      ·
        refine ⟨395388471539439074636542349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263592314359626049757694899 395388471539439074636542349)
        ·
          refine ⟨148270676827289652988703381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395388471539439074636542349 148270676827289652988703381)
          ·
            refine ⟨6950187976279202483845471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 148270676827289652988703381 6950187976279202483845471)
            ·
              refine ⟨10425281964418803725768207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6950187976279202483845471 10425281964418803725768207)
              ·
                refine ⟨15637922946628205588652311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10425281964418803725768207 15637922946628205588652311)
                ·
                  refine ⟨23456884419942308382978467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15637922946628205588652311 23456884419942308382978467)
                  ·
                    refine ⟨35185326629913462574467701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23456884419942308382978467 35185326629913462574467701)
                    ·
                      refine ⟨3298624371554387116356347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35185326629913462574467701 3298624371554387116356347)
                      ·
                        rfl

theorem cell23_6424048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 5].length) (baseStart_6424048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424048 prefixEnd_6424048 := by exact prefixLift 6424048
  have htrace : WordTrace (prefixWord ++ tailWord_6424048) baseStart_6424048 baseEnd_6424048 := by
    simpa [prefixWord, tailWord_6424048, baseEnd_6424048] using wordTrace_append hprefix tailTrace_6424048
  have hstable : (prefixWord ++ tailWord_6424048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424048).length < 2 ^ (prefixWord ++ tailWord_6424048).sum := by decide
  have hdescent : baseEnd_6424048 < baseStart_6424048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424099 : List Nat := [1, 1, 1, 4, 6, 1, 2, 1, 1, 2, 3]
def baseStart_6424099 : Nat := 118140960795 + 6424099 * 2 ^ 59
def prefixEnd_6424099 : Nat := 4983230072969 + 3 ^ 40 * 6424099 * 2
def baseEnd_6424099 : Nat := 3298650559067766416818613

theorem tailTrace_6424099 : CollatzResearch.WordTrace tailWord_6424099 prefixEnd_6424099 3298650559067766416818613 := by
  unfold tailWord_6424099
  simp only [CollatzResearch.WordTrace]
  refine ⟨234306139553593946605835351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156204093035729297737223567 234306139553593946605835351)
  ·
    refine ⟨351459209330390919908753027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234306139553593946605835351 351459209330390919908753027)
    ·
      refine ⟨527188813995586379863129541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351459209330390919908753027 527188813995586379863129541)
      ·
        refine ⟨98847902624172446224336789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 527188813995586379863129541 98847902624172446224336789)
        ·
          refine ⟨4633495435508083416765787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98847902624172446224336789 4633495435508083416765787)
          ·
            refine ⟨6950243153262125125148681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4633495435508083416765787 6950243153262125125148681)
            ·
              refine ⟨5212682364946593843861511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6950243153262125125148681 5212682364946593843861511)
              ·
                refine ⟨7819023547419890765792267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5212682364946593843861511 7819023547419890765792267)
                ·
                  refine ⟨11728535321129836148688401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7819023547419890765792267 11728535321129836148688401)
                  ·
                    refine ⟨8796401490847377111516301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11728535321129836148688401 8796401490847377111516301)
                    ·
                      refine ⟨3298650559067766416818613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8796401490847377111516301 3298650559067766416818613)
                      ·
                        rfl

theorem cell23_6424099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 2, 1, 1, 2, 3].length) (baseStart_6424099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424099 prefixEnd_6424099 := by exact prefixLift 6424099
  have htrace : WordTrace (prefixWord ++ tailWord_6424099) baseStart_6424099 baseEnd_6424099 := by
    simpa [prefixWord, tailWord_6424099, baseEnd_6424099] using wordTrace_append hprefix tailTrace_6424099
  have hstable : (prefixWord ++ tailWord_6424099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424099).length < 2 ^ (prefixWord ++ tailWord_6424099).sum := by decide
  have hdescent : baseEnd_6424099 < baseStart_6424099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424201 : List Nat := [1, 2, 1, 1, 4, 1, 2, 1, 2, 8]
def baseStart_6424201 : Nat := 118140960795 + 6424201 * 2 ^ 59
def prefixEnd_6424201 : Nat := 4983230072969 + 3 ^ 40 * 6424201 * 2
def baseEnd_6424201 : Nat := 1099567644698175005914381

theorem tailTrace_6424201 : CollatzResearch.WordTrace tailWord_6424201 prefixEnd_6424201 1099567644698175005914381 := by
  unfold tailWord_6424201
  simp only [CollatzResearch.WordTrace]
  refine ⟨234309859799224418026048457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156206573199482945350698971 234309859799224418026048457)
  ·
    refine ⟨175732394849418313519536343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234309859799224418026048457 175732394849418313519536343)
    ·
      refine ⟨263598592274127470279304515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175732394849418313519536343 263598592274127470279304515)
      ·
        refine ⟨395397888411191205418956773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263598592274127470279304515 395397888411191205418956773)
        ·
          refine ⟨74137104077098351016054395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 395397888411191205418956773 74137104077098351016054395)
          ·
            refine ⟨111205656115647526524081593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74137104077098351016054395 111205656115647526524081593)
            ·
              refine ⟨83404242086735644893061195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111205656115647526524081593 83404242086735644893061195)
              ·
                refine ⟨125106363130103467339591793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83404242086735644893061195 125106363130103467339591793)
                ·
                  refine ⟨93829772347577600504693845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 125106363130103467339591793 93829772347577600504693845)
                  ·
                    refine ⟨1099567644698175005914381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 93829772347577600504693845 1099567644698175005914381)
                    ·
                      rfl

theorem cell23_6424201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 8].length) (baseStart_6424201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424201 prefixEnd_6424201 := by exact prefixLift 6424201
  have htrace : WordTrace (prefixWord ++ tailWord_6424201) baseStart_6424201 baseEnd_6424201 := by
    simpa [prefixWord, tailWord_6424201, baseEnd_6424201] using wordTrace_append hprefix tailTrace_6424201
  have hstable : (prefixWord ++ tailWord_6424201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424201).length < 2 ^ (prefixWord ++ tailWord_6424201).sum := by decide
  have hdescent : baseEnd_6424201 < baseStart_6424201 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424211 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 5]
def baseStart_6424211 : Nat := 118140960795 + 6424211 * 2 ^ 59
def prefixEnd_6424211 : Nat := 4983230072969 + 3 ^ 40 * 6424211 * 2
def baseEnd_6424211 : Nat := 3298708068901069978618097

theorem tailTrace_6424211 : CollatzResearch.WordTrace tailWord_6424211 prefixEnd_6424211 3298708068901069978618097 := by
  unfold tailWord_6424211
  simp only [CollatzResearch.WordTrace]
  refine ⟨234310224529188189733912487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156206816352792126489274991 234310224529188189733912487)
  ·
    refine ⟨351465336793782284600868731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 234310224529188189733912487 351465336793782284600868731)
    ·
      refine ⟨527198005190673426901303097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 351465336793782284600868731 527198005190673426901303097)
      ·
        refine ⟨395398503893005070175977323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 527198005190673426901303097 395398503893005070175977323)
        ·
          refine ⟨593097755839507605263965985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395398503893005070175977323 593097755839507605263965985)
          ·
            refine ⟨444823316879630703947974489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593097755839507605263965985 444823316879630703947974489)
            ·
              refine ⟨333617487659723027960980867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444823316879630703947974489 333617487659723027960980867)
              ·
                refine ⟨500426231489584541941471301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333617487659723027960980867 500426231489584541941471301)
                ·
                  refine ⟨93829918404297101614025869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 500426231489584541941471301 93829918404297101614025869)
                  ·
                    refine ⟨35186219401611413105259701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 93829918404297101614025869 35186219401611413105259701)
                    ·
                      refine ⟨3298708068901069978618097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35186219401611413105259701 3298708068901069978618097)
                      ·
                        rfl

theorem cell23_6424211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_6424211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424211 prefixEnd_6424211 := by exact prefixLift 6424211
  have htrace : WordTrace (prefixWord ++ tailWord_6424211) baseStart_6424211 baseEnd_6424211 := by
    simpa [prefixWord, tailWord_6424211, baseEnd_6424211] using wordTrace_append hprefix tailTrace_6424211
  have hstable : (prefixWord ++ tailWord_6424211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424211).length < 2 ^ (prefixWord ++ tailWord_6424211).sum := by decide
  have hdescent : baseEnd_6424211 < baseStart_6424211 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424225 : List Nat := [1, 2, 3, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_6424225 : Nat := 118140960795 + 6424225 * 2 ^ 59
def prefixEnd_6424225 : Nat := 4983230072969 + 3 ^ 40 * 6424225 * 2
def baseEnd_6424225 : Nat := 3298715257630232923843033

theorem tailTrace_6424225 : CollatzResearch.WordTrace tailWord_6424225 prefixEnd_6424225 3298715257630232923843033 := by
  unfold tailWord_6424225
  simp only [CollatzResearch.WordTrace]
  refine ⟨234310735151137470124922129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 156207156767424980083281419 234310735151137470124922129)
  ·
    refine ⟨175733051363353102593691597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 234310735151137470124922129 175733051363353102593691597)
    ·
      refine ⟨65899894261257413472634349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175733051363353102593691597 65899894261257413472634349)
      ·
        refine ⟨24712460347971530052237881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65899894261257413472634349 24712460347971530052237881)
        ·
          refine ⟨18534345260978647539178411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24712460347971530052237881 18534345260978647539178411)
          ·
            refine ⟨27801517891467971308767617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18534345260978647539178411 27801517891467971308767617)
            ·
              refine ⟨20851138418600978481575713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27801517891467971308767617 20851138418600978481575713)
              ·
                refine ⟨15638353813950733861181785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20851138418600978481575713 15638353813950733861181785)
                ·
                  refine ⟨11728765360463050395886339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15638353813950733861181785 11728765360463050395886339)
                  ·
                    refine ⟨17593148040694575593829509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11728765360463050395886339 17593148040694575593829509)
                    ·
                      refine ⟨3298715257630232923843033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17593148040694575593829509 3298715257630232923843033)
                      ·
                        rfl

theorem cell23_6424225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_6424225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424225 prefixEnd_6424225 := by exact prefixLift 6424225
  have htrace : WordTrace (prefixWord ++ tailWord_6424225) baseStart_6424225 baseEnd_6424225 := by
    simpa [prefixWord, tailWord_6424225, baseEnd_6424225] using wordTrace_append hprefix tailTrace_6424225
  have hstable : (prefixWord ++ tailWord_6424225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424225).length < 2 ^ (prefixWord ++ tailWord_6424225).sum := by decide
  have hdescent : baseEnd_6424225 < baseStart_6424225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424226 : List Nat := [3, 3, 1, 4, 1, 2, 2, 2, 5]
def baseStart_6424226 : Nat := 118140960795 + 6424226 * 2 ^ 59
def prefixEnd_6424226 : Nat := 4983230072969 + 3 ^ 40 * 6424226 * 2
def baseEnd_6424226 : Nat := 366523974567876379992281

theorem tailTrace_6424226 : CollatzResearch.WordTrace tailWord_6424226 prefixEnd_6424226 366523974567876379992281 := by
  unfold tailWord_6424226
  simp only [CollatzResearch.WordTrace]
  refine ⟨58577692906033461823927133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 156207181082755898197139021 58577692906033461823927133)
  ·
    refine ⟨21966634839762548183972675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58577692906033461823927133 21966634839762548183972675)
    ·
      refine ⟨32949952259643822275959013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21966634839762548183972675 32949952259643822275959013)
      ·
        refine ⟨6178116048683216676742315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32949952259643822275959013 6178116048683216676742315)
        ·
          refine ⟨9267174073024825015113473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6178116048683216676742315 9267174073024825015113473)
          ·
            refine ⟨6950380554768618761335105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9267174073024825015113473 6950380554768618761335105)
            ·
              refine ⟨5212785416076464071001329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6950380554768618761335105 5212785416076464071001329)
              ·
                refine ⟨3909589062057348053250997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5212785416076464071001329 3909589062057348053250997)
                ·
                  refine ⟨366523974567876379992281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3909589062057348053250997 366523974567876379992281)
                  ·
                    rfl

theorem cell23_6424226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 2, 5].length) (baseStart_6424226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424226 prefixEnd_6424226 := by exact prefixLift 6424226
  have htrace : WordTrace (prefixWord ++ tailWord_6424226) baseStart_6424226 baseEnd_6424226 := by
    simpa [prefixWord, tailWord_6424226, baseEnd_6424226] using wordTrace_append hprefix tailTrace_6424226
  have hstable : (prefixWord ++ tailWord_6424226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424226).length < 2 ^ (prefixWord ++ tailWord_6424226).sum := by decide
  have hdescent : baseEnd_6424226 < baseStart_6424226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424292 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 3, 1, 3]
def baseStart_6424292 : Nat := 118140960795 + 6424292 * 2 ^ 59
def prefixEnd_6424292 : Nat := 4983230072969 + 3 ^ 40 * 6424292 * 2
def baseEnd_6424292 : Nat := 3298749660834084161705225

theorem tailTrace_6424292 : CollatzResearch.WordTrace tailWord_6424292 prefixEnd_6424292 3298749660834084161705225 := by
  unfold tailWord_6424292
  simp only [CollatzResearch.WordTrace]
  refine ⟨117156589420947370283805565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156208785894596493711740753 117156589420947370283805565)
  ·
    refine ⟨43933721032855263856427087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117156589420947370283805565 43933721032855263856427087)
    ·
      refine ⟨65900581549282895784640631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43933721032855263856427087 65900581549282895784640631)
      ·
        refine ⟨98850872323924343676960947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65900581549282895784640631 98850872323924343676960947)
        ·
          refine ⟨148276308485886515515441421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98850872323924343676960947 148276308485886515515441421)
          ·
            refine ⟨55603615682207443318290533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148276308485886515515441421 55603615682207443318290533)
            ·
              refine ⟨10425677940413895622179475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55603615682207443318290533 10425677940413895622179475)
              ·
                refine ⟨15638516910620843433269213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10425677940413895622179475 15638516910620843433269213)
                ·
                  refine ⟨5864443841482816287475955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15638516910620843433269213 5864443841482816287475955)
                  ·
                    refine ⟨8796665762224224431213933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5864443841482816287475955 8796665762224224431213933)
                    ·
                      refine ⟨3298749660834084161705225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8796665762224224431213933 3298749660834084161705225)
                      ·
                        rfl

theorem cell23_6424292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_6424292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424292 prefixEnd_6424292 := by exact prefixLift 6424292
  have htrace : WordTrace (prefixWord ++ tailWord_6424292) baseStart_6424292 baseEnd_6424292 := by
    simpa [prefixWord, tailWord_6424292, baseEnd_6424292] using wordTrace_append hprefix tailTrace_6424292
  have hstable : (prefixWord ++ tailWord_6424292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424292).length < 2 ^ (prefixWord ++ tailWord_6424292).sum := by decide
  have hdescent : baseEnd_6424292 < baseStart_6424292 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6424332 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 5, 2, 2]
def baseStart_6424332 : Nat := 118140960795 + 6424332 * 2 ^ 59
def prefixEnd_6424332 : Nat := 4983230072969 + 3 ^ 40 * 6424332 * 2
def baseEnd_6424332 : Nat := 3298770200060264005205041

theorem tailTrace_6424332 : CollatzResearch.WordTrace tailWord_6424332 prefixEnd_6424332 3298770200060264005205041 := by
  unfold tailWord_6424332
  simp only [CollatzResearch.WordTrace]
  refine ⟨117157318880874913699533625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 156209758507833218266044833 117157318880874913699533625)
  ·
    refine ⟨87867989160656185274650219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117157318880874913699533625 87867989160656185274650219)
    ·
      refine ⟨131801983740984277911975329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87867989160656185274650219 131801983740984277911975329)
      ·
        refine ⟨98851487805738208433981497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131801983740984277911975329 98851487805738208433981497)
        ·
          refine ⟨74138615854303656325486123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98851487805738208433981497 74138615854303656325486123)
          ·
            refine ⟨111207923781455484488229185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74138615854303656325486123 111207923781455484488229185)
            ·
              refine ⟨83405942836091613366171889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111207923781455484488229185 83405942836091613366171889)
              ·
                refine ⟨62554457127068710024628917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83405942836091613366171889 62554457127068710024628917)
                ·
                  refine ⟨5864480355662691564808961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62554457127068710024628917 5864480355662691564808961)
                  ·
                    refine ⟨4398360266747018673606721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5864480355662691564808961 4398360266747018673606721)
                    ·
                      refine ⟨3298770200060264005205041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4398360266747018673606721 3298770200060264005205041)
                      ·
                        rfl

theorem cell23_6424332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_6424332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6424332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6424332 prefixEnd_6424332 := by exact prefixLift 6424332
  have htrace : WordTrace (prefixWord ++ tailWord_6424332) baseStart_6424332 baseEnd_6424332 := by
    simpa [prefixWord, tailWord_6424332, baseEnd_6424332] using wordTrace_append hprefix tailTrace_6424332
  have hstable : (prefixWord ++ tailWord_6424332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6424332).length < 2 ^ (prefixWord ++ tailWord_6424332).sum := by decide
  have hdescent : baseEnd_6424332 < baseStart_6424332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6424332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
