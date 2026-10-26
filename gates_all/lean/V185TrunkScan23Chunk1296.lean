import V185TrunkScan23Chunk1295

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7676090 : List Nat := [3, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2]
def baseStart_7676090 : Nat := 118140960795 + 7676090 * 2 ^ 59
def prefixEnd_7676090 : Nat := 4983230072969 + 3 ^ 40 * 7676090 * 2
def baseEnd_7676090 : Nat := 3941523717170977496273311

theorem tailTrace_7676090 : CollatzResearch.WordTrace tailWord_7676090 prefixEnd_7676090 3941523717170977496273311 := by
  unfold tailWord_7676090
  simp only [CollatzResearch.WordTrace]
  refine ⟨69992500690211094161328431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186646668507229584430209149 69992500690211094161328431)
  ·
    refine ⟨104988751035316641241992647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69992500690211094161328431 104988751035316641241992647)
    ·
      refine ⟨157483126552974961862988971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104988751035316641241992647 157483126552974961862988971)
      ·
        refine ⟨236224689829462442794483457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157483126552974961862988971 236224689829462442794483457)
        ·
          refine ⟨177168517372096832095862593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236224689829462442794483457 177168517372096832095862593)
          ·
            refine ⟨132876388029072624071896945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177168517372096832095862593 132876388029072624071896945)
            ·
              refine ⟨99657291021804468053922709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132876388029072624071896945 99657291021804468053922709)
              ·
                refine ⟨4671435516647084440027627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99657291021804468053922709 4671435516647084440027627)
                ·
                  refine ⟨7007153274970626660041441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671435516647084440027627 7007153274970626660041441)
                  ·
                    refine ⟨5255364956227969995031081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7007153274970626660041441 5255364956227969995031081)
                    ·
                      refine ⟨3941523717170977496273311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255364956227969995031081 3941523717170977496273311)
                      ·
                        rfl

theorem cell23_7676090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2].length) (baseStart_7676090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676090 prefixEnd_7676090 := by exact prefixLift 7676090
  have htrace : WordTrace (prefixWord ++ tailWord_7676090) baseStart_7676090 baseEnd_7676090 := by
    simpa [prefixWord, tailWord_7676090, baseEnd_7676090] using wordTrace_append hprefix tailTrace_7676090
  have hstable : (prefixWord ++ tailWord_7676090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676090).length < 2 ^ (prefixWord ++ tailWord_7676090).sum := by decide
  have hdescent : baseEnd_7676090 < baseStart_7676090 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676100 : List Nat := [2, 3, 3, 1, 2, 1, 4, 1, 2, 4]
def baseStart_7676100 : Nat := 118140960795 + 7676100 * 2 ^ 59
def prefixEnd_7676100 : Nat := 4983230072969 + 3 ^ 40 * 7676100 * 2
def baseEnd_7676100 : Nat := 1313842950659174152382755

theorem tailTrace_7676100 : CollatzResearch.WordTrace tailWord_7676100 prefixEnd_7676100 1313842950659174152382755 := by
  unfold tailWord_7676100
  simp only [CollatzResearch.WordTrace]
  refine ⟨139985183745404074176588877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186646911660538765568785169 139985183745404074176588877)
  ·
    refine ⟨52494443904526527816220829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139985183745404074176588877 52494443904526527816220829)
    ·
      refine ⟨19685416464197447931082811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52494443904526527816220829 19685416464197447931082811)
      ·
        refine ⟨29528124696296171896624217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19685416464197447931082811 29528124696296171896624217)
        ·
          refine ⟨22146093522222128922468163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29528124696296171896624217 22146093522222128922468163)
          ·
            refine ⟨33219140283333193383702245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22146093522222128922468163 33219140283333193383702245)
            ·
              refine ⟨6228588803124973759444171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33219140283333193383702245 6228588803124973759444171)
              ·
                refine ⟨9342883204687460639166257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6228588803124973759444171 9342883204687460639166257)
                ·
                  refine ⟨7007162403515595479374693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9342883204687460639166257 7007162403515595479374693)
                  ·
                    refine ⟨1313842950659174152382755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7007162403515595479374693 1313842950659174152382755)
                    ·
                      rfl

theorem cell23_7676100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_7676100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676100 prefixEnd_7676100 := by exact prefixLift 7676100
  have htrace : WordTrace (prefixWord ++ tailWord_7676100) baseStart_7676100 baseEnd_7676100 := by
    simpa [prefixWord, tailWord_7676100, baseEnd_7676100] using wordTrace_append hprefix tailTrace_7676100
  have hstable : (prefixWord ++ tailWord_7676100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676100).length < 2 ^ (prefixWord ++ tailWord_7676100).sum := by decide
  have hdescent : baseEnd_7676100 < baseStart_7676100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676106 : List Nat := [3, 1, 2, 1, 3, 1, 2, 3, 1, 3, 3]
def baseStart_7676106 : Nat := 118140960795 + 7676106 * 2 ^ 59
def prefixEnd_7676106 : Nat := 4983230072969 + 3 ^ 40 * 7676106 * 2
def baseEnd_7676106 : Nat := 3941531932861449433673237

theorem tailTrace_7676106 : CollatzResearch.WordTrace tailWord_7676106 prefixEnd_7676106 3941531932861449433673237 := by
  unfold tailWord_7676106
  simp only [CollatzResearch.WordTrace]
  refine ⟨69992646582196602844474043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186647057552524274251930781 69992646582196602844474043)
  ·
    refine ⟨104988969873294904266711065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69992646582196602844474043 104988969873294904266711065)
    ·
      refine ⟨78741727404971178200033299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104988969873294904266711065 78741727404971178200033299)
      ·
        refine ⟨118112591107456767300049949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78741727404971178200033299 118112591107456767300049949)
        ·
          refine ⟨44292221665296287737518731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118112591107456767300049949 44292221665296287737518731)
          ·
            refine ⟨66438332497944431606278097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44292221665296287737518731 66438332497944431606278097)
            ·
              refine ⟨49828749373458323704708573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66438332497944431606278097 49828749373458323704708573)
              ·
                refine ⟨18685781015046871389265715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49828749373458323704708573 18685781015046871389265715)
                ·
                  refine ⟨28028671522570307083898573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18685781015046871389265715 28028671522570307083898573)
                  ·
                    refine ⟨10510751820963865156461965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28028671522570307083898573 10510751820963865156461965)
                    ·
                      refine ⟨3941531932861449433673237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10510751820963865156461965 3941531932861449433673237)
                      ·
                        rfl

theorem cell23_7676106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_7676106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676106 prefixEnd_7676106 := by exact prefixLift 7676106
  have htrace : WordTrace (prefixWord ++ tailWord_7676106) baseStart_7676106 baseEnd_7676106 := by
    simpa [prefixWord, tailWord_7676106, baseEnd_7676106] using wordTrace_append hprefix tailTrace_7676106
  have hstable : (prefixWord ++ tailWord_7676106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676106).length < 2 ^ (prefixWord ++ tailWord_7676106).sum := by decide
  have hdescent : baseEnd_7676106 < baseStart_7676106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676110 : List Nat := [4, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3]
def baseStart_7676110 : Nat := 118140960795 + 7676110 * 2 ^ 59
def prefixEnd_7676110 : Nat := 4983230072969 + 3 ^ 40 * 7676110 * 2
def baseEnd_7676110 : Nat := 3941533986784067418023219

theorem tailTrace_7676110 : CollatzResearch.WordTrace tailWord_7676110 prefixEnd_7676110 3941533986784067418023219 := by
  unfold tailWord_7676110
  simp only [CollatzResearch.WordTrace]
  refine ⟨34996341527596490007630223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186647154813847946707361189 34996341527596490007630223)
  ·
    refine ⟨52494512291394735011445335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34996341527596490007630223 52494512291394735011445335)
    ·
      refine ⟨78741768437092102517168003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52494512291394735011445335 78741768437092102517168003)
      ·
        refine ⟨118112652655638153775752005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78741768437092102517168003 118112652655638153775752005)
        ·
          refine ⟨22146122372932153832953501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118112652655638153775752005 22146122372932153832953501)
          ·
            refine ⟨8304795889849557687357563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22146122372932153832953501 8304795889849557687357563)
            ·
              refine ⟨12457193834774336531036345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8304795889849557687357563 12457193834774336531036345)
              ·
                refine ⟨9342895376080752398277259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12457193834774336531036345 9342895376080752398277259)
                ·
                  refine ⟨14014343064121128597415889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9342895376080752398277259 14014343064121128597415889)
                  ·
                    refine ⟨10510757298090846448061917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14014343064121128597415889 10510757298090846448061917)
                    ·
                      refine ⟨3941533986784067418023219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10510757298090846448061917 3941533986784067418023219)
                      ·
                        rfl

theorem cell23_7676110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3].length) (baseStart_7676110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676110 prefixEnd_7676110 := by exact prefixLift 7676110
  have htrace : WordTrace (prefixWord ++ tailWord_7676110) baseStart_7676110 baseEnd_7676110 := by
    simpa [prefixWord, tailWord_7676110, baseEnd_7676110] using wordTrace_append hprefix tailTrace_7676110
  have hstable : (prefixWord ++ tailWord_7676110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676110).length < 2 ^ (prefixWord ++ tailWord_7676110).sum := by decide
  have hdescent : baseEnd_7676110 < baseStart_7676110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676130 : List Nat := [3, 3, 4, 1, 2, 10]
def baseStart_7676130 : Nat := 118140960795 + 7676130 * 2 ^ 59
def prefixEnd_7676130 : Nat := 4983230072969 + 3 ^ 40 * 7676130 * 2
def baseEnd_7676130 : Nat := 16220346734144680410589

theorem tailTrace_7676130 : CollatzResearch.WordTrace tailWord_7676130 prefixEnd_7676130 16220346734144680410589 := by
  unfold tailWord_7676130
  simp only [CollatzResearch.WordTrace]
  refine ⟨69992865420174865869192461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186647641120466308984513229 69992865420174865869192461)
  ·
    refine ⟨26247324532565574700947173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69992865420174865869192461 26247324532565574700947173)
    ·
      refine ⟨4921373349856045256427595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26247324532565574700947173 4921373349856045256427595)
      ·
        refine ⟨7382060024784067884641393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4921373349856045256427595 7382060024784067884641393)
        ·
          refine ⟨5536545018588050913481045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7382060024784067884641393 5536545018588050913481045)
          ·
            refine ⟨16220346734144680410589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5536545018588050913481045 16220346734144680410589)
            ·
              rfl

theorem cell23_7676130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 10].length) (baseStart_7676130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676130 prefixEnd_7676130 := by exact prefixLift 7676130
  have htrace : WordTrace (prefixWord ++ tailWord_7676130) baseStart_7676130 baseEnd_7676130 := by
    simpa [prefixWord, tailWord_7676130, baseEnd_7676130] using wordTrace_append hprefix tailTrace_7676130
  have hstable : (prefixWord ++ tailWord_7676130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676130).length < 2 ^ (prefixWord ++ tailWord_7676130).sum := by decide
  have hdescent : baseEnd_7676130 < baseStart_7676130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676139 : List Nat := [1, 1, 1, 1, 2, 5, 2, 2, 2, 6]
def baseStart_7676139 : Nat := 118140960795 + 7676139 * 2 ^ 59
def prefixEnd_7676139 : Nat := 4983230072969 + 3 ^ 40 * 7676139 * 2
def baseEnd_7676139 : Nat := 1313849625907682601520195

theorem tailTrace_7676139 : CollatzResearch.WordTrace tailWord_7676139 prefixEnd_7676139 1313849625907682601520195 := by
  unfold tailWord_7676139
  simp only [CollatzResearch.WordTrace]
  refine ⟨279971789937666858013847471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186647859958444572009231647 279971789937666858013847471)
  ·
    refine ⟨419957684906500287020771207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279971789937666858013847471 419957684906500287020771207)
    ·
      refine ⟨629936527359750430531156811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419957684906500287020771207 629936527359750430531156811)
      ·
        refine ⟨944904791039625645796735217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629936527359750430531156811 944904791039625645796735217)
        ·
          refine ⟨708678593279719234347551413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 944904791039625645796735217 708678593279719234347551413)
          ·
            refine ⟨66438618119973678220082945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 708678593279719234347551413 66438618119973678220082945)
            ·
              refine ⟨49828963589980258665062209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66438618119973678220082945 49828963589980258665062209)
              ·
                refine ⟨37371722692485193998796657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49828963589980258665062209 37371722692485193998796657)
                ·
                  refine ⟨28028792019363895499097493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37371722692485193998796657 28028792019363895499097493)
                  ·
                    refine ⟨1313849625907682601520195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28028792019363895499097493 1313849625907682601520195)
                    ·
                      rfl

theorem cell23_7676139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 2, 2, 2, 6].length) (baseStart_7676139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676139 prefixEnd_7676139 := by exact prefixLift 7676139
  have htrace : WordTrace (prefixWord ++ tailWord_7676139) baseStart_7676139 baseEnd_7676139 := by
    simpa [prefixWord, tailWord_7676139, baseEnd_7676139] using wordTrace_append hprefix tailTrace_7676139
  have hstable : (prefixWord ++ tailWord_7676139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676139).length < 2 ^ (prefixWord ++ tailWord_7676139).sum := by decide
  have hdescent : baseEnd_7676139 < baseStart_7676139 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676141 : List Nat := [1, 5, 1, 2, 3, 2, 2, 2, 1, 2, 2]
def baseStart_7676141 : Nat := 118140960795 + 7676141 * 2 ^ 59
def prefixEnd_7676141 : Nat := 4983230072969 + 3 ^ 40 * 7676141 * 2
def baseEnd_7676141 : Nat := 3941549904684356796735577

theorem tailTrace_7676141 : CollatzResearch.WordTrace tailWord_7676141 prefixEnd_7676141 3941549904684356796735577 := by
  unfold tailWord_7676141
  simp only [CollatzResearch.WordTrace]
  refine ⟨279971862883659612355420277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186647908589106408236946851 279971862883659612355420277)
  ·
    refine ⟨26247362145343088658320651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279971862883659612355420277 26247362145343088658320651)
    ·
      refine ⟨39371043218014632987480977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26247362145343088658320651 39371043218014632987480977)
      ·
        refine ⟨29528282413510974740610733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39371043218014632987480977 29528282413510974740610733)
        ·
          refine ⟨11073105905066615527729025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29528282413510974740610733 11073105905066615527729025)
          ·
            refine ⟨8304829428799961645796769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11073105905066615527729025 8304829428799961645796769)
            ·
              refine ⟨6228622071599971234347577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8304829428799961645796769 6228622071599971234347577)
              ·
                refine ⟨4671466553699978425760683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6228622071599971234347577 4671466553699978425760683)
                ·
                  refine ⟨7007199830549967638641025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671466553699978425760683 7007199830549967638641025)
                  ·
                    refine ⟨5255399872912475728980769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7007199830549967638641025 5255399872912475728980769)
                    ·
                      refine ⟨3941549904684356796735577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255399872912475728980769 3941549904684356796735577)
                      ·
                        rfl

theorem cell23_7676141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_7676141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676141 prefixEnd_7676141 := by exact prefixLift 7676141
  have htrace : WordTrace (prefixWord ++ tailWord_7676141) baseStart_7676141 baseEnd_7676141 := by
    simpa [prefixWord, tailWord_7676141, baseEnd_7676141] using wordTrace_append hprefix tailTrace_7676141
  have hstable : (prefixWord ++ tailWord_7676141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676141).length < 2 ^ (prefixWord ++ tailWord_7676141).sum := by decide
  have hdescent : baseEnd_7676141 < baseStart_7676141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676146 : List Nat := [3, 2, 1, 3, 2, 1, 1, 1, 2, 3, 4]
def baseStart_7676146 : Nat := 118140960795 + 7676146 * 2 ^ 59
def prefixEnd_7676146 : Nat := 4983230072969 + 3 ^ 40 * 7676146 * 2
def baseEnd_7676146 : Nat := 3941552472087629277173053

theorem tailTrace_7676146 : CollatzResearch.WordTrace tailWord_7676146 prefixEnd_7676146 3941552472087629277173053 := by
  unfold tailWord_7676146
  simp only [CollatzResearch.WordTrace]
  refine ⟨69993011312160374552338073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186648030165760998806234861 69993011312160374552338073)
  ·
    refine ⟨52494758484120280914253555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69993011312160374552338073 52494758484120280914253555)
    ·
      refine ⟨78742137726180421371380333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52494758484120280914253555 78742137726180421371380333)
      ·
        refine ⟨29528301647317658014267625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78742137726180421371380333 29528301647317658014267625)
        ·
          refine ⟨22146226235488243510700719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29528301647317658014267625 22146226235488243510700719)
          ·
            refine ⟨33219339353232365266051079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22146226235488243510700719 33219339353232365266051079)
            ·
              refine ⟨49829009029848547899076619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33219339353232365266051079 49829009029848547899076619)
              ·
                refine ⟨74743513544772821848614929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49829009029848547899076619 74743513544772821848614929)
                ·
                  refine ⟨56057635158579616386461197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74743513544772821848614929 56057635158579616386461197)
                  ·
                    refine ⟨21021613184467356144922949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56057635158579616386461197 21021613184467356144922949)
                    ·
                      refine ⟨3941552472087629277173053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21021613184467356144922949 3941552472087629277173053)
                      ·
                        rfl

theorem cell23_7676146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_7676146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676146 prefixEnd_7676146 := by exact prefixLift 7676146
  have htrace : WordTrace (prefixWord ++ tailWord_7676146) baseStart_7676146 baseEnd_7676146 := by
    simpa [prefixWord, tailWord_7676146, baseEnd_7676146] using wordTrace_append hprefix tailTrace_7676146
  have hstable : (prefixWord ++ tailWord_7676146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676146).length < 2 ^ (prefixWord ++ tailWord_7676146).sum := by decide
  have hdescent : baseEnd_7676146 < baseStart_7676146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676156 : List Nat := [2, 2, 2, 1, 4, 2, 1, 1, 2, 6]
def baseStart_7676156 : Nat := 118140960795 + 7676156 * 2 ^ 59
def prefixEnd_7676156 : Nat := 4983230072969 + 3 ^ 40 * 7676156 * 2
def baseEnd_7676156 : Nat := 1313852535631391412682669

theorem tailTrace_7676156 : CollatzResearch.WordTrace tailWord_7676156 prefixEnd_7676156 1313852535631391412682669 := by
  unfold tailWord_7676156
  simp only [CollatzResearch.WordTrace]
  refine ⟨139986204989302634958608161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186648273319070179944810881 139986204989302634958608161)
  ·
    refine ⟨104989653741976976218956121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139986204989302634958608161 104989653741976976218956121)
    ·
      refine ⟨78742240306482732164217091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104989653741976976218956121 78742240306482732164217091)
      ·
        refine ⟨118113360459724098246325637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78742240306482732164217091 118113360459724098246325637)
        ·
          refine ⟨22146255086198268421186057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118113360459724098246325637 22146255086198268421186057)
          ·
            refine ⟨16609691314648701315889543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22146255086198268421186057 16609691314648701315889543)
            ·
              refine ⟨24914536971973051973834315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16609691314648701315889543 24914536971973051973834315)
              ·
                refine ⟨37371805457959577960751473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24914536971973051973834315 37371805457959577960751473)
                ·
                  refine ⟨28028854093469683470563605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37371805457959577960751473 28028854093469683470563605)
                  ·
                    refine ⟨1313852535631391412682669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28028854093469683470563605 1313852535631391412682669)
                    ·
                      rfl

theorem cell23_7676156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_7676156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676156 prefixEnd_7676156 := by exact prefixLift 7676156
  have htrace : WordTrace (prefixWord ++ tailWord_7676156) baseStart_7676156 baseEnd_7676156 := by
    simpa [prefixWord, tailWord_7676156, baseEnd_7676156] using wordTrace_append hprefix tailTrace_7676156
  have hstable : (prefixWord ++ tailWord_7676156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676156).length < 2 ^ (prefixWord ++ tailWord_7676156).sum := by decide
  have hdescent : baseEnd_7676156 < baseStart_7676156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676163 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 1, 4, 2]
def baseStart_7676163 : Nat := 118140960795 + 7676163 * 2 ^ 59
def prefixEnd_7676163 : Nat := 4983230072969 + 3 ^ 40 * 7676163 * 2
def baseEnd_7676163 : Nat := 3941561201258755710660475

theorem tailTrace_7676163 : CollatzResearch.WordTrace tailWord_7676163 prefixEnd_7676163 3941561201258755710660475 := by
  unfold tailWord_7676163
  simp only [CollatzResearch.WordTrace]
  refine ⟨279972665289579910112721143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186648443526386606741814095 279972665289579910112721143)
  ·
    refine ⟨419958997934369865169081715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279972665289579910112721143 419958997934369865169081715)
    ·
      refine ⟨629938496901554797753622573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419958997934369865169081715 629938496901554797753622573)
      ·
        refine ⟨236226936338083049157608465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 629938496901554797753622573 236226936338083049157608465)
        ·
          refine ⟨177170202253562286868206349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236226936338083049157608465 177170202253562286868206349)
          ·
            refine ⟨66438825845085857575577381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177170202253562286868206349 66438825845085857575577381)
            ·
              refine ⟨12457279845953598295420759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66438825845085857575577381 12457279845953598295420759)
              ·
                refine ⟨18685919768930397443131139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12457279845953598295420759 18685919768930397443131139)
                ·
                  refine ⟨28028879653395596164696709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18685919768930397443131139 28028879653395596164696709)
                  ·
                    refine ⟨5255414935011674280880633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28028879653395596164696709 5255414935011674280880633)
                    ·
                      refine ⟨3941561201258755710660475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255414935011674280880633 3941561201258755710660475)
                      ·
                        rfl

theorem cell23_7676163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 4, 2].length) (baseStart_7676163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676163 prefixEnd_7676163 := by exact prefixLift 7676163
  have htrace : WordTrace (prefixWord ++ tailWord_7676163) baseStart_7676163 baseEnd_7676163 := by
    simpa [prefixWord, tailWord_7676163, baseEnd_7676163] using wordTrace_append hprefix tailTrace_7676163
  have hstable : (prefixWord ++ tailWord_7676163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676163).length < 2 ^ (prefixWord ++ tailWord_7676163).sum := by decide
  have hdescent : baseEnd_7676163 < baseStart_7676163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676169 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 9]
def baseStart_7676169 : Nat := 118140960795 + 7676169 * 2 ^ 59
def prefixEnd_7676169 : Nat := 4983230072969 + 3 ^ 40 * 7676169 * 2
def baseEnd_7676169 : Nat := 437951586904742520798383

theorem tailTrace_7676169 : CollatzResearch.WordTrace tailWord_7676169 prefixEnd_7676169 437951586904742520798383 := by
  unfold tailWord_7676169
  simp only [CollatzResearch.WordTrace]
  refine ⟨279972884127558173137439561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186648589418372115424959707 279972884127558173137439561)
  ·
    refine ⟨209979663095668629853079671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279972884127558173137439561 209979663095668629853079671)
    ·
      refine ⟨314969494643502944779619507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209979663095668629853079671 314969494643502944779619507)
      ·
        refine ⟨472454241965254417169429261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314969494643502944779619507 472454241965254417169429261)
        ·
          refine ⟨177170340736970406438535973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472454241965254417169429261 177170340736970406438535973)
          ·
            refine ⟨33219438888181951207225495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177170340736970406438535973 33219438888181951207225495)
            ·
              refine ⟨49829158332272926810838243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33219438888181951207225495 49829158332272926810838243)
              ·
                refine ⟨74743737498409390216257365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49829158332272926810838243 74743737498409390216257365)
                ·
                  refine ⟨437951586904742520798383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74743737498409390216257365 437951586904742520798383)
                  ·
                    rfl

theorem cell23_7676169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 9].length) (baseStart_7676169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676169 prefixEnd_7676169 := by exact prefixLift 7676169
  have htrace : WordTrace (prefixWord ++ tailWord_7676169) baseStart_7676169 baseEnd_7676169 := by
    simpa [prefixWord, tailWord_7676169, baseEnd_7676169] using wordTrace_append hprefix tailTrace_7676169
  have hstable : (prefixWord ++ tailWord_7676169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676169).length < 2 ^ (prefixWord ++ tailWord_7676169).sum := by decide
  have hdescent : baseEnd_7676169 < baseStart_7676169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676236 : List Nat := [2, 2, 1, 3, 2, 1, 1, 3, 1, 3, 4]
def baseStart_7676236 : Nat := 118140960795 + 7676236 * 2 ^ 59
def prefixEnd_7676236 : Nat := 4983230072969 + 3 ^ 40 * 7676236 * 2
def baseEnd_7676236 : Nat := 3941598685346533925047639

theorem tailTrace_7676236 : CollatzResearch.WordTrace tailWord_7676236 prefixEnd_7676236 3941598685346533925047639 := by
  unfold tailWord_7676236
  simp only [CollatzResearch.WordTrace]
  refine ⟨139987663909157721790064281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186650218545543629053419041 139987663909157721790064281)
  ·
    refine ⟨104990747931868291342548211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139987663909157721790064281 104990747931868291342548211)
    ·
      refine ⟨157486121897802437013822317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104990747931868291342548211 157486121897802437013822317)
      ·
        refine ⟨59057295711675913880183369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157486121897802437013822317 59057295711675913880183369)
        ·
          refine ⟨44292971783756935410137527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59057295711675913880183369 44292971783756935410137527)
          ·
            refine ⟨66439457675635403115206291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44292971783756935410137527 66439457675635403115206291)
            ·
              refine ⟨99659186513453104672809437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66439457675635403115206291 99659186513453104672809437)
              ·
                refine ⟨37372194942544914252303539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99659186513453104672809437 37372194942544914252303539)
                ·
                  refine ⟨56058292413817371378455309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37372194942544914252303539 56058292413817371378455309)
                  ·
                    refine ⟨21021859655181514266920741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56058292413817371378455309 21021859655181514266920741)
                    ·
                      refine ⟨3941598685346533925047639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21021859655181514266920741 3941598685346533925047639)
                      ·
                        rfl

theorem cell23_7676236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_7676236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676236 prefixEnd_7676236 := by exact prefixLift 7676236
  have htrace : WordTrace (prefixWord ++ tailWord_7676236) baseStart_7676236 baseEnd_7676236 := by
    simpa [prefixWord, tailWord_7676236, baseEnd_7676236] using wordTrace_append hprefix tailTrace_7676236
  have hstable : (prefixWord ++ tailWord_7676236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676236).length < 2 ^ (prefixWord ++ tailWord_7676236).sum := by decide
  have hdescent : baseEnd_7676236 < baseStart_7676236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676314 : List Nat := [3, 1, 1, 4, 1, 4, 2, 2, 1, 4]
def baseStart_7676314 : Nat := 118140960795 + 7676314 * 2 ^ 59
def prefixEnd_7676314 : Nat := 4983230072969 + 3 ^ 40 * 7676314 * 2
def baseEnd_7676314 : Nat := 1313879578945861539957427

theorem tailTrace_7676314 : CollatzResearch.WordTrace tailWord_7676314 prefixEnd_7676314 1313879578945861539957427 := by
  unfold tailWord_7676314
  simp only [CollatzResearch.WordTrace]
  refine ⟨69994543178008215725366999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186652115141355241934311997 69994543178008215725366999)
  ·
    refine ⟨104991814767012323588050499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69994543178008215725366999 104991814767012323588050499)
    ·
      refine ⟨157487722150518485382075749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104991814767012323588050499 157487722150518485382075749)
      ·
        refine ⟨29528947903222216009139203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157487722150518485382075749 29528947903222216009139203)
        ·
          refine ⟨44293421854833324013708805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29528947903222216009139203 44293421854833324013708805)
          ·
            refine ⟨8305016597781248252570401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44293421854833324013708805 8305016597781248252570401)
            ·
              refine ⟨6228762448335936189427801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8305016597781248252570401 6228762448335936189427801)
              ·
                refine ⟨4671571836251952142070851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6228762448335936189427801 4671571836251952142070851)
                ·
                  refine ⟨7007357754377928213106277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671571836251952142070851 7007357754377928213106277)
                  ·
                    refine ⟨1313879578945861539957427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7007357754377928213106277 1313879578945861539957427)
                    ·
                      rfl

theorem cell23_7676314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 2, 1, 4].length) (baseStart_7676314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676314 prefixEnd_7676314 := by exact prefixLift 7676314
  have htrace : WordTrace (prefixWord ++ tailWord_7676314) baseStart_7676314 baseEnd_7676314 := by
    simpa [prefixWord, tailWord_7676314, baseEnd_7676314] using wordTrace_append hprefix tailTrace_7676314
  have hstable : (prefixWord ++ tailWord_7676314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676314).length < 2 ^ (prefixWord ++ tailWord_7676314).sum := by decide
  have hdescent : baseEnd_7676314 < baseStart_7676314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676343 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 4]
def baseStart_7676343 : Nat := 118140960795 + 7676343 * 2 ^ 59
def prefixEnd_7676343 : Nat := 4983230072969 + 3 ^ 40 * 7676343 * 2
def baseEnd_7676343 : Nat := 3941653627776565006409647

theorem tailTrace_7676343 : CollatzResearch.WordTrace tailWord_7676343 prefixEnd_7676343 3941653627776565006409647 := by
  unfold tailWord_7676343
  simp only [CollatzResearch.WordTrace]
  refine ⟨279979230428927800854273683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186652820285951867236182455 279979230428927800854273683)
  ·
    refine ⟨419968845643391701281410525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279979230428927800854273683 419968845643391701281410525)
    ·
      refine ⟨157488317116271887980528947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419968845643391701281410525 157488317116271887980528947)
      ·
        refine ⟨236232475674407831970793421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157488317116271887980528947 236232475674407831970793421)
        ·
          refine ⟨88587178377902936989047533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236232475674407831970793421 88587178377902936989047533)
          ·
            refine ⟨33220191891713601370892825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88587178377902936989047533 33220191891713601370892825)
            ·
              refine ⟨24915143918785201028169619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33220191891713601370892825 24915143918785201028169619)
              ·
                refine ⟨37372715878177801542254429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24915143918785201028169619 37372715878177801542254429)
                ·
                  refine ⟨14014768454316675578345411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37372715878177801542254429 14014768454316675578345411)
                  ·
                    refine ⟨21022152681475013367518117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14014768454316675578345411 21022152681475013367518117)
                    ·
                      refine ⟨3941653627776565006409647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21022152681475013367518117 3941653627776565006409647)
                      ·
                        rfl

theorem cell23_7676343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_7676343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676343 prefixEnd_7676343 := by exact prefixLift 7676343
  have htrace : WordTrace (prefixWord ++ tailWord_7676343) baseStart_7676343 baseEnd_7676343 := by
    simpa [prefixWord, tailWord_7676343, baseEnd_7676343] using wordTrace_append hprefix tailTrace_7676343
  have hstable : (prefixWord ++ tailWord_7676343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676343).length < 2 ^ (prefixWord ++ tailWord_7676343).sum := by decide
  have hdescent : baseEnd_7676343 < baseStart_7676343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676360 : List Nat := [2, 1, 3, 1, 3, 3, 1, 3, 1, 1, 4]
def baseStart_7676360 : Nat := 118140960795 + 7676360 * 2 ^ 59
def prefixEnd_7676360 : Nat := 4983230072969 + 3 ^ 40 * 7676360 * 2
def baseEnd_7676360 : Nat := 3941662356947691439897069

theorem tailTrace_7676360 : CollatzResearch.WordTrace tailWord_7676360 prefixEnd_7676360 3941662356947691439897069 := by
  unfold tailWord_7676360
  simp only [CollatzResearch.WordTrace]
  refine ⟨139989925234933106378821267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186653233646577475171761689 139989925234933106378821267)
  ·
    refine ⟨209984887852399659568231901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139989925234933106378821267 209984887852399659568231901)
    ·
      refine ⟨78744332944649872338086963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 209984887852399659568231901 78744332944649872338086963)
      ·
        refine ⟨118116499416974808507130445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78744332944649872338086963 118116499416974808507130445)
        ·
          refine ⟨44293687281365553190173917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118116499416974808507130445 44293687281365553190173917)
          ·
            refine ⟨16610132730512082446315219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44293687281365553190173917 16610132730512082446315219)
            ·
              refine ⟨24915199095768123669472829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16610132730512082446315219 24915199095768123669472829)
              ·
                refine ⟨9343199660913046376052311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24915199095768123669472829 9343199660913046376052311)
                ·
                  refine ⟨14014799491369569564078467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9343199660913046376052311 14014799491369569564078467)
                  ·
                    refine ⟨21022199237054354346117701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14014799491369569564078467 21022199237054354346117701)
                    ·
                      refine ⟨3941662356947691439897069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21022199237054354346117701 3941662356947691439897069)
                      ·
                        rfl

theorem cell23_7676360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_7676360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676360 prefixEnd_7676360 := by exact prefixLift 7676360
  have htrace : WordTrace (prefixWord ++ tailWord_7676360) baseStart_7676360 baseEnd_7676360 := by
    simpa [prefixWord, tailWord_7676360, baseEnd_7676360] using wordTrace_append hprefix tailTrace_7676360
  have hstable : (prefixWord ++ tailWord_7676360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676360).length < 2 ^ (prefixWord ++ tailWord_7676360).sum := by decide
  have hdescent : baseEnd_7676360 < baseStart_7676360 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676376 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 2, 2, 7]
def baseStart_7676376 : Nat := 118140960795 + 7676376 * 2 ^ 59
def prefixEnd_7676376 : Nat := 4983230072969 + 3 ^ 40 * 7676376 * 2
def baseEnd_7676376 : Nat := 3941670572638163377296995

theorem tailTrace_7676376 : CollatzResearch.WordTrace tailWord_7676376 prefixEnd_7676376 3941670572638163377296995 := by
  unfold tailWord_7676376
  simp only [CollatzResearch.WordTrace]
  refine ⟨139990217018904123745112491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186653622691872164993483321 139990217018904123745112491)
  ·
    refine ⟨209985325528356185617668737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139990217018904123745112491 209985325528356185617668737)
    ·
      refine ⟨157488994146267139213251553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209985325528356185617668737 157488994146267139213251553)
      ·
        refine ⟨118116745609700354409938665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157488994146267139213251553 118116745609700354409938665)
        ·
          refine ⟨88587559207275265807453999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118116745609700354409938665 88587559207275265807453999)
          ·
            refine ⟨132881338810912898711180999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88587559207275265807453999 132881338810912898711180999)
            ·
              refine ⟨199322008216369348066771499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132881338810912898711180999 199322008216369348066771499)
              ·
                refine ⟨298983012324554022100157249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199322008216369348066771499 298983012324554022100157249)
                ·
                  refine ⟨224237259243415516575117937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 298983012324554022100157249 224237259243415516575117937)
                  ·
                    refine ⟨168177944432561637431338453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 224237259243415516575117937 168177944432561637431338453)
                    ·
                      refine ⟨3941670572638163377296995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168177944432561637431338453 3941670572638163377296995)
                      ·
                        rfl

theorem cell23_7676376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_7676376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676376 prefixEnd_7676376 := by exact prefixLift 7676376
  have htrace : WordTrace (prefixWord ++ tailWord_7676376) baseStart_7676376 baseEnd_7676376 := by
    simpa [prefixWord, tailWord_7676376, baseEnd_7676376] using wordTrace_append hprefix tailTrace_7676376
  have hstable : (prefixWord ++ tailWord_7676376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676376).length < 2 ^ (prefixWord ++ tailWord_7676376).sum := by decide
  have hdescent : baseEnd_7676376 < baseStart_7676376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676377 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 3, 2, 2]
def baseStart_7676377 : Nat := 118140960795 + 7676377 * 2 ^ 59
def prefixEnd_7676377 : Nat := 4983230072969 + 3 ^ 40 * 7676377 * 2
def baseEnd_7676377 : Nat := 3941671086118817873384491

theorem tailTrace_7676377 : CollatzResearch.WordTrace tailWord_7676377 prefixEnd_7676377 3941671086118817873384491 := by
  unfold tailWord_7676377
  simp only [CollatzResearch.WordTrace]
  refine ⟨279980470510804624661011385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186653647007203083107340923 279980470510804624661011385)
  ·
    refine ⟨209985352883103468495758539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279980470510804624661011385 209985352883103468495758539)
    ·
      refine ⟨314978029324655202743637809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209985352883103468495758539 314978029324655202743637809)
      ·
        refine ⟨236233521993491402057728357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314978029324655202743637809 236233521993491402057728357)
        ·
          refine ⟨44293785373779637885824067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236233521993491402057728357 44293785373779637885824067)
          ·
            refine ⟨66440678060669456828736101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44293785373779637885824067 66440678060669456828736101)
            ·
              refine ⟨12457627136375523155388019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66440678060669456828736101 12457627136375523155388019)
              ·
                refine ⟨18686440704563284733082029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12457627136375523155388019 18686440704563284733082029)
                ·
                  refine ⟨7007415264211231774905761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18686440704563284733082029 7007415264211231774905761)
                  ·
                    refine ⟨5255561448158423831179321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7007415264211231774905761 5255561448158423831179321)
                    ·
                      refine ⟨3941671086118817873384491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255561448158423831179321 3941671086118817873384491)
                      ·
                        rfl

theorem cell23_7676377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 3, 2, 2].length) (baseStart_7676377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676377 prefixEnd_7676377 := by exact prefixLift 7676377
  have htrace : WordTrace (prefixWord ++ tailWord_7676377) baseStart_7676377 baseEnd_7676377 := by
    simpa [prefixWord, tailWord_7676377, baseEnd_7676377] using wordTrace_append hprefix tailTrace_7676377
  have hstable : (prefixWord ++ tailWord_7676377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676377).length < 2 ^ (prefixWord ++ tailWord_7676377).sum := by decide
  have hdescent : baseEnd_7676377 < baseStart_7676377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676387 : List Nat := [1, 1, 1, 6, 4, 1, 1, 1, 1, 6]
def baseStart_7676387 : Nat := 118140960795 + 7676387 * 2 ^ 59
def prefixEnd_7676387 : Nat := 4983230072969 + 3 ^ 40 * 7676387 * 2
def baseEnd_7676387 : Nat := 1313892073641787611419815

theorem tailTrace_7676387 : CollatzResearch.WordTrace tailWord_7676387 prefixEnd_7676387 1313892073641787611419815 := by
  unfold tailWord_7676387
  simp only [CollatzResearch.WordTrace]
  refine ⟨279980835240768396368875415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186653890160512264245916943 279980835240768396368875415)
  ·
    refine ⟨419971252861152594553313123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279980835240768396368875415 419971252861152594553313123)
    ·
      refine ⟨629956879291728891829969685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419971252861152594553313123 629956879291728891829969685)
      ·
        refine ⟨29529228716799791804529829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 629956879291728891829969685 29529228716799791804529829)
        ·
          refine ⟨5536730384399960963349343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29529228716799791804529829 5536730384399960963349343)
          ·
            refine ⟨8305095576599941445024015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5536730384399960963349343 8305095576599941445024015)
            ·
              refine ⟨12457643364899912167536023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8305095576599941445024015 12457643364899912167536023)
              ·
                refine ⟨18686465047349868251304035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12457643364899912167536023 18686465047349868251304035)
                ·
                  refine ⟨28029697571024802376956053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18686465047349868251304035 28029697571024802376956053)
                  ·
                    refine ⟨1313892073641787611419815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28029697571024802376956053 1313892073641787611419815)
                    ·
                      rfl

theorem cell23_7676387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 1, 1, 6].length) (baseStart_7676387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676387 prefixEnd_7676387 := by exact prefixLift 7676387
  have htrace : WordTrace (prefixWord ++ tailWord_7676387) baseStart_7676387 baseEnd_7676387 := by
    simpa [prefixWord, tailWord_7676387, baseEnd_7676387] using wordTrace_append hprefix tailTrace_7676387
  have hstable : (prefixWord ++ tailWord_7676387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676387).length < 2 ^ (prefixWord ++ tailWord_7676387).sum := by decide
  have hdescent : baseEnd_7676387 < baseStart_7676387 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676393 : List Nat := [1, 2, 1, 1, 1, 2, 1, 7, 1, 3, 3]
def baseStart_7676393 : Nat := 118140960795 + 7676393 * 2 ^ 59
def prefixEnd_7676393 : Nat := 4983230072969 + 3 ^ 40 * 7676393 * 2
def baseEnd_7676393 : Nat := 3941679301809289810784417

theorem tailTrace_7676393 : CollatzResearch.WordTrace tailWord_7676393 prefixEnd_7676393 3941679301809289810784417 := by
  unfold tailWord_7676393
  simp only [CollatzResearch.WordTrace]
  refine ⟨279981054078746659393593833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186654036052497772929062555 279981054078746659393593833)
  ·
    refine ⟨209985790559059994545195375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279981054078746659393593833 209985790559059994545195375)
    ·
      refine ⟨314978685838589991817793063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209985790559059994545195375 314978685838589991817793063)
      ·
        refine ⟨472468028757884987726689595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314978685838589991817793063 472468028757884987726689595)
        ·
          refine ⟨708702043136827481590034393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472468028757884987726689595 708702043136827481590034393)
          ·
            refine ⟨531526532352620611192525795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 708702043136827481590034393 531526532352620611192525795)
            ·
              refine ⟨797289798528930916788788693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531526532352620611192525795 797289798528930916788788693)
              ·
                refine ⟨18686479653021818362237235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 797289798528930916788788693 18686479653021818362237235)
                ·
                  refine ⟨28029719479532727543355853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18686479653021818362237235 28029719479532727543355853)
                  ·
                    refine ⟨10511144804824772828758445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28029719479532727543355853 10511144804824772828758445)
                    ·
                      refine ⟨3941679301809289810784417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10511144804824772828758445 3941679301809289810784417)
                      ·
                        rfl

theorem cell23_7676393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 7, 1, 3, 3].length) (baseStart_7676393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676393 prefixEnd_7676393 := by exact prefixLift 7676393
  have htrace : WordTrace (prefixWord ++ tailWord_7676393) baseStart_7676393 baseEnd_7676393 := by
    simpa [prefixWord, tailWord_7676393, baseEnd_7676393] using wordTrace_append hprefix tailTrace_7676393
  have hstable : (prefixWord ++ tailWord_7676393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676393).length < 2 ^ (prefixWord ++ tailWord_7676393).sum := by decide
  have hdescent : baseEnd_7676393 < baseStart_7676393 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676397 : List Nat := [1, 5, 1, 3, 1, 1, 1, 4, 1, 2, 3]
def baseStart_7676397 : Nat := 118140960795 + 7676397 * 2 ^ 59
def prefixEnd_7676397 : Nat := 4983230072969 + 3 ^ 40 * 7676397 * 2
def baseEnd_7676397 : Nat := 3941681355731907795134399

theorem tailTrace_7676397 : CollatzResearch.WordTrace tailWord_7676397 prefixEnd_7676397 3941681355731907795134399 := by
  unfold tailWord_7676397
  simp only [CollatzResearch.WordTrace]
  refine ⟨279981199970732168076739445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186654133313821445384492963 279981199970732168076739445)
  ·
    refine ⟨26248237497256140757194323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279981199970732168076739445 26248237497256140757194323)
    ·
      refine ⟨39372356245884211135791485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26248237497256140757194323 39372356245884211135791485)
      ·
        refine ⟨14764633592206579175921807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39372356245884211135791485 14764633592206579175921807)
        ·
          refine ⟨22146950388309868763882711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14764633592206579175921807 22146950388309868763882711)
          ·
            refine ⟨33220425582464803145824067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22146950388309868763882711 33220425582464803145824067)
            ·
              refine ⟨49830638373697204718736101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33220425582464803145824067 49830638373697204718736101)
              ·
                refine ⟨9343244695068225884763019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49830638373697204718736101 9343244695068225884763019)
                ·
                  refine ⟨14014867042602338827144529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9343244695068225884763019 14014867042602338827144529)
                  ·
                    refine ⟨10511150281951754120358397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14014867042602338827144529 10511150281951754120358397)
                    ·
                      refine ⟨3941681355731907795134399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10511150281951754120358397 3941681355731907795134399)
                      ·
                        rfl

theorem cell23_7676397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_7676397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676397 prefixEnd_7676397 := by exact prefixLift 7676397
  have htrace : WordTrace (prefixWord ++ tailWord_7676397) baseStart_7676397 baseEnd_7676397 := by
    simpa [prefixWord, tailWord_7676397, baseEnd_7676397] using wordTrace_append hprefix tailTrace_7676397
  have hstable : (prefixWord ++ tailWord_7676397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676397).length < 2 ^ (prefixWord ++ tailWord_7676397).sum := by decide
  have hdescent : baseEnd_7676397 < baseStart_7676397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676416 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 8]
def baseStart_7676416 : Nat := 118140960795 + 7676416 * 2 ^ 59
def prefixEnd_7676416 : Nat := 4983230072969 + 3 ^ 40 * 7676416 * 2
def baseEnd_7676416 : Nat := 3941691111864343220796811

theorem tailTrace_7676416 : CollatzResearch.WordTrace tailWord_7676416 prefixEnd_7676416 3941691111864343220796811 := by
  unfold tailWord_7676416
  simp only [CollatzResearch.WordTrace]
  refine ⟨139990946478831667160840551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186654595305108889547787401 139990946478831667160840551)
  ·
    refine ⟨209986419718247500741260827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139990946478831667160840551 209986419718247500741260827)
    ·
      refine ⟨314979629577371251111891241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209986419718247500741260827 314979629577371251111891241)
      ·
        refine ⟨236234722183028438333918431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314979629577371251111891241 236234722183028438333918431)
        ·
          refine ⟨354352083274542657500877647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236234722183028438333918431 354352083274542657500877647)
          ·
            refine ⟨531528124911813986251316471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354352083274542657500877647 531528124911813986251316471)
            ·
              refine ⟨797292187367720979376974707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531528124911813986251316471 797292187367720979376974707)
              ·
                refine ⟨1195938281051581469065462061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 797292187367720979376974707 1195938281051581469065462061)
                ·
                  refine ⟨448476855394343050899548273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1195938281051581469065462061 448476855394343050899548273)
                  ·
                    refine ⟨336357641545757288174661205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 448476855394343050899548273 336357641545757288174661205)
                    ·
                      refine ⟨3941691111864343220796811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 336357641545757288174661205 3941691111864343220796811)
                      ·
                        rfl

theorem cell23_7676416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_7676416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676416 prefixEnd_7676416 := by exact prefixLift 7676416
  have htrace : WordTrace (prefixWord ++ tailWord_7676416) baseStart_7676416 baseEnd_7676416 := by
    simpa [prefixWord, tailWord_7676416, baseEnd_7676416] using wordTrace_append hprefix tailTrace_7676416
  have hstable : (prefixWord ++ tailWord_7676416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676416).length < 2 ^ (prefixWord ++ tailWord_7676416).sum := by decide
  have hdescent : baseEnd_7676416 < baseStart_7676416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676444 : List Nat := [2, 2, 3, 1, 2, 2, 4, 1, 2, 1, 3]
def baseStart_7676444 : Nat := 118140960795 + 7676444 * 2 ^ 59
def prefixEnd_7676444 : Nat := 4983230072969 + 3 ^ 40 * 7676444 * 2
def baseEnd_7676444 : Nat := 3941705489322669111246683

theorem tailTrace_7676444 : CollatzResearch.WordTrace tailWord_7676444 prefixEnd_7676444 3941705489322669111246683 := by
  unfold tailWord_7676444
  simp only [CollatzResearch.WordTrace]
  refine ⟨139991457100780947551850193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186655276134374596735800257 139991457100780947551850193)
  ·
    refine ⟨104993592825585710663887645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139991457100780947551850193 104993592825585710663887645)
    ·
      refine ⟨39372597309594641498957867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 104993592825585710663887645 39372597309594641498957867)
      ·
        refine ⟨59058895964391962248436801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39372597309594641498957867 59058895964391962248436801)
        ·
          refine ⟨44294171973293971686327601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59058895964391962248436801 44294171973293971686327601)
          ·
            refine ⟨33220628979970478764745701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44294171973293971686327601 33220628979970478764745701)
            ·
              refine ⟨6228867933744464768389819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33220628979970478764745701 6228867933744464768389819)
              ·
                refine ⟨9343301900616697152584729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6228867933744464768389819 9343301900616697152584729)
                ·
                  refine ⟨7007476425462522864438547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9343301900616697152584729 7007476425462522864438547)
                  ·
                    refine ⟨10511214638193784296657821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7007476425462522864438547 10511214638193784296657821)
                    ·
                      refine ⟨3941705489322669111246683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10511214638193784296657821 3941705489322669111246683)
                      ·
                        rfl

theorem cell23_7676444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 2, 1, 3].length) (baseStart_7676444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676444 prefixEnd_7676444 := by exact prefixLift 7676444
  have htrace : WordTrace (prefixWord ++ tailWord_7676444) baseStart_7676444 baseEnd_7676444 := by
    simpa [prefixWord, tailWord_7676444, baseEnd_7676444] using wordTrace_append hprefix tailTrace_7676444
  have hstable : (prefixWord ++ tailWord_7676444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676444).length < 2 ^ (prefixWord ++ tailWord_7676444).sum := by decide
  have hdescent : baseEnd_7676444 < baseStart_7676444 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676453 : List Nat := [1, 3, 1, 2, 2, 1, 3, 2, 2, 1, 5]
def baseStart_7676453 : Nat := 118140960795 + 7676453 * 2 ^ 59
def prefixEnd_7676453 : Nat := 4983230072969 + 3 ^ 40 * 7676453 * 2
def baseEnd_7676453 : Nat := 3941710110648559576034141

theorem tailTrace_7676453 : CollatzResearch.WordTrace tailWord_7676453 prefixEnd_7676453 3941710110648559576034141 := by
  unfold tailWord_7676453
  simp only [CollatzResearch.WordTrace]
  refine ⟨279983242458529289640778013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186655494972352859760518675 279983242458529289640778013)
  ·
    refine ⟨104993715921948483615291755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279983242458529289640778013 104993715921948483615291755)
    ·
      refine ⟨157490573882922725422937633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104993715921948483615291755 157490573882922725422937633)
      ·
        refine ⟨118117930412192044067203225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157490573882922725422937633 118117930412192044067203225)
        ·
          refine ⟨88588447809144033050402419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118117930412192044067203225 88588447809144033050402419)
          ·
            refine ⟨132882671713716049575603629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88588447809144033050402419 132882671713716049575603629)
            ·
              refine ⟨49831001892643518590851361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132882671713716049575603629 49831001892643518590851361)
              ·
                refine ⟨37373251419482638943138521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49831001892643518590851361 37373251419482638943138521)
                ·
                  refine ⟨28029938564611979207353891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37373251419482638943138521 28029938564611979207353891)
                  ·
                    refine ⟨42044907846917968811030837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28029938564611979207353891 42044907846917968811030837)
                    ·
                      refine ⟨3941710110648559576034141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42044907846917968811030837 3941710110648559576034141)
                      ·
                        rfl

theorem cell23_7676453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_7676453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676453 prefixEnd_7676453 := by exact prefixLift 7676453
  have htrace : WordTrace (prefixWord ++ tailWord_7676453) baseStart_7676453 baseEnd_7676453 := by
    simpa [prefixWord, tailWord_7676453, baseEnd_7676453] using wordTrace_append hprefix tailTrace_7676453
  have hstable : (prefixWord ++ tailWord_7676453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676453).length < 2 ^ (prefixWord ++ tailWord_7676453).sum := by decide
  have hdescent : baseEnd_7676453 < baseStart_7676453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676461 : List Nat := [1, 5, 4, 1, 1, 1, 1, 2, 1, 3, 3]
def baseStart_7676461 : Nat := 118140960795 + 7676461 * 2 ^ 59
def prefixEnd_7676461 : Nat := 4983230072969 + 3 ^ 40 * 7676461 * 2
def baseEnd_7676461 : Nat := 3941714218493795544734105

theorem tailTrace_7676461 : CollatzResearch.WordTrace tailWord_7676461 prefixEnd_7676461 3941714218493795544734105 := by
  unfold tailWord_7676461
  simp only [CollatzResearch.WordTrace]
  refine ⟨279983534242500307007069237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186655689495000204671379491 279983534242500307007069237)
  ·
    refine ⟨26248456335234403781912741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 279983534242500307007069237 26248456335234403781912741)
    ·
      refine ⟨4921585562856450709108639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26248456335234403781912741 4921585562856450709108639)
      ·
        refine ⟨7382378344284676063662959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4921585562856450709108639 7382378344284676063662959)
        ·
          refine ⟨11073567516427014095494439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7382378344284676063662959 11073567516427014095494439)
          ·
            refine ⟨16610351274640521143241659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11073567516427014095494439 16610351274640521143241659)
            ·
              refine ⟨24915526911960781714862489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16610351274640521143241659 24915526911960781714862489)
              ·
                refine ⟨18686645183970586286146867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24915526911960781714862489 18686645183970586286146867)
                ·
                  refine ⟨28029967775955879429220301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18686645183970586286146867 28029967775955879429220301)
                  ·
                    refine ⟨10511237915983454785957613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28029967775955879429220301 10511237915983454785957613)
                    ·
                      refine ⟨3941714218493795544734105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10511237915983454785957613 3941714218493795544734105)
                      ·
                        rfl

theorem cell23_7676461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_7676461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676461 prefixEnd_7676461 := by exact prefixLift 7676461
  have htrace : WordTrace (prefixWord ++ tailWord_7676461) baseStart_7676461 baseEnd_7676461 := by
    simpa [prefixWord, tailWord_7676461, baseEnd_7676461] using wordTrace_append hprefix tailTrace_7676461
  have hstable : (prefixWord ++ tailWord_7676461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676461).length < 2 ^ (prefixWord ++ tailWord_7676461).sum := by decide
  have hdescent : baseEnd_7676461 < baseStart_7676461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676483 : List Nat := [1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 3]
def baseStart_7676483 : Nat := 118140960795 + 7676483 * 2 ^ 59
def prefixEnd_7676483 : Nat := 4983230072969 + 3 ^ 40 * 7676483 * 2
def baseEnd_7676483 : Nat := 3941725515068194458659003

theorem tailTrace_7676483 : CollatzResearch.WordTrace tailWord_7676483 prefixEnd_7676483 3941725515068194458659003 := by
  unfold tailWord_7676483
  simp only [CollatzResearch.WordTrace]
  refine ⟨279984336648420604764370103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186656224432280403176246735 279984336648420604764370103)
  ·
    refine ⟨419976504972630907146555155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279984336648420604764370103 419976504972630907146555155)
    ·
      refine ⟨629964757458946360719832733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419976504972630907146555155 629964757458946360719832733)
      ·
        refine ⟨236236784047104885269937275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 629964757458946360719832733 236236784047104885269937275)
        ·
          refine ⟨354355176070657327904905913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236236784047104885269937275 354355176070657327904905913)
          ·
            refine ⟨265766382052992995928679435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354355176070657327904905913 265766382052992995928679435)
            ·
              refine ⟨398649573079489493893019153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265766382052992995928679435 398649573079489493893019153)
              ·
                refine ⟨298987179809617120419764365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 398649573079489493893019153 298987179809617120419764365)
                ·
                  refine ⟨112120192428606420157411637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 298987179809617120419764365 112120192428606420157411637)
                  ·
                    refine ⟨10511268040181851889757341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112120192428606420157411637 10511268040181851889757341)
                    ·
                      refine ⟨3941725515068194458659003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10511268040181851889757341 3941725515068194458659003)
                      ·
                        rfl

theorem cell23_7676483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 5, 3].length) (baseStart_7676483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676483 prefixEnd_7676483 := by exact prefixLift 7676483
  have htrace : WordTrace (prefixWord ++ tailWord_7676483) baseStart_7676483 baseEnd_7676483 := by
    simpa [prefixWord, tailWord_7676483, baseEnd_7676483] using wordTrace_append hprefix tailTrace_7676483
  have hstable : (prefixWord ++ tailWord_7676483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676483).length < 2 ^ (prefixWord ++ tailWord_7676483).sum := by decide
  have hdescent : baseEnd_7676483 < baseStart_7676483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676500 : List Nat := [2, 4, 1, 1, 1, 3, 1, 1, 1, 5, 3]
def baseStart_7676500 : Nat := 118140960795 + 7676500 * 2 ^ 59
def prefixEnd_7676500 : Nat := 4983230072969 + 3 ^ 40 * 7676500 * 2
def baseEnd_7676500 : Nat := 3941734244239320892146425

theorem tailTrace_7676500 : CollatzResearch.WordTrace tailWord_7676500 prefixEnd_7676500 3941734244239320892146425 := by
  unfold tailWord_7676500
  simp only [CollatzResearch.WordTrace]
  refine ⟨139992478344679508333869477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186656637792906011111825969 139992478344679508333869477)
  ·
    refine ⟨26248589689627407812600527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139992478344679508333869477 26248589689627407812600527)
    ·
      refine ⟨39372884534441111718900791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26248589689627407812600527 39372884534441111718900791)
      ·
        refine ⟨59059326801661667578351187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39372884534441111718900791 59059326801661667578351187)
        ·
          refine ⟨88588990202492501367526781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59059326801661667578351187 88588990202492501367526781)
          ·
            refine ⟨33220871325934688012822543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88588990202492501367526781 33220871325934688012822543)
            ·
              refine ⟨49831306988902032019233815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33220871325934688012822543 49831306988902032019233815)
              ·
                refine ⟨74746960483353048028850723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49831306988902032019233815 74746960483353048028850723)
                ·
                  refine ⟨112120440725029572043276085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74746960483353048028850723 112120440725029572043276085)
                  ·
                    refine ⟨10511291317971522379057133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112120440725029572043276085 10511291317971522379057133)
                    ·
                      refine ⟨3941734244239320892146425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10511291317971522379057133 3941734244239320892146425)
                      ·
                        rfl

theorem cell23_7676500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_7676500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676500 prefixEnd_7676500 := by exact prefixLift 7676500
  have htrace : WordTrace (prefixWord ++ tailWord_7676500) baseStart_7676500 baseEnd_7676500 := by
    simpa [prefixWord, tailWord_7676500, baseEnd_7676500] using wordTrace_append hprefix tailTrace_7676500
  have hstable : (prefixWord ++ tailWord_7676500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676500).length < 2 ^ (prefixWord ++ tailWord_7676500).sum := by decide
  have hdescent : baseEnd_7676500 < baseStart_7676500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676503 : List Nat := [1, 1, 3, 2, 2, 2, 2, 2, 1, 7]
def baseStart_7676503 : Nat := 118140960795 + 7676503 * 2 ^ 59
def prefixEnd_7676503 : Nat := 4983230072969 + 3 ^ 40 * 7676503 * 2
def baseEnd_7676503 : Nat := 1313911928227094793469637

theorem tailTrace_7676503 : CollatzResearch.WordTrace tailWord_7676503 prefixEnd_7676503 1313911928227094793469637 := by
  unfold tailWord_7676503
  simp only [CollatzResearch.WordTrace]
  refine ⟨279985066108348148180098163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186656710738898765453398775 279985066108348148180098163)
  ·
    refine ⟨419977599162522222270147245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279985066108348148180098163 419977599162522222270147245)
    ·
      refine ⟨157491599685945833351305217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 419977599162522222270147245 157491599685945833351305217)
      ·
        refine ⟨118118699764459375013478913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157491599685945833351305217 118118699764459375013478913)
        ·
          refine ⟨88589024823344531260109185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118118699764459375013478913 88589024823344531260109185)
          ·
            refine ⟨66441768617508398445081889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88589024823344531260109185 66441768617508398445081889)
            ·
              refine ⟨49831326463131298833811417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66441768617508398445081889 49831326463131298833811417)
              ·
                refine ⟨37373494847348474125358563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49831326463131298833811417 37373494847348474125358563)
                ·
                  refine ⟨56060242271022711188037845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37373494847348474125358563 56060242271022711188037845)
                  ·
                    refine ⟨1313911928227094793469637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56060242271022711188037845 1313911928227094793469637)
                    ·
                      rfl

theorem cell23_7676503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_7676503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676503 prefixEnd_7676503 := by exact prefixLift 7676503
  have htrace : WordTrace (prefixWord ++ tailWord_7676503) baseStart_7676503 baseEnd_7676503 := by
    simpa [prefixWord, tailWord_7676503, baseEnd_7676503] using wordTrace_append hprefix tailTrace_7676503
  have hstable : (prefixWord ++ tailWord_7676503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676503).length < 2 ^ (prefixWord ++ tailWord_7676503).sum := by decide
  have hdescent : baseEnd_7676503 < baseStart_7676503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676540 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_7676540 : Nat := 118140960795 + 7676540 * 2 ^ 59
def prefixEnd_7676540 : Nat := 4983230072969 + 3 ^ 40 * 7676540 * 2
def baseEnd_7676540 : Nat := 3941754783465500735646241

theorem tailTrace_7676540 : CollatzResearch.WordTrace tailWord_7676540 prefixEnd_7676540 3941754783465500735646241 := by
  unfold tailWord_7676540
  simp only [CollatzResearch.WordTrace]
  refine ⟨139993207804607051749597537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186657610406142735666130049 139993207804607051749597537)
  ·
    refine ⟨104994905853455288812198153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139993207804607051749597537 104994905853455288812198153)
    ·
      refine ⟨78746179390091466609148615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104994905853455288812198153 78746179390091466609148615)
      ·
        refine ⟨118119269085137199913722923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78746179390091466609148615 118119269085137199913722923)
        ·
          refine ⟨177178903627705799870584385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118119269085137199913722923 177178903627705799870584385)
          ·
            refine ⟨132884177720779349902938289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177178903627705799870584385 132884177720779349902938289)
            ·
              refine ⟨99663133290584512427203717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132884177720779349902938289 99663133290584512427203717)
              ·
                refine ⟨18686837491984596080100697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99663133290584512427203717 18686837491984596080100697)
                ·
                  refine ⟨14015128118988447060075523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18686837491984596080100697 14015128118988447060075523)
                  ·
                    refine ⟨21022692178482670590113285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14015128118988447060075523 21022692178482670590113285)
                    ·
                      refine ⟨3941754783465500735646241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21022692178482670590113285 3941754783465500735646241)
                      ·
                        rfl

theorem cell23_7676540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_7676540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676540 prefixEnd_7676540 := by exact prefixLift 7676540
  have htrace : WordTrace (prefixWord ++ tailWord_7676540) baseStart_7676540 baseEnd_7676540 := by
    simpa [prefixWord, tailWord_7676540, baseEnd_7676540] using wordTrace_append hprefix tailTrace_7676540
  have hstable : (prefixWord ++ tailWord_7676540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676540).length < 2 ^ (prefixWord ++ tailWord_7676540).sum := by decide
  have hdescent : baseEnd_7676540 < baseStart_7676540 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676553 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 4, 1, 6]
def baseStart_7676553 : Nat := 118140960795 + 7676553 * 2 ^ 59
def prefixEnd_7676553 : Nat := 4983230072969 + 3 ^ 40 * 7676553 * 2
def baseEnd_7676553 : Nat := 3941761458714009184783681

theorem tailTrace_7676553 : CollatzResearch.WordTrace tailWord_7676553 prefixEnd_7676553 3941761458714009184783681 := by
  unfold tailWord_7676553
  simp only [CollatzResearch.WordTrace]
  refine ⟨279986889758167006719418313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186657926505444671146278875 279986889758167006719418313)
  ·
    refine ⟨209990167318625255039563735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 279986889758167006719418313 209990167318625255039563735)
    ·
      refine ⟨314985250977937882559345603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209990167318625255039563735 314985250977937882559345603)
      ·
        refine ⟨472477876466906823839018405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314985250977937882559345603 472477876466906823839018405)
        ·
          refine ⟨88589601837545029469815951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 472477876466906823839018405 88589601837545029469815951)
          ·
            refine ⟨132884402756317544204723927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88589601837545029469815951 132884402756317544204723927)
            ·
              refine ⟨199326604134476316307085891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132884402756317544204723927 199326604134476316307085891)
              ·
                refine ⟨298989906201714474460628837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199326604134476316307085891 298989906201714474460628837)
                ·
                  refine ⟨56060607412821463961367907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 298989906201714474460628837 56060607412821463961367907)
                  ·
                    refine ⟨84090911119232195942051861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56060607412821463961367907 84090911119232195942051861)
                    ·
                      refine ⟨3941761458714009184783681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84090911119232195942051861 3941761458714009184783681)
                      ·
                        rfl

theorem cell23_7676553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_7676553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676553 prefixEnd_7676553 := by exact prefixLift 7676553
  have htrace : WordTrace (prefixWord ++ tailWord_7676553) baseStart_7676553 baseEnd_7676553 := by
    simpa [prefixWord, tailWord_7676553, baseEnd_7676553] using wordTrace_append hprefix tailTrace_7676553
  have hstable : (prefixWord ++ tailWord_7676553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676553).length < 2 ^ (prefixWord ++ tailWord_7676553).sum := by decide
  have hdescent : baseEnd_7676553 < baseStart_7676553 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676603 : List Nat := [1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 7]
def baseStart_7676603 : Nat := 118140960795 + 7676603 * 2 ^ 59
def prefixEnd_7676603 : Nat := 4983230072969 + 3 ^ 40 * 7676603 * 2
def baseEnd_7676603 : Nat := 3941787132746733989158451

theorem tailTrace_7676603 : CollatzResearch.WordTrace tailWord_7676603 prefixEnd_7676603 3941787132746733989158451 := by
  unfold tailWord_7676603
  simp only [CollatzResearch.WordTrace]
  refine ⟨279988713407985865258738463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186659142271990576839158975 279988713407985865258738463)
  ·
    refine ⟨419983070111978797888107695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279988713407985865258738463 419983070111978797888107695)
    ·
      refine ⟨629974605167968196832161543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419983070111978797888107695 629974605167968196832161543)
      ·
        refine ⟨944961907751952295248242315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 629974605167968196832161543 944961907751952295248242315)
        ·
          refine ⟨1417442861627928442872363473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 944961907751952295248242315 1417442861627928442872363473)
          ·
            refine ⟨1063082146220946332154272605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1417442861627928442872363473 1063082146220946332154272605)
            ·
              refine ⟨398655804832854874557852227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1063082146220946332154272605 398655804832854874557852227)
              ·
                refine ⟨597983707249282311836778341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398655804832854874557852227 597983707249282311836778341)
                ·
                  refine ⟨112121945109240433469395939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 597983707249282311836778341 112121945109240433469395939)
                  ·
                    refine ⟨168182917663860650204093909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112121945109240433469395939 168182917663860650204093909)
                    ·
                      refine ⟨3941787132746733989158451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168182917663860650204093909 3941787132746733989158451)
                      ·
                        rfl

theorem cell23_7676603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 7].length) (baseStart_7676603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676603 prefixEnd_7676603 := by exact prefixLift 7676603
  have htrace : WordTrace (prefixWord ++ tailWord_7676603) baseStart_7676603 baseEnd_7676603 := by
    simpa [prefixWord, tailWord_7676603, baseEnd_7676603] using wordTrace_append hprefix tailTrace_7676603
  have hstable : (prefixWord ++ tailWord_7676603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676603).length < 2 ^ (prefixWord ++ tailWord_7676603).sum := by decide
  have hdescent : baseEnd_7676603 < baseStart_7676603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676634 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2]
def baseStart_7676634 : Nat := 118140960795 + 7676634 * 2 ^ 59
def prefixEnd_7676634 : Nat := 4983230072969 + 3 ^ 40 * 7676634 * 2
def baseEnd_7676634 : Nat := 3941803050647023367870809

theorem tailTrace_7676634 : CollatzResearch.WordTrace tailWord_7676634 prefixEnd_7676634 3941803050647023367870809 := by
  unfold tailWord_7676634
  simp only [CollatzResearch.WordTrace]
  refine ⟨69997461017718389388279239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186659896047249038368744637 69997461017718389388279239)
  ·
    refine ⟨104996191526577584082418859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69997461017718389388279239 104996191526577584082418859)
    ·
      refine ⟨157494287289866376123628289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104996191526577584082418859 157494287289866376123628289)
      ·
        refine ⟨118120715467399782092721217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157494287289866376123628289 118120715467399782092721217)
        ·
          refine ⟨88590536600549836569540913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118120715467399782092721217 88590536600549836569540913)
          ·
            refine ⟨66442902450412377427155685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88590536600549836569540913 66442902450412377427155685)
            ·
              refine ⟨12458044209452320767591691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66442902450412377427155685 12458044209452320767591691)
              ·
                refine ⟨18687066314178481151387537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12458044209452320767591691 18687066314178481151387537)
                ·
                  refine ⟨14015299735633860863540653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18687066314178481151387537 14015299735633860863540653)
                  ·
                    refine ⟨5255737400862697823827745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14015299735633860863540653 5255737400862697823827745)
                    ·
                      refine ⟨3941803050647023367870809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255737400862697823827745 3941803050647023367870809)
                      ·
                        rfl

theorem cell23_7676634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_7676634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676634 prefixEnd_7676634 := by exact prefixLift 7676634
  have htrace : WordTrace (prefixWord ++ tailWord_7676634) baseStart_7676634 baseEnd_7676634 := by
    simpa [prefixWord, tailWord_7676634, baseEnd_7676634] using wordTrace_append hprefix tailTrace_7676634
  have hstable : (prefixWord ++ tailWord_7676634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676634).length < 2 ^ (prefixWord ++ tailWord_7676634).sum := by decide
  have hdescent : baseEnd_7676634 < baseStart_7676634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676644 : List Nat := [2, 3, 1, 1, 1, 5, 3, 1, 1, 5]
def baseStart_7676644 : Nat := 118140960795 + 7676644 * 2 ^ 59
def prefixEnd_7676644 : Nat := 4983230072969 + 3 ^ 40 * 7676644 * 2
def baseEnd_7676644 : Nat := 1313936061817856109581921

theorem tailTrace_7676644 : CollatzResearch.WordTrace tailWord_7676644 prefixEnd_7676644 1313936061817856109581921 := by
  unfold tailWord_7676644
  simp only [CollatzResearch.WordTrace]
  refine ⟨139995104400418664630490493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186660139200558219507320657 139995104400418664630490493)
  ·
    refine ⟨52498164150156999236433935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139995104400418664630490493 52498164150156999236433935)
    ·
      refine ⟨78747246225235498854650903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52498164150156999236433935 78747246225235498854650903)
      ·
        refine ⟨118120869337853248281976355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78747246225235498854650903 118120869337853248281976355)
        ·
          refine ⟨177181304006779872422964533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118120869337853248281976355 177181304006779872422964533)
          ·
            refine ⟨16610747250635613039652925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177181304006779872422964533 16610747250635613039652925)
            ·
              refine ⟨6229030218988354889869847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16610747250635613039652925 6229030218988354889869847)
              ·
                refine ⟨9343545328482532334804771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6229030218988354889869847 9343545328482532334804771)
                ·
                  refine ⟨14015317992723798502207157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9343545328482532334804771 14015317992723798502207157)
                  ·
                    refine ⟨1313936061817856109581921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14015317992723798502207157 1313936061817856109581921)
                    ·
                      rfl

theorem cell23_7676644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_7676644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676644 prefixEnd_7676644 := by exact prefixLift 7676644
  have htrace : WordTrace (prefixWord ++ tailWord_7676644) baseStart_7676644 baseEnd_7676644 := by
    simpa [prefixWord, tailWord_7676644, baseEnd_7676644] using wordTrace_append hprefix tailTrace_7676644
  have hstable : (prefixWord ++ tailWord_7676644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676644).length < 2 ^ (prefixWord ++ tailWord_7676644).sum := by decide
  have hdescent : baseEnd_7676644 < baseStart_7676644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676658 : List Nat := [3, 2, 1, 3, 1, 2, 4, 2, 1, 1, 3]
def baseStart_7676658 : Nat := 118140960795 + 7676658 * 2 ^ 59
def prefixEnd_7676658 : Nat := 4983230072969 + 3 ^ 40 * 7676658 * 2
def baseEnd_7676658 : Nat := 3941815374182731273970699

theorem tailTrace_7676658 : CollatzResearch.WordTrace tailWord_7676658 prefixEnd_7676658 3941815374182731273970699 := by
  unfold tailWord_7676658
  simp only [CollatzResearch.WordTrace]
  refine ⟨69997679855696652412997657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186660479615191073101327085 69997679855696652412997657)
  ·
    refine ⟨52498259891772489309748243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69997679855696652412997657 52498259891772489309748243)
    ·
      refine ⟨78747389837658733964622365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52498259891772489309748243 78747389837658733964622365)
      ·
        refine ⟨29530271189122025236733387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78747389837658733964622365 29530271189122025236733387)
        ·
          refine ⟨44295406783683037855100081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29530271189122025236733387 44295406783683037855100081)
          ·
            refine ⟨33221555087762278391325061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44295406783683037855100081 33221555087762278391325061)
            ·
              refine ⟨6229041578955427198373449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33221555087762278391325061 6229041578955427198373449)
              ·
                refine ⟨4671781184216570398780087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6229041578955427198373449 4671781184216570398780087)
                ·
                  refine ⟨7007671776324855598170131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671781184216570398780087 7007671776324855598170131)
                  ·
                    refine ⟨10511507664487283397255197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7007671776324855598170131 10511507664487283397255197)
                    ·
                      refine ⟨3941815374182731273970699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10511507664487283397255197 3941815374182731273970699)
                      ·
                        rfl

theorem cell23_7676658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_7676658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676658 prefixEnd_7676658 := by exact prefixLift 7676658
  have htrace : WordTrace (prefixWord ++ tailWord_7676658) baseStart_7676658 baseEnd_7676658 := by
    simpa [prefixWord, tailWord_7676658, baseEnd_7676658] using wordTrace_append hprefix tailTrace_7676658
  have hstable : (prefixWord ++ tailWord_7676658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676658).length < 2 ^ (prefixWord ++ tailWord_7676658).sum := by decide
  have hdescent : baseEnd_7676658 < baseStart_7676658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676664 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 3, 2, 2]
def baseStart_7676664 : Nat := 118140960795 + 7676664 * 2 ^ 59
def prefixEnd_7676664 : Nat := 4983230072969 + 3 ^ 40 * 7676664 * 2
def baseEnd_7676664 : Nat := 3941818455066658250495671

theorem tailTrace_7676664 : CollatzResearch.WordTrace tailWord_7676664 prefixEnd_7676664 3941818455066658250495671 := by
  unfold tailWord_7676664
  simp only [CollatzResearch.WordTrace]
  refine ⟨139995469130382436338354523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186660625507176581784472697 139995469130382436338354523)
  ·
    refine ⟨209993203695573654507531785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139995469130382436338354523 209993203695573654507531785)
    ·
      refine ⟨157494902771680240880648839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209993203695573654507531785 157494902771680240880648839)
      ·
        refine ⟨236242354157520361320973259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157494902771680240880648839 236242354157520361320973259)
        ·
          refine ⟨354363531236280541981459889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236242354157520361320973259 354363531236280541981459889)
          ·
            refine ⟨265772648427210406486094917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354363531236280541981459889 265772648427210406486094917)
            ·
              refine ⟨49832371580101951216142797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265772648427210406486094917 49832371580101951216142797)
              ·
                refine ⟨18687139342538231706053549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49832371580101951216142797 18687139342538231706053549)
                ·
                  refine ⟨7007677253451836889770081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18687139342538231706053549 7007677253451836889770081)
                  ·
                    refine ⟨5255757940088877667327561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7007677253451836889770081 5255757940088877667327561)
                    ·
                      refine ⟨3941818455066658250495671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255757940088877667327561 3941818455066658250495671)
                      ·
                        rfl

theorem cell23_7676664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 3, 2, 2].length) (baseStart_7676664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676664 prefixEnd_7676664 := by exact prefixLift 7676664
  have htrace : WordTrace (prefixWord ++ tailWord_7676664) baseStart_7676664 baseEnd_7676664 := by
    simpa [prefixWord, tailWord_7676664, baseEnd_7676664] using wordTrace_append hprefix tailTrace_7676664
  have hstable : (prefixWord ++ tailWord_7676664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676664).length < 2 ^ (prefixWord ++ tailWord_7676664).sum := by decide
  have hdescent : baseEnd_7676664 < baseStart_7676664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676674 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_7676674 : Nat := 118140960795 + 7676674 * 2 ^ 59
def prefixEnd_7676674 : Nat := 4983230072969 + 3 ^ 40 * 7676674 * 2
def baseEnd_7676674 : Nat := 1313941196624401070456875

theorem tailTrace_7676674 : CollatzResearch.WordTrace tailWord_7676674 prefixEnd_7676674 1313941196624401070456875 := by
  unfold tailWord_7676674
  simp only [CollatzResearch.WordTrace]
  refine ⟨69997825747682161096143269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186660868660485762923048717 69997825747682161096143269)
  ·
    refine ⟨13124592327690405205526863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 69997825747682161096143269 13124592327690405205526863)
    ·
      refine ⟨19686888491535607808290295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13124592327690405205526863 19686888491535607808290295)
      ·
        refine ⟨29530332737303411712435443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19686888491535607808290295 29530332737303411712435443)
        ·
          refine ⟨44295499105955117568653165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29530332737303411712435443 44295499105955117568653165)
          ·
            refine ⟨16610812164733169088244937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44295499105955117568653165 16610812164733169088244937)
            ·
              refine ⟨12458109123549876816183703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16610812164733169088244937 12458109123549876816183703)
              ·
                refine ⟨18687163685324815224275555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12458109123549876816183703 18687163685324815224275555)
                ·
                  refine ⟨28030745527987222836413333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18687163685324815224275555 28030745527987222836413333)
                  ·
                    refine ⟨1313941196624401070456875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28030745527987222836413333 1313941196624401070456875)
                    ·
                      rfl

theorem cell23_7676674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_7676674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676674 prefixEnd_7676674 := by exact prefixLift 7676674
  have htrace : WordTrace (prefixWord ++ tailWord_7676674) baseStart_7676674 baseEnd_7676674 := by
    simpa [prefixWord, tailWord_7676674, baseEnd_7676674] using wordTrace_append hprefix tailTrace_7676674
  have hstable : (prefixWord ++ tailWord_7676674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676674).length < 2 ^ (prefixWord ++ tailWord_7676674).sum := by decide
  have hdescent : baseEnd_7676674 < baseStart_7676674 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676698 : List Nat := [3, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2]
def baseStart_7676698 : Nat := 118140960795 + 7676698 * 2 ^ 59
def prefixEnd_7676698 : Nat := 4983230072969 + 3 ^ 40 * 7676698 * 2
def baseEnd_7676698 : Nat := 3941835913408911117470515

theorem tailTrace_7676698 : CollatzResearch.WordTrace tailWord_7676698 prefixEnd_7676698 3941835913408911117470515 := by
  unfold tailWord_7676698
  simp only [CollatzResearch.WordTrace]
  refine ⟨69998044585660424120861687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186661452228427797655631165 69998044585660424120861687)
  ·
    refine ⟨104997066878490636181292531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 69998044585660424120861687 104997066878490636181292531)
    ·
      refine ⟨157495600317735954271938797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104997066878490636181292531 157495600317735954271938797)
      ·
        refine ⟨59060850119150982851977049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157495600317735954271938797 59060850119150982851977049)
        ·
          refine ⟨44295637589363237138982787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59060850119150982851977049 44295637589363237138982787)
          ·
            refine ⟨66443456384044855708474181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44295637589363237138982787 66443456384044855708474181)
            ·
              refine ⟨12458148072008410445338909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66443456384044855708474181 12458148072008410445338909)
              ·
                refine ⟨4671805527003153917002091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12458148072008410445338909 4671805527003153917002091)
                ·
                  refine ⟨7007708290504730875503137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671805527003153917002091 7007708290504730875503137)
                  ·
                    refine ⟨5255781217878548156627353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7007708290504730875503137 5255781217878548156627353)
                    ·
                      refine ⟨3941835913408911117470515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255781217878548156627353 3941835913408911117470515)
                      ·
                        rfl

theorem cell23_7676698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_7676698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676698 prefixEnd_7676698 := by exact prefixLift 7676698
  have htrace : WordTrace (prefixWord ++ tailWord_7676698) baseStart_7676698 baseEnd_7676698 := by
    simpa [prefixWord, tailWord_7676698, baseEnd_7676698] using wordTrace_append hprefix tailTrace_7676698
  have hstable : (prefixWord ++ tailWord_7676698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676698).length < 2 ^ (prefixWord ++ tailWord_7676698).sum := by decide
  have hdescent : baseEnd_7676698 < baseStart_7676698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676708 : List Nat := [2, 3, 1, 3, 4, 1, 1, 2, 2, 4]
def baseStart_7676708 : Nat := 118140960795 + 7676708 * 2 ^ 59
def prefixEnd_7676708 : Nat := 4983230072969 + 3 ^ 40 * 7676708 * 2
def baseEnd_7676708 : Nat := 1313947016071818692781823

theorem tailTrace_7676708 : CollatzResearch.WordTrace tailWord_7676708 prefixEnd_7676708 1313947016071818692781823 := by
  unfold tailWord_7676708
  simp only [CollatzResearch.WordTrace]
  refine ⟨139996271536302734095655389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186661695381736978794207185 139996271536302734095655389)
  ·
    refine ⟨52498601826113525285870771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 139996271536302734095655389 52498601826113525285870771)
    ·
      refine ⟨78747902739170287928806157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52498601826113525285870771 78747902739170287928806157)
      ·
        refine ⟨29530463527188857973302309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78747902739170287928806157 29530463527188857973302309)
        ·
          refine ⟨5536961911347910869994183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29530463527188857973302309 5536961911347910869994183)
          ·
            refine ⟨8305442867021866304991275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5536961911347910869994183 8305442867021866304991275)
            ·
              refine ⟨12458164300532799457486913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8305442867021866304991275 12458164300532799457486913)
              ·
                refine ⟨9343623225399599593115185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12458164300532799457486913 9343623225399599593115185)
                ·
                  refine ⟨7007717419049699694836389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9343623225399599593115185 7007717419049699694836389)
                  ·
                    refine ⟨1313947016071818692781823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7007717419049699694836389 1313947016071818692781823)
                    ·
                      rfl

theorem cell23_7676708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_7676708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676708 prefixEnd_7676708 := by exact prefixLift 7676708
  have htrace : WordTrace (prefixWord ++ tailWord_7676708) baseStart_7676708 baseEnd_7676708 := by
    simpa [prefixWord, tailWord_7676708, baseEnd_7676708] using wordTrace_append hprefix tailTrace_7676708
  have hstable : (prefixWord ++ tailWord_7676708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676708).length < 2 ^ (prefixWord ++ tailWord_7676708).sum := by decide
  have hdescent : baseEnd_7676708 < baseStart_7676708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676720 : List Nat := [2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 4]
def baseStart_7676720 : Nat := 118140960795 + 7676720 * 2 ^ 59
def prefixEnd_7676720 : Nat := 4983230072969 + 3 ^ 40 * 7676720 * 2
def baseEnd_7676720 : Nat := 3941847209983310031395413

theorem tailTrace_7676720 : CollatzResearch.WordTrace tailWord_7676720 prefixEnd_7676720 3941847209983310031395413 := by
  unfold tailWord_7676720
  simp only [CollatzResearch.WordTrace]
  refine ⟨139996490374280997120373807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186661987165707996160498409 139996490374280997120373807)
  ·
    refine ⟨209994735561421495680560711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139996490374280997120373807 209994735561421495680560711)
    ·
      refine ⟨314992103342132243520841067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209994735561421495680560711 314992103342132243520841067)
      ·
        refine ⟨472488155013198365281261601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314992103342132243520841067 472488155013198365281261601)
        ·
          refine ⟨354366116259898773960946201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472488155013198365281261601 354366116259898773960946201)
          ·
            refine ⟨265774587194924080470709651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354366116259898773960946201 265774587194924080470709651)
            ·
              refine ⟨398661880792386120706064477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265774587194924080470709651 398661880792386120706064477)
              ·
                refine ⟨149498205297144795264774179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398661880792386120706064477 149498205297144795264774179)
                ·
                  refine ⟨224247307945717192897161269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149498205297144795264774179 224247307945717192897161269)
                  ·
                    refine ⟨21023185119910986834108869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 224247307945717192897161269 21023185119910986834108869)
                    ·
                      refine ⟨3941847209983310031395413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21023185119910986834108869 3941847209983310031395413)
                      ·
                        rfl

theorem cell23_7676720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_7676720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676720 prefixEnd_7676720 := by exact prefixLift 7676720
  have htrace : WordTrace (prefixWord ++ tailWord_7676720) baseStart_7676720 baseEnd_7676720 := by
    simpa [prefixWord, tailWord_7676720, baseEnd_7676720] using wordTrace_append hprefix tailTrace_7676720
  have hstable : (prefixWord ++ tailWord_7676720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676720).length < 2 ^ (prefixWord ++ tailWord_7676720).sum := by decide
  have hdescent : baseEnd_7676720 < baseStart_7676720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676749 : List Nat := [1, 6, 1, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_7676749 : Nat := 118140960795 + 7676749 * 2 ^ 59
def prefixEnd_7676749 : Nat := 4983230072969 + 3 ^ 40 * 7676749 * 2
def baseEnd_7676749 : Nat := 3941862100922290417932781

theorem tailTrace_7676749 : CollatzResearch.WordTrace tailWord_7676749 prefixEnd_7676749 3941862100922290417932781 := by
  unfold tailWord_7676749
  simp only [CollatzResearch.WordTrace]
  refine ⟨279994038465456932193553301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186662692310304621462368867 279994038465456932193553301)
  ·
    refine ⟨13124720553068293696572811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 279994038465456932193553301 13124720553068293696572811)
    ·
      refine ⟨19687080829602440544859217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13124720553068293696572811 19687080829602440544859217)
      ·
        refine ⟨14765310622201830408644413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19687080829602440544859217 14765310622201830408644413)
        ·
          refine ⟨5536991483325686403241655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14765310622201830408644413 5536991483325686403241655)
          ·
            refine ⟨8305487224988529604862483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5536991483325686403241655 8305487224988529604862483)
            ·
              refine ⟨12458230837482794407293725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8305487224988529604862483 12458230837482794407293725)
              ·
                refine ⟨4671836564056047902735147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12458230837482794407293725 4671836564056047902735147)
                ·
                  refine ⟨7007754846084071854102721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671836564056047902735147 7007754846084071854102721)
                  ·
                    refine ⟨5255816134563053890577041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7007754846084071854102721 5255816134563053890577041)
                    ·
                      refine ⟨3941862100922290417932781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255816134563053890577041 3941862100922290417932781)
                      ·
                        rfl

theorem cell23_7676749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_7676749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676749 prefixEnd_7676749 := by exact prefixLift 7676749
  have htrace : WordTrace (prefixWord ++ tailWord_7676749) baseStart_7676749 baseEnd_7676749 := by
    simpa [prefixWord, tailWord_7676749, baseEnd_7676749] using wordTrace_append hprefix tailTrace_7676749
  have hstable : (prefixWord ++ tailWord_7676749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676749).length < 2 ^ (prefixWord ++ tailWord_7676749).sum := by decide
  have hdescent : baseEnd_7676749 < baseStart_7676749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676754 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2]
def baseStart_7676754 : Nat := 118140960795 + 7676754 * 2 ^ 59
def prefixEnd_7676754 : Nat := 4983230072969 + 3 ^ 40 * 7676754 * 2
def baseEnd_7676754 : Nat := 3941864668325562898370257

theorem tailTrace_7676754 : CollatzResearch.WordTrace tailWord_7676754 prefixEnd_7676754 3941864668325562898370257 := by
  unfold tailWord_7676754
  simp only [CollatzResearch.WordTrace]
  refine ⟨69998555207609704511871329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186662813886959212031656877 69998555207609704511871329)
  ·
    refine ⟨52498916405707278383903497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 69998555207609704511871329 52498916405707278383903497)
    ·
      refine ⟨39374187304280458787927623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52498916405707278383903497 39374187304280458787927623)
      ·
        refine ⟨59061280956420688181891435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39374187304280458787927623 59061280956420688181891435)
        ·
          refine ⟨88591921434631032272837153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59061280956420688181891435 88591921434631032272837153)
          ·
            refine ⟨66443941075973274204627865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88591921434631032272837153 66443941075973274204627865)
            ·
              refine ⟨49832955806979955653470899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66443941075973274204627865 49832955806979955653470899)
              ·
                refine ⟨74749433710469933480206349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49832955806979955653470899 74749433710469933480206349)
                ·
                  refine ⟨28031037641426225055077381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74749433710469933480206349 28031037641426225055077381)
                  ·
                    refine ⟨5255819557767417197827009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28031037641426225055077381 5255819557767417197827009)
                    ·
                      refine ⟨3941864668325562898370257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255819557767417197827009 3941864668325562898370257)
                      ·
                        rfl

theorem cell23_7676754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2].length) (baseStart_7676754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676754 prefixEnd_7676754 := by exact prefixLift 7676754
  have htrace : WordTrace (prefixWord ++ tailWord_7676754) baseStart_7676754 baseEnd_7676754 := by
    simpa [prefixWord, tailWord_7676754, baseEnd_7676754] using wordTrace_append hprefix tailTrace_7676754
  have hstable : (prefixWord ++ tailWord_7676754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676754).length < 2 ^ (prefixWord ++ tailWord_7676754).sum := by decide
  have hdescent : baseEnd_7676754 < baseStart_7676754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676757 : List Nat := [1, 3, 2, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_7676757 : Nat := 118140960795 + 7676757 * 2 ^ 59
def prefixEnd_7676757 : Nat := 4983230072969 + 3 ^ 40 * 7676757 * 2
def baseEnd_7676757 : Nat := 3941866208767526386632743

theorem tailTrace_7676757 : CollatzResearch.WordTrace tailWord_7676757 prefixEnd_7676757 3941866208767526386632743 := by
  unfold tailWord_7676757
  simp only [CollatzResearch.WordTrace]
  refine ⟨279994330249427949559844525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186662886832951966373229683 279994330249427949559844525)
  ·
    refine ⟨104997873843535481084941697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 279994330249427949559844525 104997873843535481084941697)
    ·
      refine ⟨78748405382651610813706273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 104997873843535481084941697 78748405382651610813706273)
      ·
        refine ⟨59061304036988708110279705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78748405382651610813706273 59061304036988708110279705)
        ·
          refine ⟨44295978027741531082709779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59061304036988708110279705 44295978027741531082709779)
          ·
            refine ⟨66443967041612296624064669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44295978027741531082709779 66443967041612296624064669)
            ·
              refine ⟨24916487640604611234024251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66443967041612296624064669 24916487640604611234024251)
              ·
                refine ⟨37374731460906916851036377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24916487640604611234024251 37374731460906916851036377)
                ·
                  refine ⟨28031048595680187638277283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37374731460906916851036377 28031048595680187638277283)
                  ·
                    refine ⟨42046572893520281457415925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28031048595680187638277283 42046572893520281457415925)
                    ·
                      refine ⟨3941866208767526386632743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42046572893520281457415925 3941866208767526386632743)
                      ·
                        rfl

theorem cell23_7676757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_7676757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676757 prefixEnd_7676757 := by exact prefixLift 7676757
  have htrace : WordTrace (prefixWord ++ tailWord_7676757) baseStart_7676757 baseEnd_7676757 := by
    simpa [prefixWord, tailWord_7676757, baseEnd_7676757] using wordTrace_append hprefix tailTrace_7676757
  have hstable : (prefixWord ++ tailWord_7676757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676757).length < 2 ^ (prefixWord ++ tailWord_7676757).sum := by decide
  have hdescent : baseEnd_7676757 < baseStart_7676757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676760 : List Nat := [2, 1, 2, 2, 1, 1, 1, 4, 9]
def baseStart_7676760 : Nat := 118140960795 + 7676760 * 2 ^ 59
def prefixEnd_7676760 : Nat := 4983230072969 + 3 ^ 40 * 7676760 * 2
def baseEnd_7676760 : Nat := 437985305467721097210581

theorem tailTrace_7676760 : CollatzResearch.WordTrace tailWord_7676760 prefixEnd_7676760 437985305467721097210581 := by
  unfold tailWord_7676760
  simp only [CollatzResearch.WordTrace]
  refine ⟨139997219834208540536101867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186662959778944720714802489 139997219834208540536101867)
  ·
    refine ⟨209995829751312810804152801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139997219834208540536101867 209995829751312810804152801)
    ·
      refine ⟨157496872313484608103114601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 209995829751312810804152801 157496872313484608103114601)
      ·
        refine ⟨118122654235113456077335951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157496872313484608103114601 118122654235113456077335951)
        ·
          refine ⟨177183981352670184116003927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118122654235113456077335951 177183981352670184116003927)
          ·
            refine ⟨265775972029005276174005891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177183981352670184116003927 265775972029005276174005891)
            ·
              refine ⟨398663958043507914261008837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265775972029005276174005891 398663958043507914261008837)
              ·
                refine ⟨74749492133157733923939157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 398663958043507914261008837 74749492133157733923939157)
                ·
                  refine ⟨437985305467721097210581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74749492133157733923939157 437985305467721097210581)
                  ·
                    rfl

theorem cell23_7676760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 9].length) (baseStart_7676760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676760 prefixEnd_7676760 := by exact prefixLift 7676760
  have htrace : WordTrace (prefixWord ++ tailWord_7676760) baseStart_7676760 baseEnd_7676760 := by
    simpa [prefixWord, tailWord_7676760, baseEnd_7676760] using wordTrace_append hprefix tailTrace_7676760
  have hstable : (prefixWord ++ tailWord_7676760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676760).length < 2 ^ (prefixWord ++ tailWord_7676760).sum := by decide
  have hdescent : baseEnd_7676760 < baseStart_7676760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676771 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 4, 2, 2]
def baseStart_7676771 : Nat := 118140960795 + 7676771 * 2 ^ 59
def prefixEnd_7676771 : Nat := 4983230072969 + 3 ^ 40 * 7676771 * 2
def baseEnd_7676771 : Nat := 3941873397496689331857679

theorem tailTrace_7676771 : CollatzResearch.WordTrace tailWord_7676771 prefixEnd_7676771 3941873397496689331857679 := by
  unfold tailWord_7676771
  simp only [CollatzResearch.WordTrace]
  refine ⟨279994840871377229950854167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186663227247584819967236111 279994840871377229950854167)
  ·
    refine ⟨419992261307065844926281251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279994840871377229950854167 419992261307065844926281251)
    ·
      refine ⟨629988391960598767389421877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419992261307065844926281251 629988391960598767389421877)
      ·
        refine ⟨59061411746306134442758301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 629988391960598767389421877 59061411746306134442758301)
        ·
          refine ⟨22148029404864800416034363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59061411746306134442758301 22148029404864800416034363)
          ·
            refine ⟨33222044107297200624051545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22148029404864800416034363 33222044107297200624051545)
            ·
              refine ⟨24916533080472900468038659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33222044107297200624051545 24916533080472900468038659)
              ·
                refine ⟨37374799620709350702057989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24916533080472900468038659 37374799620709350702057989)
                ·
                  refine ⟨7007774928883003256635873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37374799620709350702057989 7007774928883003256635873)
                  ·
                    refine ⟨5255831196662252442476905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7007774928883003256635873 5255831196662252442476905)
                    ·
                      refine ⟨3941873397496689331857679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255831196662252442476905 3941873397496689331857679)
                      ·
                        rfl

theorem cell23_7676771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 4, 2, 2].length) (baseStart_7676771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676771 prefixEnd_7676771 := by exact prefixLift 7676771
  have htrace : WordTrace (prefixWord ++ tailWord_7676771) baseStart_7676771 baseEnd_7676771 := by
    simpa [prefixWord, tailWord_7676771, baseEnd_7676771] using wordTrace_append hprefix tailTrace_7676771
  have hstable : (prefixWord ++ tailWord_7676771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676771).length < 2 ^ (prefixWord ++ tailWord_7676771).sum := by decide
  have hdescent : baseEnd_7676771 < baseStart_7676771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676782 : List Nat := [4, 1, 2, 3, 3, 1, 2, 1, 2, 1, 3]
def baseStart_7676782 : Nat := 118140960795 + 7676782 * 2 ^ 59
def prefixEnd_7676782 : Nat := 4983230072969 + 3 ^ 40 * 7676782 * 2
def baseEnd_7676782 : Nat := 3941879045783888788820129

theorem tailTrace_7676782 : CollatzResearch.WordTrace tailWord_7676782 prefixEnd_7676782 3941879045783888788820129 := by
  unfold tailWord_7676782
  simp only [CollatzResearch.WordTrace]
  refine ⟨34999405259292172353688075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186663494716224919219669733 34999405259292172353688075)
  ·
    refine ⟨52499107888938258530532113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34999405259292172353688075 52499107888938258530532113)
    ·
      refine ⟨39374330916703693897899085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52499107888938258530532113 39374330916703693897899085)
      ·
        refine ⟨14765374093763885211712157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39374330916703693897899085 14765374093763885211712157)
        ·
          refine ⟨5537015285161456954392059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14765374093763885211712157 5537015285161456954392059)
          ·
            refine ⟨8305522927742185431588089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5537015285161456954392059 8305522927742185431588089)
            ·
              refine ⟨6229142195806639073691067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8305522927742185431588089 6229142195806639073691067)
              ·
                refine ⟨9343713293709958610536601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6229142195806639073691067 9343713293709958610536601)
                ·
                  refine ⟨7007784970282468957902451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9343713293709958610536601 7007784970282468957902451)
                  ·
                    refine ⟨10511677455423703436853677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7007784970282468957902451 10511677455423703436853677)
                    ·
                      refine ⟨3941879045783888788820129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10511677455423703436853677 3941879045783888788820129)
                      ·
                        rfl

theorem cell23_7676782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_7676782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676782 prefixEnd_7676782 := by exact prefixLift 7676782
  have htrace : WordTrace (prefixWord ++ tailWord_7676782) baseStart_7676782 baseEnd_7676782 := by
    simpa [prefixWord, tailWord_7676782, baseEnd_7676782] using wordTrace_append hprefix tailTrace_7676782
  have hstable : (prefixWord ++ tailWord_7676782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676782).length < 2 ^ (prefixWord ++ tailWord_7676782).sum := by decide
  have hdescent : baseEnd_7676782 < baseStart_7676782 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676787 : List Nat := [1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 3]
def baseStart_7676787 : Nat := 118140960795 + 7676787 * 2 ^ 59
def prefixEnd_7676787 : Nat := 4983230072969 + 3 ^ 40 * 7676787 * 2
def baseEnd_7676787 : Nat := 3941881613187161269257605

theorem tailTrace_7676787 : CollatzResearch.WordTrace tailWord_7676787 prefixEnd_7676787 3941881613187161269257605 := by
  unfold tailWord_7676787
  simp only [CollatzResearch.WordTrace]
  refine ⟨279995424439319264683436615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186663616292879509788957743 279995424439319264683436615)
  ·
    refine ⟨419993136658978897025154923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279995424439319264683436615 419993136658978897025154923)
    ·
      refine ⟨629989704988468345537732385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 419993136658978897025154923 629989704988468345537732385)
      ·
        refine ⟨472492278741351259153299289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 629989704988468345537732385 472492278741351259153299289)
        ·
          refine ⟨354369209056013444364974467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472492278741351259153299289 354369209056013444364974467)
          ·
            refine ⟨531553813584020166547461701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354369209056013444364974467 531553813584020166547461701)
            ·
              refine ⟨99666340047003781227649069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 531553813584020166547461701 99666340047003781227649069)
              ·
                refine ⟨37374877517626417960368401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99666340047003781227649069 37374877517626417960368401)
                ·
                  refine ⟨28031158138219813470276301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37374877517626417960368401 28031158138219813470276301)
                  ·
                    refine ⟨10511684301832430051353613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28031158138219813470276301 10511684301832430051353613)
                    ·
                      refine ⟨3941881613187161269257605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10511684301832430051353613 3941881613187161269257605)
                      ·
                        rfl

theorem cell23_7676787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 3].length) (baseStart_7676787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676787 prefixEnd_7676787 := by exact prefixLift 7676787
  have htrace : WordTrace (prefixWord ++ tailWord_7676787) baseStart_7676787 baseEnd_7676787 := by
    simpa [prefixWord, tailWord_7676787, baseEnd_7676787] using wordTrace_append hprefix tailTrace_7676787
  have hstable : (prefixWord ++ tailWord_7676787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676787).length < 2 ^ (prefixWord ++ tailWord_7676787).sum := by decide
  have hdescent : baseEnd_7676787 < baseStart_7676787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676822 : List Nat := [5, 3, 1, 1, 1, 1, 1, 4, 2, 2, 2]
def baseStart_7676822 : Nat := 118140960795 + 7676822 * 2 ^ 59
def prefixEnd_7676822 : Nat := 4983230072969 + 3 ^ 40 * 7676822 * 2
def baseEnd_7676822 : Nat := 3941899585010068632319945

theorem tailTrace_7676822 : CollatzResearch.WordTrace tailWord_7676822 prefixEnd_7676822 3941899585010068632319945 := by
  unfold tailWord_7676822
  simp only [CollatzResearch.WordTrace]
  refine ⟨17499793812137029103810045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186664467329461643773973813 17499793812137029103810045)
  ·
    refine ⟨6562422679551385913928767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17499793812137029103810045 6562422679551385913928767)
    ·
      refine ⟨9843634019327078870893151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6562422679551385913928767 9843634019327078870893151)
      ·
        refine ⟨14765451028990618306339727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9843634019327078870893151 14765451028990618306339727)
        ·
          refine ⟨22148176543485927459509591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14765451028990618306339727 22148176543485927459509591)
          ·
            refine ⟨33222264815228891189264387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22148176543485927459509591 33222264815228891189264387)
            ·
              refine ⟨49833397222843336783896581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33222264815228891189264387 49833397222843336783896581)
              ·
                refine ⟨9343761979283125646980609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49833397222843336783896581 9343761979283125646980609)
                ·
                  refine ⟨7007821484462344235235457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9343761979283125646980609 7007821484462344235235457)
                  ·
                    refine ⟨5255866113346758176426593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7007821484462344235235457 5255866113346758176426593)
                    ·
                      refine ⟨3941899585010068632319945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255866113346758176426593 3941899585010068632319945)
                      ·
                        rfl

theorem cell23_7676822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_7676822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676822 prefixEnd_7676822 := by exact prefixLift 7676822
  have htrace : WordTrace (prefixWord ++ tailWord_7676822) baseStart_7676822 baseEnd_7676822 := by
    simpa [prefixWord, tailWord_7676822, baseEnd_7676822] using wordTrace_append hprefix tailTrace_7676822
  have hstable : (prefixWord ++ tailWord_7676822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676822).length < 2 ^ (prefixWord ++ tailWord_7676822).sum := by decide
  have hdescent : baseEnd_7676822 < baseStart_7676822 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676834 : List Nat := [3, 3, 1, 2, 2, 1, 2, 1, 1, 2, 5]
def baseStart_7676834 : Nat := 118140960795 + 7676834 * 2 ^ 59
def prefixEnd_7676834 : Nat := 4983230072969 + 3 ^ 40 * 7676834 * 2
def baseEnd_7676834 : Nat := 3941905746777922585369889

theorem tailTrace_7676834 : CollatzResearch.WordTrace tailWord_7676834 prefixEnd_7676834 3941905746777922585369889 := by
  unfold tailWord_7676834
  simp only [CollatzResearch.WordTrace]
  refine ⟨69999284667537247927599389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186664759113432661140265037 69999284667537247927599389)
  ·
    refine ⟨26249731750326467972849771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 69999284667537247927599389 26249731750326467972849771)
    ·
      refine ⟨39374597625489701959274657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26249731750326467972849771 39374597625489701959274657)
      ·
        refine ⟨29530948219117276469455993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39374597625489701959274657 29530948219117276469455993)
        ·
          refine ⟨22148211164337957352091995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29530948219117276469455993 22148211164337957352091995)
          ·
            refine ⟨33222316746506936028137993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22148211164337957352091995 33222316746506936028137993)
            ·
              refine ⟨24916737559880202021103495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33222316746506936028137993 24916737559880202021103495)
              ·
                refine ⟨37375106339820303031655243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24916737559880202021103495 37375106339820303031655243)
                ·
                  refine ⟨56062659509730454547482865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37375106339820303031655243 56062659509730454547482865)
                  ·
                    refine ⟨42046994632297840910612149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56062659509730454547482865 42046994632297840910612149)
                    ·
                      refine ⟨3941905746777922585369889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42046994632297840910612149 3941905746777922585369889)
                      ·
                        rfl

theorem cell23_7676834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_7676834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676834 prefixEnd_7676834 := by exact prefixLift 7676834
  have htrace : WordTrace (prefixWord ++ tailWord_7676834) baseStart_7676834 baseEnd_7676834 := by
    simpa [prefixWord, tailWord_7676834, baseEnd_7676834] using wordTrace_append hprefix tailTrace_7676834
  have hstable : (prefixWord ++ tailWord_7676834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676834).length < 2 ^ (prefixWord ++ tailWord_7676834).sum := by decide
  have hdescent : baseEnd_7676834 < baseStart_7676834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676844 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 2, 4, 2]
def baseStart_7676844 : Nat := 118140960795 + 7676844 * 2 ^ 59
def prefixEnd_7676844 : Nat := 4983230072969 + 3 ^ 40 * 7676844 * 2
def baseEnd_7676844 : Nat := 3941910881584467546244843

theorem tailTrace_7676844 : CollatzResearch.WordTrace tailWord_7676844 prefixEnd_7676844 3941910881584467546244843 := by
  unfold tailWord_7676844
  simp only [CollatzResearch.WordTrace]
  refine ⟨139998751700056381709130793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186665002266741842278841057 139998751700056381709130793)
  ·
    refine ⟨104999063775042286281848095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 139998751700056381709130793 104999063775042286281848095)
    ·
      refine ⟨157498595662563429422772143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 104999063775042286281848095 157498595662563429422772143)
      ·
        refine ⟨236247893493845144134158215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157498595662563429422772143 236247893493845144134158215)
        ·
          refine ⟨354371840240767716201237323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236247893493845144134158215 354371840240767716201237323)
          ·
            refine ⟨531557760361151574301855985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354371840240767716201237323 531557760361151574301855985)
            ·
              refine ⟨398668320270863680726391989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531557760361151574301855985 398668320270863680726391989)
              ·
                refine ⟨37375155025393470068099249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 398668320270863680726391989 37375155025393470068099249)
                ·
                  refine ⟨28031366269045102551074437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37375155025393470068099249 28031366269045102551074437)
                  ·
                    refine ⟨5255881175445956728326457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28031366269045102551074437 5255881175445956728326457)
                    ·
                      refine ⟨3941910881584467546244843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255881175445956728326457 3941910881584467546244843)
                      ·
                        rfl

theorem cell23_7676844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 4, 2].length) (baseStart_7676844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676844 prefixEnd_7676844 := by exact prefixLift 7676844
  have htrace : WordTrace (prefixWord ++ tailWord_7676844) baseStart_7676844 baseEnd_7676844 := by
    simpa [prefixWord, tailWord_7676844, baseEnd_7676844] using wordTrace_append hprefix tailTrace_7676844
  have hstable : (prefixWord ++ tailWord_7676844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676844).length < 2 ^ (prefixWord ++ tailWord_7676844).sum := by decide
  have hdescent : baseEnd_7676844 < baseStart_7676844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676864 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 3]
def baseStart_7676864 : Nat := 118140960795 + 7676864 * 2 ^ 59
def prefixEnd_7676864 : Nat := 4983230072969 + 3 ^ 40 * 7676864 * 2
def baseEnd_7676864 : Nat := 3941921151197557467994751

theorem tailTrace_7676864 : CollatzResearch.WordTrace tailWord_7676864 prefixEnd_7676864 3941921151197557467994751 := by
  unfold tailWord_7676864
  simp only [CollatzResearch.WordTrace]
  refine ⟨139999116430020153416994823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186665488573360204555993097 139999116430020153416994823)
  ·
    refine ⟨209998674645030230125492235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 139999116430020153416994823 209998674645030230125492235)
    ·
      refine ⟨314998011967545345188238353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 209998674645030230125492235 314998011967545345188238353)
      ·
        refine ⟨236248508975659008891178765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 314998011967545345188238353 236248508975659008891178765)
        ·
          refine ⟨88593190865872128334192037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236248508975659008891178765 88593190865872128334192037)
          ·
            refine ⟨16611223287351024062661007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88593190865872128334192037 16611223287351024062661007)
            ·
              refine ⟨24916834931026536093991511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16611223287351024062661007 24916834931026536093991511)
              ·
                refine ⟨37375252396539804140987267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24916834931026536093991511 37375252396539804140987267)
                ·
                  refine ⟨56062878594809706211480901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37375252396539804140987267 56062878594809706211480901)
                  ·
                    refine ⟨10511789736526819914652669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56062878594809706211480901 10511789736526819914652669)
                    ·
                      refine ⟨3941921151197557467994751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10511789736526819914652669 3941921151197557467994751)
                      ·
                        rfl

theorem cell23_7676864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_7676864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676864 prefixEnd_7676864 := by exact prefixLift 7676864
  have htrace : WordTrace (prefixWord ++ tailWord_7676864) baseStart_7676864 baseEnd_7676864 := by
    simpa [prefixWord, tailWord_7676864, baseEnd_7676864] using wordTrace_append hprefix tailTrace_7676864
  have hstable : (prefixWord ++ tailWord_7676864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676864).length < 2 ^ (prefixWord ++ tailWord_7676864).sum := by decide
  have hdescent : baseEnd_7676864 < baseStart_7676864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676871 : List Nat := [1, 1, 4, 1, 1, 2, 3, 5, 1, 4]
def baseStart_7676871 : Nat := 118140960795 + 7676871 * 2 ^ 59
def prefixEnd_7676871 : Nat := 4983230072969 + 3 ^ 40 * 7676871 * 2
def baseEnd_7676871 : Nat := 1313974915187379646869073

theorem tailTrace_7676871 : CollatzResearch.WordTrace tailWord_7676871 prefixEnd_7676871 1313974915187379646869073 := by
  unfold tailWord_7676871
  simp only [CollatzResearch.WordTrace]
  refine ⟨279998488171014947029494467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186665658780676631352996311 279998488171014947029494467)
  ·
    refine ⟨419997732256522420544241701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279998488171014947029494467 419997732256522420544241701)
    ·
      refine ⟨78749574798097953852045319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 419997732256522420544241701 78749574798097953852045319)
      ·
        refine ⟨118124362197146930778067979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78749574798097953852045319 118124362197146930778067979)
        ·
          refine ⟨177186543295720396167101969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118124362197146930778067979 177186543295720396167101969)
          ·
            refine ⟨132889907471790297125326477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177186543295720396167101969 132889907471790297125326477)
            ·
              refine ⟨49833715301921361421997429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132889907471790297125326477 49833715301921361421997429)
              ·
                refine ⟨4671910809555127633312259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49833715301921361421997429 4671910809555127633312259)
                ·
                  refine ⟨7007866214332691449968389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671910809555127633312259 7007866214332691449968389)
                  ·
                    refine ⟨1313974915187379646869073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7007866214332691449968389 1313974915187379646869073)
                    ·
                      rfl

theorem cell23_7676871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_7676871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676871 prefixEnd_7676871 := by exact prefixLift 7676871
  have htrace : WordTrace (prefixWord ++ tailWord_7676871) baseStart_7676871 baseEnd_7676871 := by
    simpa [prefixWord, tailWord_7676871, baseEnd_7676871] using wordTrace_append hprefix tailTrace_7676871
  have hstable : (prefixWord ++ tailWord_7676871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676871).length < 2 ^ (prefixWord ++ tailWord_7676871).sum := by decide
  have hdescent : baseEnd_7676871 < baseStart_7676871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676884 : List Nat := [2, 4, 1, 2, 1, 3, 1, 1, 8]
def baseStart_7676884 : Nat := 118140960795 + 7676884 * 2 ^ 59
def prefixEnd_7676884 : Nat := 4983230072969 + 3 ^ 40 * 7676884 * 2
def baseEnd_7676884 : Nat := 437992380090071932193851

theorem tailTrace_7676884 : CollatzResearch.WordTrace tailWord_7676884 prefixEnd_7676884 437992380090071932193851 := by
  unfold tailWord_7676884
  simp only [CollatzResearch.WordTrace]
  refine ⟨139999481159983925124858853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186665974879978566833145137 139999481159983925124858853)
  ·
    refine ⟨26249902717496985960911035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 139999481159983925124858853 26249902717496985960911035)
    ·
      refine ⟨39374854076245478941366553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26249902717496985960911035 39374854076245478941366553)
      ·
        refine ⟨29531140557184109206024915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39374854076245478941366553 29531140557184109206024915)
        ·
          refine ⟨44296710835776163809037373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29531140557184109206024915 44296710835776163809037373)
          ·
            refine ⟨16611266563416061428389015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44296710835776163809037373 16611266563416061428389015)
            ·
              refine ⟨24916899845124092142583523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16611266563416061428389015 24916899845124092142583523)
              ·
                refine ⟨37375349767686138213875285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24916899845124092142583523 37375349767686138213875285)
                ·
                  refine ⟨437992380090071932193851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37375349767686138213875285 437992380090071932193851)
                  ·
                    rfl

theorem cell23_7676884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 1, 8].length) (baseStart_7676884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676884 prefixEnd_7676884 := by exact prefixLift 7676884
  have htrace : WordTrace (prefixWord ++ tailWord_7676884) baseStart_7676884 baseEnd_7676884 := by
    simpa [prefixWord, tailWord_7676884, baseEnd_7676884] using wordTrace_append hprefix tailTrace_7676884
  have hstable : (prefixWord ++ tailWord_7676884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676884).length < 2 ^ (prefixWord ++ tailWord_7676884).sum := by decide
  have hdescent : baseEnd_7676884 < baseStart_7676884 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676911 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 3, 1, 3]
def baseStart_7676911 : Nat := 118140960795 + 7676911 * 2 ^ 59
def prefixEnd_7676911 : Nat := 4983230072969 + 3 ^ 40 * 7676911 * 2
def baseEnd_7676911 : Nat := 3941945284788318784107035

theorem tailTrace_7676911 : CollatzResearch.WordTrace tailWord_7676911 prefixEnd_7676911 3941945284788318784107035 := by
  unfold tailWord_7676911
  simp only [CollatzResearch.WordTrace]
  refine ⟨279999947090870033860950587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186666631393913355907300391 279999947090870033860950587)
  ·
    refine ⟨419999920636305050791425881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 279999947090870033860950587 419999920636305050791425881)
    ·
      refine ⟨314999940477228788093569411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 419999920636305050791425881 314999940477228788093569411)
      ·
        refine ⟨472499910715843182140354117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 314999940477228788093569411 472499910715843182140354117)
        ·
          refine ⟨88593733259220596651316397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 472499910715843182140354117 88593733259220596651316397)
          ·
            refine ⟨33222649972207723744243649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88593733259220596651316397 33222649972207723744243649)
            ·
              refine ⟨24916987479155792808182737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33222649972207723744243649 24916987479155792808182737)
              ·
                refine ⟨18687740609366844606137053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24916987479155792808182737 18687740609366844606137053)
                ·
                  refine ⟨7007902728512566727301395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18687740609366844606137053 7007902728512566727301395)
                  ·
                    refine ⟨10511854092768850090952093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7007902728512566727301395 10511854092768850090952093)
                    ·
                      refine ⟨3941945284788318784107035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10511854092768850090952093 3941945284788318784107035)
                      ·
                        rfl

theorem cell23_7676911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 3, 1, 3].length) (baseStart_7676911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676911 prefixEnd_7676911 := by exact prefixLift 7676911
  have htrace : WordTrace (prefixWord ++ tailWord_7676911) baseStart_7676911 baseEnd_7676911 := by
    simpa [prefixWord, tailWord_7676911, baseEnd_7676911] using wordTrace_append hprefix tailTrace_7676911
  have hstable : (prefixWord ++ tailWord_7676911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676911).length < 2 ^ (prefixWord ++ tailWord_7676911).sum := by decide
  have hdescent : baseEnd_7676911 < baseStart_7676911 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676921 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 2, 3, 2]
def baseStart_7676921 : Nat := 118140960795 + 7676921 * 2 ^ 59
def prefixEnd_7676921 : Nat := 4983230072969 + 3 ^ 40 * 7676921 * 2
def baseEnd_7676921 : Nat := 3941950419594863744981989

theorem tailTrace_7676921 : CollatzResearch.WordTrace tailWord_7676921 prefixEnd_7676921 3941950419594863744981989 := by
  unfold tailWord_7676921
  simp only [CollatzResearch.WordTrace]
  refine ⟨280000311820833805568814617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186666874547222537045876411 280000311820833805568814617)
  ·
    refine ⟨210000233865625354176610963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280000311820833805568814617 210000233865625354176610963)
    ·
      refine ⟨315000350798438031264916445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210000233865625354176610963 315000350798438031264916445)
      ·
        refine ⟨118125131549414261724343667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315000350798438031264916445 118125131549414261724343667)
        ·
          refine ⟨177187697324121392586515501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118125131549414261724343667 177187697324121392586515501)
          ·
            refine ⟨66445386496545522219943313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177187697324121392586515501 66445386496545522219943313)
            ·
              refine ⟨49834039872409141664957485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66445386496545522219943313 49834039872409141664957485)
              ·
                refine ⟨18687764952153428124359057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49834039872409141664957485 18687764952153428124359057)
                ·
                  refine ⟨14015823714115071093269293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18687764952153428124359057 14015823714115071093269293)
                  ·
                    refine ⟨5255933892793151659975985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14015823714115071093269293 5255933892793151659975985)
                    ·
                      refine ⟨3941950419594863744981989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255933892793151659975985 3941950419594863744981989)
                      ·
                        rfl

theorem cell23_7676921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 2, 3, 2].length) (baseStart_7676921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676921 prefixEnd_7676921 := by exact prefixLift 7676921
  have htrace : WordTrace (prefixWord ++ tailWord_7676921) baseStart_7676921 baseEnd_7676921 := by
    simpa [prefixWord, tailWord_7676921, baseEnd_7676921] using wordTrace_append hprefix tailTrace_7676921
  have hstable : (prefixWord ++ tailWord_7676921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676921).length < 2 ^ (prefixWord ++ tailWord_7676921).sum := by decide
  have hdescent : baseEnd_7676921 < baseStart_7676921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676938 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 2, 3, 2]
def baseStart_7676938 : Nat := 118140960795 + 7676938 * 2 ^ 59
def prefixEnd_7676938 : Nat := 4983230072969 + 3 ^ 40 * 7676938 * 2
def baseEnd_7676938 : Nat := 3941959148765990178469411

theorem tailTrace_7676938 : CollatzResearch.WordTrace tailWord_7676938 prefixEnd_7676938 3941959148765990178469411 := by
  unfold tailWord_7676938
  simp only [CollatzResearch.WordTrace]
  refine ⟨70000232965443054368045867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186667287907848144981455645 70000232965443054368045867)
  ·
    refine ⟨105000349448164581552068801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70000232965443054368045867 105000349448164581552068801)
    ·
      refine ⟨78750262086123436164051601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105000349448164581552068801 78750262086123436164051601)
      ·
        refine ⟨59062696564592577123038701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78750262086123436164051601 59062696564592577123038701)
        ·
          refine ⟨22148511211722216421139513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59062696564592577123038701 22148511211722216421139513)
          ·
            refine ⟨16611383408791662315854635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22148511211722216421139513 16611383408791662315854635)
            ·
              refine ⟨24917075113187493473781953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16611383408791662315854635 24917075113187493473781953)
              ·
                refine ⟨18687806334890620105336465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24917075113187493473781953 18687806334890620105336465)
                ·
                  refine ⟨14015854751167965079002349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18687806334890620105336465 14015854751167965079002349)
                  ·
                    refine ⟨5255945531687986904625881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14015854751167965079002349 5255945531687986904625881)
                    ·
                      refine ⟨3941959148765990178469411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255945531687986904625881 3941959148765990178469411)
                      ·
                        rfl

theorem cell23_7676938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_7676938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676938 prefixEnd_7676938 := by exact prefixLift 7676938
  have htrace : WordTrace (prefixWord ++ tailWord_7676938) baseStart_7676938 baseEnd_7676938 := by
    simpa [prefixWord, tailWord_7676938, baseEnd_7676938] using wordTrace_append hprefix tailTrace_7676938
  have hstable : (prefixWord ++ tailWord_7676938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676938).length < 2 ^ (prefixWord ++ tailWord_7676938).sum := by decide
  have hdescent : baseEnd_7676938 < baseStart_7676938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676954 : List Nat := [3, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5]
def baseStart_7676954 : Nat := 118140960795 + 7676954 * 2 ^ 59
def prefixEnd_7676954 : Nat := 4983230072969 + 3 ^ 40 * 7676954 * 2
def baseEnd_7676954 : Nat := 3941967364456462115869337

theorem tailTrace_7676954 : CollatzResearch.WordTrace tailWord_7676954 prefixEnd_7676954 3941967364456462115869337 := by
  unfold tailWord_7676954
  simp only [CollatzResearch.WordTrace]
  refine ⟨70000378857428563051191479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186667676953142834803177277 70000378857428563051191479)
  ·
    refine ⟨105000568286142844576787219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70000378857428563051191479 105000568286142844576787219)
    ·
      refine ⟨157500852429214266865180829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105000568286142844576787219 157500852429214266865180829)
      ·
        refine ⟨59062819660955350074442811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157500852429214266865180829 59062819660955350074442811)
        ·
          refine ⟨88594229491433025111664217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59062819660955350074442811 88594229491433025111664217)
          ·
            refine ⟨66445672118574768833748163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88594229491433025111664217 66445672118574768833748163)
            ·
              refine ⟨99668508177862153250622245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66445672118574768833748163 99668508177862153250622245)
              ·
                refine ⟨18687845283349153734491671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99668508177862153250622245 18687845283349153734491671)
                ·
                  refine ⟨28031767925023730601737507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18687845283349153734491671 28031767925023730601737507)
                  ·
                    refine ⟨42047651887535595902606261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28031767925023730601737507 42047651887535595902606261)
                    ·
                      refine ⟨3941967364456462115869337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42047651887535595902606261 3941967364456462115869337)
                      ·
                        rfl

theorem cell23_7676954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_7676954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676954 prefixEnd_7676954 := by exact prefixLift 7676954
  have htrace : WordTrace (prefixWord ++ tailWord_7676954) baseStart_7676954 baseEnd_7676954 := by
    simpa [prefixWord, tailWord_7676954, baseEnd_7676954] using wordTrace_append hprefix tailTrace_7676954
  have hstable : (prefixWord ++ tailWord_7676954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676954).length < 2 ^ (prefixWord ++ tailWord_7676954).sum := by decide
  have hdescent : baseEnd_7676954 < baseStart_7676954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676974 : List Nat := [4, 1, 3, 1, 1, 1, 1, 11]
def baseStart_7676974 : Nat := 118140960795 + 7676974 * 2 ^ 59
def prefixEnd_7676974 : Nat := 4983230072969 + 3 ^ 40 * 7676974 * 2
def baseEnd_7676974 : Nat := 145999171632205631022935

theorem tailTrace_7676974 : CollatzResearch.WordTrace tailWord_7676974 prefixEnd_7676974 145999171632205631022935 := by
  unfold tailWord_7676974
  simp only [CollatzResearch.WordTrace]
  refine ⟨35000280611205224452561747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186668163259761197080329317 35000280611205224452561747)
  ·
    refine ⟨52500420916807836678842621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35000280611205224452561747 52500420916807836678842621)
    ·
      refine ⟨19687657843802938754565983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52500420916807836678842621 19687657843802938754565983)
      ·
        refine ⟨29531486765704408131848975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19687657843802938754565983 29531486765704408131848975)
        ·
          refine ⟨44297230148556612197773463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29531486765704408131848975 44297230148556612197773463)
          ·
            refine ⟨66445845222834918296660195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44297230148556612197773463 66445845222834918296660195)
            ·
              refine ⟨99668767834252377444990293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66445845222834918296660195 99668767834252377444990293)
              ·
                refine ⟨145999171632205631022935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 99668767834252377444990293 145999171632205631022935)
                ·
                  rfl

theorem cell23_7676974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 11].length) (baseStart_7676974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676974 prefixEnd_7676974 := by exact prefixLift 7676974
  have htrace : WordTrace (prefixWord ++ tailWord_7676974) baseStart_7676974 baseEnd_7676974 := by
    simpa [prefixWord, tailWord_7676974, baseEnd_7676974] using wordTrace_append hprefix tailTrace_7676974
  have hstable : (prefixWord ++ tailWord_7676974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676974).length < 2 ^ (prefixWord ++ tailWord_7676974).sum := by decide
  have hdescent : baseEnd_7676974 < baseStart_7676974 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7676987 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 3, 9]
def baseStart_7676987 : Nat := 118140960795 + 7676987 * 2 ^ 59
def prefixEnd_7676987 : Nat := 4983230072969 + 3 ^ 40 * 7676987 * 2
def baseEnd_7676987 : Nat := 1313994769772686828918895

theorem tailTrace_7676987 : CollatzResearch.WordTrace tailWord_7676987 prefixEnd_7676987 1313994769772686828918895 := by
  unfold tailWord_7676987
  simp only [CollatzResearch.WordTrace]
  refine ⟨280002719038594698840717215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186668479359063132560478143 280002719038594698840717215)
  ·
    refine ⟨420004078557892048261075823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280002719038594698840717215 420004078557892048261075823)
    ·
      refine ⟨630006117836838072391613735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420004078557892048261075823 630006117836838072391613735)
      ·
        refine ⟨945009176755257108587420603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630006117836838072391613735 945009176755257108587420603)
        ·
          refine ⟨1417513765132885662881130905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945009176755257108587420603 1417513765132885662881130905)
          ·
            refine ⟨1063135323849664247160848179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1417513765132885662881130905 1063135323849664247160848179)
            ·
              refine ⟨1594702985774496370741272269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063135323849664247160848179 1594702985774496370741272269)
              ·
                refine ⟨598013619665436139027977101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1594702985774496370741272269 598013619665436139027977101)
                ·
                  refine ⟨224255107374538552135491413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 598013619665436139027977101 224255107374538552135491413)
                  ·
                    refine ⟨1313994769772686828918895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 224255107374538552135491413 1313994769772686828918895)
                    ·
                      rfl

theorem cell23_7676987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 9].length) (baseStart_7676987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7676987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7676987 prefixEnd_7676987 := by exact prefixLift 7676987
  have htrace : WordTrace (prefixWord ++ tailWord_7676987) baseStart_7676987 baseEnd_7676987 := by
    simpa [prefixWord, tailWord_7676987, baseEnd_7676987] using wordTrace_append hprefix tailTrace_7676987
  have hstable : (prefixWord ++ tailWord_7676987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7676987).length < 2 ^ (prefixWord ++ tailWord_7676987).sum := by decide
  have hdescent : baseEnd_7676987 < baseStart_7676987 := by decide
  rcases family_descends (prefixWord ++ tailWord_7676987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677002 : List Nat := [3, 1, 2, 1, 1, 2, 6, 2, 1, 2, 2]
def baseStart_7677002 : Nat := 118140960795 + 7677002 * 2 ^ 59
def prefixEnd_7677002 : Nat := 4983230072969 + 3 ^ 40 * 7677002 * 2
def baseEnd_7677002 : Nat := 3941992011527877928069117

theorem tailTrace_7677002 : CollatzResearch.WordTrace tailWord_7677002 prefixEnd_7677002 3941992011527877928069117 := by
  unfold tailWord_7677002
  simp only [CollatzResearch.WordTrace]
  refine ⟨70000816533385089100628315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186668844089026904268342173 70000816533385089100628315)
  ·
    refine ⟨105001224800077633650942473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70000816533385089100628315 105001224800077633650942473)
    ·
      refine ⟨78750918600058225238206855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105001224800077633650942473 78750918600058225238206855)
      ·
        refine ⟨118126377900087337857310283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78750918600058225238206855 118126377900087337857310283)
        ·
          refine ⟨177189566850131006785965425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118126377900087337857310283 177189566850131006785965425)
          ·
            refine ⟨132892175137598255089474069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177189566850131006785965425 132892175137598255089474069)
            ·
              refine ⟨6229320709574918207319097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 132892175137598255089474069 6229320709574918207319097)
              ·
                refine ⟨4671990532181188655489323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6229320709574918207319097 4671990532181188655489323)
                ·
                  refine ⟨7007985798271782983233985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4671990532181188655489323 7007985798271782983233985)
                  ·
                    refine ⟨5255989348703837237425489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7007985798271782983233985 5255989348703837237425489)
                    ·
                      refine ⟨3941992011527877928069117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255989348703837237425489 3941992011527877928069117)
                      ·
                        rfl

theorem cell23_7677002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_7677002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677002 prefixEnd_7677002 := by exact prefixLift 7677002
  have htrace : WordTrace (prefixWord ++ tailWord_7677002) baseStart_7677002 baseEnd_7677002 := by
    simpa [prefixWord, tailWord_7677002, baseEnd_7677002] using wordTrace_append hprefix tailTrace_7677002
  have hstable : (prefixWord ++ tailWord_7677002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677002).length < 2 ^ (prefixWord ++ tailWord_7677002).sum := by decide
  have hdescent : baseEnd_7677002 < baseStart_7677002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677011 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 3, 3, 2]
def baseStart_7677011 : Nat := 118140960795 + 7677011 * 2 ^ 59
def prefixEnd_7677011 : Nat := 4983230072969 + 3 ^ 40 * 7677011 * 2
def baseEnd_7677011 : Nat := 3941996632853768392856575

theorem tailTrace_7677011 : CollatzResearch.WordTrace tailWord_7677011 prefixEnd_7677011 3941996632853768392856575 := by
  unfold tailWord_7677011
  simp only [CollatzResearch.WordTrace]
  refine ⟨280003594390507750939590887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186669062927005167293060591 280003594390507750939590887)
  ·
    refine ⟨420005391585761626409386331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280003594390507750939590887 420005391585761626409386331)
    ·
      refine ⟨630008087378642439614079497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420005391585761626409386331 630008087378642439614079497)
      ·
        refine ⟨472506065533981829710559623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630008087378642439614079497 472506065533981829710559623)
        ·
          refine ⟨708759098300972744565839435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472506065533981829710559623 708759098300972744565839435)
          ·
            refine ⟨1063138647451459116848759153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708759098300972744565839435 1063138647451459116848759153)
            ·
              refine ⟨797353985588594337636569365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1063138647451459116848759153 797353985588594337636569365)
              ·
                refine ⟨37375968074465359576714189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 797353985588594337636569365 37375968074465359576714189)
                ·
                  refine ⟨14015988027924509841267821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37375968074465359576714189 14015988027924509841267821)
                  ·
                    refine ⟨5255995510471691190475433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14015988027924509841267821 5255995510471691190475433)
                    ·
                      refine ⟨3941996632853768392856575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5255995510471691190475433 3941996632853768392856575)
                      ·
                        rfl

theorem cell23_7677011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 3, 3, 2].length) (baseStart_7677011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677011 prefixEnd_7677011 := by exact prefixLift 7677011
  have htrace : WordTrace (prefixWord ++ tailWord_7677011) baseStart_7677011 baseEnd_7677011 := by
    simpa [prefixWord, tailWord_7677011, baseEnd_7677011] using wordTrace_append hprefix tailTrace_7677011
  have hstable : (prefixWord ++ tailWord_7677011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677011).length < 2 ^ (prefixWord ++ tailWord_7677011).sum := by decide
  have hdescent : baseEnd_7677011 < baseStart_7677011 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677024 : List Nat := [2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 4]
def baseStart_7677024 : Nat := 118140960795 + 7677024 * 2 ^ 59
def prefixEnd_7677024 : Nat := 4983230072969 + 3 ^ 40 * 7677024 * 2
def baseEnd_7677024 : Nat := 3942003308102276841994015

theorem tailTrace_7677024 : CollatzResearch.WordTrace tailWord_7677024 prefixEnd_7677024 3942003308102276841994015 := by
  unfold tailWord_7677024
  simp only [CollatzResearch.WordTrace]
  refine ⟨140002034269730327079907063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186669379026307102773209417 140002034269730327079907063)
  ·
    refine ⟨210003051404595490619860595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140002034269730327079907063 210003051404595490619860595)
    ·
      refine ⟨315004577106893235929790893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210003051404595490619860595 315004577106893235929790893)
      ·
        refine ⟨118126716415084963473671585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315004577106893235929790893 118126716415084963473671585)
        ·
          refine ⟨88595037311313722605253689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118126716415084963473671585 88595037311313722605253689)
          ·
            refine ⟨66446277983485291953940267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88595037311313722605253689 66446277983485291953940267)
            ·
              refine ⟨99669416975227937930910401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66446277983485291953940267 99669416975227937930910401)
              ·
                refine ⟨74752062731420953448182801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99669416975227937930910401 74752062731420953448182801)
                ·
                  refine ⟨56064047048565715086137101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74752062731420953448182801 56064047048565715086137101)
                  ·
                    refine ⟨21024017643212143157301413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56064047048565715086137101 21024017643212143157301413)
                    ·
                      refine ⟨3942003308102276841994015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21024017643212143157301413 3942003308102276841994015)
                      ·
                        rfl

theorem cell23_7677024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_7677024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677024 prefixEnd_7677024 := by exact prefixLift 7677024
  have htrace : WordTrace (prefixWord ++ tailWord_7677024) baseStart_7677024 baseEnd_7677024 := by
    simpa [prefixWord, tailWord_7677024, baseEnd_7677024] using wordTrace_append hprefix tailTrace_7677024
  have hstable : (prefixWord ++ tailWord_7677024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677024).length < 2 ^ (prefixWord ++ tailWord_7677024).sum := by decide
  have hdescent : baseEnd_7677024 < baseStart_7677024 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677028 : List Nat := [2, 3, 1, 1, 2, 1, 1, 6, 1, 3, 2]
def baseStart_7677028 : Nat := 118140960795 + 7677028 * 2 ^ 59
def prefixEnd_7677028 : Nat := 4983230072969 + 3 ^ 40 * 7677028 * 2
def baseEnd_7677028 : Nat := 3942005362024894826343997

theorem tailTrace_7677028 : CollatzResearch.WordTrace tailWord_7677028 prefixEnd_7677028 3942005362024894826343997 := by
  unfold tailWord_7677028
  simp only [CollatzResearch.WordTrace]
  refine ⟨140002107215723081421479869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186669476287630775228639825 140002107215723081421479869)
  ·
    refine ⟨52500790205896155533054951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140002107215723081421479869 52500790205896155533054951)
    ·
      refine ⟨78751185308844233299582427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52500790205896155533054951 78751185308844233299582427)
      ·
        refine ⟨118126777963266349949373641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78751185308844233299582427 118126777963266349949373641)
        ·
          refine ⟨88595083472449762462030231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118126777963266349949373641 88595083472449762462030231)
          ·
            refine ⟨132892625208674643693045347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88595083472449762462030231 132892625208674643693045347)
            ·
              refine ⟨199338937813011965539568021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132892625208674643693045347 199338937813011965539568021)
              ·
                refine ⟨9344012709984935884667251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 199338937813011965539568021 9344012709984935884667251)
                ·
                  refine ⟨14016019064977403827000877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9344012709984935884667251 14016019064977403827000877)
                  ·
                    refine ⟨5256007149366526435125329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14016019064977403827000877 5256007149366526435125329)
                    ·
                      refine ⟨3942005362024894826343997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5256007149366526435125329 3942005362024894826343997)
                      ·
                        rfl

theorem cell23_7677028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 1, 3, 2].length) (baseStart_7677028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677028 prefixEnd_7677028 := by exact prefixLift 7677028
  have htrace : WordTrace (prefixWord ++ tailWord_7677028) baseStart_7677028 baseEnd_7677028 := by
    simpa [prefixWord, tailWord_7677028, baseEnd_7677028] using wordTrace_append hprefix tailTrace_7677028
  have hstable : (prefixWord ++ tailWord_7677028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677028).length < 2 ^ (prefixWord ++ tailWord_7677028).sum := by decide
  have hdescent : baseEnd_7677028 < baseStart_7677028 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677041 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 3, 4, 2]
def baseStart_7677041 : Nat := 118140960795 + 7677041 * 2 ^ 59
def prefixEnd_7677041 : Nat := 4983230072969 + 3 ^ 40 * 7677041 * 2
def baseEnd_7677041 : Nat := 3942012037273403275481437

theorem tailTrace_7677041 : CollatzResearch.WordTrace tailWord_7677041 prefixEnd_7677041 3942012037273403275481437 := by
  unfold tailWord_7677041
  simp only [CollatzResearch.WordTrace]
  refine ⟨280004688580399066063182977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186669792386932710708788651 280004688580399066063182977)
  ·
    refine ⟨210003516435299299547387233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280004688580399066063182977 210003516435299299547387233)
    ·
      refine ⟨157502637326474474660540425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210003516435299299547387233 157502637326474474660540425)
      ·
        refine ⟨118126977994855855995405319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157502637326474474660540425 118126977994855855995405319)
        ·
          refine ⟨177190466992283783993107979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118126977994855855995405319 177190466992283783993107979)
          ·
            refine ⟨265785700488425675989661969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177190466992283783993107979 265785700488425675989661969)
            ·
              refine ⟨199339275366319256992246477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265785700488425675989661969 199339275366319256992246477)
              ·
                refine ⟨74752228262369721372092429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199339275366319256992246477 74752228262369721372092429)
                ·
                  refine ⟨28032085598388645514534661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74752228262369721372092429 28032085598388645514534661)
                  ·
                    refine ⟨5256016049697871033975249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28032085598388645514534661 5256016049697871033975249)
                    ·
                      refine ⟨3942012037273403275481437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5256016049697871033975249 3942012037273403275481437)
                      ·
                        rfl

theorem cell23_7677041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_7677041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677041 prefixEnd_7677041 := by exact prefixLift 7677041
  have htrace : WordTrace (prefixWord ++ tailWord_7677041) baseStart_7677041 baseEnd_7677041 := by
    simpa [prefixWord, tailWord_7677041, baseEnd_7677041] using wordTrace_append hprefix tailTrace_7677041
  have hstable : (prefixWord ++ tailWord_7677041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677041).length < 2 ^ (prefixWord ++ tailWord_7677041).sum := by decide
  have hdescent : baseEnd_7677041 < baseStart_7677041 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677104 : List Nat := [2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 5]
def baseStart_7677104 : Nat := 118140960795 + 7677104 * 2 ^ 59
def prefixEnd_7677104 : Nat := 4983230072969 + 3 ^ 40 * 7677104 * 2
def baseEnd_7677104 : Nat := 3942044386554636528993647

theorem tailTrace_7677104 : CollatzResearch.WordTrace tailWord_7677104 prefixEnd_7677104 3942044386554636528993647 := by
  unfold tailWord_7677104
  simp only [CollatzResearch.WordTrace]
  refine ⟨140003493189585413911363183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186671324252780551881817577 140003493189585413911363183)
  ·
    refine ⟨210005239784378120867044775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140003493189585413911363183 210005239784378120867044775)
    ·
      refine ⟨315007859676567181300567163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210005239784378120867044775 315007859676567181300567163)
      ·
        refine ⟨472511789514850771950850745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315007859676567181300567163 472511789514850771950850745)
        ·
          refine ⟨354383842136138078963138059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472511789514850771950850745 354383842136138078963138059)
          ·
            refine ⟨531575763204207118444707089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354383842136138078963138059 531575763204207118444707089)
            ·
              refine ⟨398681822403155338833530317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531575763204207118444707089 398681822403155338833530317)
              ·
                refine ⟨149505683401183252062573869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 398681822403155338833530317 149505683401183252062573869)
                ·
                  refine ⟨56064631275443719523465201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149505683401183252062573869 56064631275443719523465201)
                  ·
                    refine ⟨42048473456582789642598901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56064631275443719523465201 42048473456582789642598901)
                    ·
                      refine ⟨3942044386554636528993647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42048473456582789642598901 3942044386554636528993647)
                      ·
                        rfl

theorem cell23_7677104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_7677104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677104 prefixEnd_7677104 := by exact prefixLift 7677104
  have htrace : WordTrace (prefixWord ++ tailWord_7677104) baseStart_7677104 baseEnd_7677104 := by
    simpa [prefixWord, tailWord_7677104, baseEnd_7677104] using wordTrace_append hprefix tailTrace_7677104
  have hstable : (prefixWord ++ tailWord_7677104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677104).length < 2 ^ (prefixWord ++ tailWord_7677104).sum := by decide
  have hdescent : baseEnd_7677104 < baseStart_7677104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677111 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 2, 5]
def baseStart_7677111 : Nat := 118140960795 + 7677111 * 2 ^ 59
def prefixEnd_7677111 : Nat := 4983230072969 + 3 ^ 40 * 7677111 * 2
def baseEnd_7677111 : Nat := 1314015993639739333868705

theorem tailTrace_7677111 : CollatzResearch.WordTrace tailWord_7677111 prefixEnd_7677111 1314015993639739333868705 := by
  unfold tailWord_7677111
  simp only [CollatzResearch.WordTrace]
  refine ⟨280007241690145468018231187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186671494460096978678820791 280007241690145468018231187)
  ·
    refine ⟨420010862535218202027346781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280007241690145468018231187 420010862535218202027346781)
    ·
      refine ⟨157504073450706825760255043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420010862535218202027346781 157504073450706825760255043)
      ·
        refine ⟨236256110176060238640382565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157504073450706825760255043 236256110176060238640382565)
        ·
          refine ⟨44298020658011294745071731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 236256110176060238640382565 44298020658011294745071731)
          ·
            refine ⟨66447030987016942117607597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44298020658011294745071731 66447030987016942117607597)
            ·
              refine ⟨24917636620131353294102849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66447030987016942117607597 24917636620131353294102849)
              ·
                refine ⟨18688227465098514970577137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24917636620131353294102849 18688227465098514970577137)
                ·
                  refine ⟨14016170598823886227932853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18688227465098514970577137 14016170598823886227932853)
                  ·
                    refine ⟨1314015993639739333868705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14016170598823886227932853 1314015993639739333868705)
                    ·
                      rfl

theorem cell23_7677111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_7677111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677111 prefixEnd_7677111 := by exact prefixLift 7677111
  have htrace : WordTrace (prefixWord ++ tailWord_7677111) baseStart_7677111 baseEnd_7677111 := by
    simpa [prefixWord, tailWord_7677111, baseEnd_7677111] using wordTrace_append hprefix tailTrace_7677111
  have hstable : (prefixWord ++ tailWord_7677111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677111).length < 2 ^ (prefixWord ++ tailWord_7677111).sum := by decide
  have hdescent : baseEnd_7677111 < baseStart_7677111 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677151 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 3]
def baseStart_7677151 : Nat := 118140960795 + 7677151 * 2 ^ 59
def prefixEnd_7677151 : Nat := 4983230072969 + 3 ^ 40 * 7677151 * 2
def baseEnd_7677151 : Nat := 3942068520145397845105931

theorem tailTrace_7677151 : CollatzResearch.WordTrace tailWord_7677151 prefixEnd_7677151 3942068520145397845105931 := by
  unfold tailWord_7677151
  simp only [CollatzResearch.WordTrace]
  refine ⟨280008700610000554849687307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186672467073333703233124871 280008700610000554849687307)
  ·
    refine ⟨420013050915000832274530961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280008700610000554849687307 420013050915000832274530961)
    ·
      refine ⟨315009788186250624205898221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420013050915000832274530961 315009788186250624205898221)
      ·
        refine ⟨118128670569843984077211833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315009788186250624205898221 118128670569843984077211833)
        ·
          refine ⟨88596502927382988057908875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118128670569843984077211833 88596502927382988057908875)
          ·
            refine ⟨132894754391074482086863313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88596502927382988057908875 132894754391074482086863313)
            ·
              refine ⟨99671065793305861565147485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132894754391074482086863313 99671065793305861565147485)
              ·
                refine ⟨37376649672489698086930307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99671065793305861565147485 37376649672489698086930307)
                ·
                  refine ⟨56064974508734547130395461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37376649672489698086930307 56064974508734547130395461)
                  ·
                    refine ⟨10512182720387727586949149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56064974508734547130395461 10512182720387727586949149)
                    ·
                      refine ⟨3942068520145397845105931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10512182720387727586949149 3942068520145397845105931)
                      ·
                        rfl

theorem cell23_7677151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_7677151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677151 prefixEnd_7677151 := by exact prefixLift 7677151
  have htrace : WordTrace (prefixWord ++ tailWord_7677151) baseStart_7677151 baseEnd_7677151 := by
    simpa [prefixWord, tailWord_7677151, baseEnd_7677151] using wordTrace_append hprefix tailTrace_7677151
  have hstable : (prefixWord ++ tailWord_7677151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677151).length < 2 ^ (prefixWord ++ tailWord_7677151).sum := by decide
  have hdescent : baseEnd_7677151 < baseStart_7677151 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677171 : List Nat := [1, 1, 1, 2, 2, 5, 1, 4, 6]
def baseStart_7677171 : Nat := 118140960795 + 7677171 * 2 ^ 59
def prefixEnd_7677171 : Nat := 4983230072969 + 3 ^ 40 * 7677171 * 2
def baseEnd_7677171 : Nat := 438008754417609751872871

theorem tailTrace_7677171 : CollatzResearch.WordTrace tailWord_7677171 prefixEnd_7677171 438008754417609751872871 := by
  unfold tailWord_7677171
  simp only [CollatzResearch.WordTrace]
  refine ⟨280009430069928098265415367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186672953379952065510276911 280009430069928098265415367)
  ·
    refine ⟨420014145104892147398123051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280009430069928098265415367 420014145104892147398123051)
    ·
      refine ⟨630021217657338221097184577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420014145104892147398123051 630021217657338221097184577)
      ·
        refine ⟨472515913243003665822888433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630021217657338221097184577 472515913243003665822888433)
        ·
          refine ⟨354386934932252749367166325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472515913243003665822888433 354386934932252749367166325)
          ·
            refine ⟨33223775149898695253171843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 354386934932252749367166325 33223775149898695253171843)
            ·
              refine ⟨49835662724848042879757765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33223775149898695253171843 49835662724848042879757765)
              ·
                refine ⟨9344186760909008039954581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49835662724848042879757765 9344186760909008039954581)
                ·
                  refine ⟨438008754417609751872871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9344186760909008039954581 438008754417609751872871)
                  ·
                    rfl

theorem cell23_7677171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 6].length) (baseStart_7677171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677171 prefixEnd_7677171 := by exact prefixLift 7677171
  have htrace : WordTrace (prefixWord ++ tailWord_7677171) baseStart_7677171 baseEnd_7677171 := by
    simpa [prefixWord, tailWord_7677171, baseEnd_7677171] using wordTrace_append hprefix tailTrace_7677171
  have hstable : (prefixWord ++ tailWord_7677171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677171).length < 2 ^ (prefixWord ++ tailWord_7677171).sum := by decide
  have hdescent : baseEnd_7677171 < baseStart_7677171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677181 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 4, 5, 3]
def baseStart_7677181 : Nat := 118140960795 + 7677181 * 2 ^ 59
def prefixEnd_7677181 : Nat := 4983230072969 + 3 ^ 40 * 7677181 * 2
def baseEnd_7677181 : Nat := 3942083924565032727730793

theorem tailTrace_7677181 : CollatzResearch.WordTrace tailWord_7677181 prefixEnd_7677181 3942083924565032727730793 := by
  unfold tailWord_7677181
  simp only [CollatzResearch.WordTrace]
  refine ⟨280009794799891869973279397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186673196533261246648852931 280009794799891869973279397)
  ·
    refine ⟨52501836524979725619989887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280009794799891869973279397 52501836524979725619989887)
    ·
      refine ⟨78752754787469588429984831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52501836524979725619989887 78752754787469588429984831)
      ·
        refine ⟨118129132181204382644977247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78752754787469588429984831 118129132181204382644977247)
        ·
          refine ⟨177193698271806573967465871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118129132181204382644977247 177193698271806573967465871)
          ·
            refine ⟨265790547407709860951198807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177193698271806573967465871 265790547407709860951198807)
            ·
              refine ⟨398685821111564791426798211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265790547407709860951198807 398685821111564791426798211)
              ·
                refine ⟨598028731667347187140197317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398685821111564791426798211 598028731667347187140197317)
                ·
                  refine ⟨112130387187627597588786997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 598028731667347187140197317 112130387187627597588786997)
                  ·
                    refine ⟨10512223798840087273948781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112130387187627597588786997 10512223798840087273948781)
                    ·
                      refine ⟨3942083924565032727730793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10512223798840087273948781 3942083924565032727730793)
                      ·
                        rfl

theorem cell23_7677181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_7677181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677181 prefixEnd_7677181 := by exact prefixLift 7677181
  have htrace : WordTrace (prefixWord ++ tailWord_7677181) baseStart_7677181 baseEnd_7677181 := by
    simpa [prefixWord, tailWord_7677181, baseEnd_7677181] using wordTrace_append hprefix tailTrace_7677181
  have hstable : (prefixWord ++ tailWord_7677181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677181).length < 2 ^ (prefixWord ++ tailWord_7677181).sum := by decide
  have hdescent : baseEnd_7677181 < baseStart_7677181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677188 : List Nat := [2, 3, 2, 2, 2, 1, 2, 3, 6]
def baseStart_7677188 : Nat := 118140960795 + 7677188 * 2 ^ 59
def prefixEnd_7677188 : Nat := 4983230072969 + 3 ^ 40 * 7677188 * 2
def baseEnd_7677188 : Nat := 438009724325512688927029

theorem tailTrace_7677188 : CollatzResearch.WordTrace tailWord_7677188 prefixEnd_7677188 438009724325512688927029 := by
  unfold tailWord_7677188
  simp only [CollatzResearch.WordTrace]
  refine ⟨140005025055433255084392109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186673366740577673445856145 140005025055433255084392109)
  ·
    refine ⟨52501884395787470656647041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140005025055433255084392109 52501884395787470656647041)
    ·
      refine ⟨39376413296840602992485281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52501884395787470656647041 39376413296840602992485281)
      ·
        refine ⟨29532309972630452244363961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39376413296840602992485281 29532309972630452244363961)
        ·
          refine ⟨22149232479472839183272971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29532309972630452244363961 22149232479472839183272971)
          ·
            refine ⟨33223848719209258774909457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22149232479472839183272971 33223848719209258774909457)
            ·
              refine ⟨24917886539406944081182093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33223848719209258774909457 24917886539406944081182093)
              ·
                refine ⟨9344207452277604030443285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24917886539406944081182093 9344207452277604030443285)
                ·
                  refine ⟨438009724325512688927029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9344207452277604030443285 438009724325512688927029)
                  ·
                    rfl

theorem cell23_7677188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_7677188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677188 prefixEnd_7677188 := by exact prefixLift 7677188
  have htrace : WordTrace (prefixWord ++ tailWord_7677188) baseStart_7677188 baseEnd_7677188 := by
    simpa [prefixWord, tailWord_7677188, baseEnd_7677188] using wordTrace_append hprefix tailTrace_7677188
  have hstable : (prefixWord ++ tailWord_7677188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677188).length < 2 ^ (prefixWord ++ tailWord_7677188).sum := by decide
  have hdescent : baseEnd_7677188 < baseStart_7677188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677201 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 3, 5]
def baseStart_7677201 : Nat := 118140960795 + 7677201 * 2 ^ 59
def prefixEnd_7677201 : Nat := 4983230072969 + 3 ^ 40 * 7677201 * 2
def baseEnd_7677201 : Nat := 1314031398059374216493567

theorem tailTrace_7677201 : CollatzResearch.WordTrace tailWord_7677201 prefixEnd_7677201 1314031398059374216493567 := by
  unfold tailWord_7677201
  simp only [CollatzResearch.WordTrace]
  refine ⟨280010524259819413389007457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186673682839879608926004971 280010524259819413389007457)
  ·
    refine ⟨210007893194864560041755593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280010524259819413389007457 210007893194864560041755593)
    ·
      refine ⟨157505919896148420031316695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210007893194864560041755593 157505919896148420031316695)
      ·
        refine ⟨236258879844222630046975043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157505919896148420031316695 236258879844222630046975043)
        ·
          refine ⟨354388319766333945070462565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236258879844222630046975043 354388319766333945070462565)
          ·
            refine ⟨66447809956187614700711731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 354388319766333945070462565 66447809956187614700711731)
            ·
              refine ⟨99671714934281422051067597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66447809956187614700711731 99671714934281422051067597)
              ·
                refine ⟨37376893100355533269150349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99671714934281422051067597 37376893100355533269150349)
                ·
                  refine ⟨14016334912633324975931381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37376893100355533269150349 14016334912633324975931381)
                  ·
                    refine ⟨1314031398059374216493567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14016334912633324975931381 1314031398059374216493567)
                    ·
                      rfl

theorem cell23_7677201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 5].length) (baseStart_7677201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677201 prefixEnd_7677201 := by exact prefixLift 7677201
  have htrace : WordTrace (prefixWord ++ tailWord_7677201) baseStart_7677201 baseEnd_7677201 := by
    simpa [prefixWord, tailWord_7677201, baseEnd_7677201] using wordTrace_append hprefix tailTrace_7677201
  have hstable : (prefixWord ++ tailWord_7677201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677201).length < 2 ^ (prefixWord ++ tailWord_7677201).sum := by decide
  have hdescent : baseEnd_7677201 < baseStart_7677201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677202 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_7677202 : Nat := 118140960795 + 7677202 * 2 ^ 59
def prefixEnd_7677202 : Nat := 4983230072969 + 3 ^ 40 * 7677202 * 2
def baseEnd_7677202 : Nat := 3942094707658777145568197

theorem tailTrace_7677202 : CollatzResearch.WordTrace tailWord_7677202 prefixEnd_7677202 3942094707658777145568197 := by
  unfold tailWord_7677202
  simp only [CollatzResearch.WordTrace]
  refine ⟨70002640183203947639948465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186673707155210527039862573 70002640183203947639948465)
  ·
    refine ⟨52501980137402960729961349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70002640183203947639948465 52501980137402960729961349)
    ·
      refine ⟨9844121275763055136867753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52501980137402960729961349 9844121275763055136867753)
      ·
        refine ⟨7383090956822291352650815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9844121275763055136867753 7383090956822291352650815)
        ·
          refine ⟨11074636435233437028976223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7383090956822291352650815 11074636435233437028976223)
          ·
            refine ⟨16611954652850155543464335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11074636435233437028976223 16611954652850155543464335)
            ·
              refine ⟨24917931979275233315196503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16611954652850155543464335 24917931979275233315196503)
              ·
                refine ⟨37376897968912849972794755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24917931979275233315196503 37376897968912849972794755)
                ·
                  refine ⟨56065346953369274959192133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37376897968912849972794755 56065346953369274959192133)
                  ·
                    refine ⟨10512252553756739054848525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56065346953369274959192133 10512252553756739054848525)
                    ·
                      refine ⟨3942094707658777145568197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10512252553756739054848525 3942094707658777145568197)
                      ·
                        rfl

theorem cell23_7677202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_7677202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677202 prefixEnd_7677202 := by exact prefixLift 7677202
  have htrace : WordTrace (prefixWord ++ tailWord_7677202) baseStart_7677202 baseEnd_7677202 := by
    simpa [prefixWord, tailWord_7677202, baseEnd_7677202] using wordTrace_append hprefix tailTrace_7677202
  have hstable : (prefixWord ++ tailWord_7677202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677202).length < 2 ^ (prefixWord ++ tailWord_7677202).sum := by decide
  have hdescent : baseEnd_7677202 < baseStart_7677202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677252 : List Nat := [2, 3, 4, 1, 1, 2, 2, 2, 1, 5]
def baseStart_7677252 : Nat := 118140960795 + 7677252 * 2 ^ 59
def prefixEnd_7677252 : Nat := 4983230072969 + 3 ^ 40 * 7677252 * 2
def baseEnd_7677252 : Nat := 1314040127230500649980989

theorem tailTrace_7677252 : CollatzResearch.WordTrace tailWord_7677252 prefixEnd_7677252 1314040127230500649980989 := by
  unfold tailWord_7677252
  simp only [CollatzResearch.WordTrace]
  refine ⟨140006192191317324549557005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186674922921756432732742673 140006192191317324549557005)
  ·
    refine ⟨52502322071743996706083877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140006192191317324549557005 52502322071743996706083877)
    ·
      refine ⟨9844185388451999382390727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52502322071743996706083877 9844185388451999382390727)
      ·
        refine ⟨14766278082677999073586091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9844185388451999382390727 14766278082677999073586091)
        ·
          refine ⟨22149417124016998610379137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14766278082677999073586091 22149417124016998610379137)
          ·
            refine ⟨16612062843012748957784353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22149417124016998610379137 16612062843012748957784353)
            ·
              refine ⟨12459047132259561718338265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16612062843012748957784353 12459047132259561718338265)
              ·
                refine ⟨9344285349194671288753699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12459047132259561718338265 9344285349194671288753699)
                ·
                  refine ⟨14016428023792006933130549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9344285349194671288753699 14016428023792006933130549)
                  ·
                    refine ⟨1314040127230500649980989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14016428023792006933130549 1314040127230500649980989)
                    ·
                      rfl

theorem cell23_7677252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_7677252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677252 prefixEnd_7677252 := by exact prefixLift 7677252
  have htrace : WordTrace (prefixWord ++ tailWord_7677252) baseStart_7677252 baseEnd_7677252 := by
    simpa [prefixWord, tailWord_7677252, baseEnd_7677252] using wordTrace_append hprefix tailTrace_7677252
  have hstable : (prefixWord ++ tailWord_7677252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677252).length < 2 ^ (prefixWord ++ tailWord_7677252).sum := by decide
  have hdescent : baseEnd_7677252 < baseStart_7677252 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677255 : List Nat := [1, 1, 4, 1, 2, 4, 2, 2, 1, 1, 4]
def baseStart_7677255 : Nat := 118140960795 + 7677255 * 2 ^ 59
def prefixEnd_7677255 : Nat := 4983230072969 + 3 ^ 40 * 7677255 * 2
def baseEnd_7677255 : Nat := 3942121922133465438205453

theorem tailTrace_7677255 : CollatzResearch.WordTrace tailWord_7677255 prefixEnd_7677255 3942121922133465438205453 := by
  unfold tailWord_7677255
  simp only [CollatzResearch.WordTrace]
  refine ⟨280012493801623780611473219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186674995867749187074315479 280012493801623780611473219)
  ·
    refine ⟨420018740702435670917209829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280012493801623780611473219 420018740702435670917209829)
    ·
      refine ⟨78753513881706688296976843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 420018740702435670917209829 78753513881706688296976843)
      ·
        refine ⟨118130270822560032445465265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78753513881706688296976843 118130270822560032445465265)
        ·
          refine ⟨88597703116920024334098949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118130270822560032445465265 88597703116920024334098949)
          ·
            refine ⟨16612069334422504562643553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88597703116920024334098949 16612069334422504562643553)
            ·
              refine ⟨12459052000816878421982665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16612069334422504562643553 12459052000816878421982665)
              ·
                refine ⟨9344289000612658816486999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12459052000816878421982665 9344289000612658816486999)
                ·
                  refine ⟨14016433500918988224730499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9344289000612658816486999 14016433500918988224730499)
                  ·
                    refine ⟨21024650251378482337095749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14016433500918988224730499 21024650251378482337095749)
                    ·
                      refine ⟨3942121922133465438205453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21024650251378482337095749 3942121922133465438205453)
                      ·
                        rfl

theorem cell23_7677255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 1, 1, 4].length) (baseStart_7677255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677255 prefixEnd_7677255 := by exact prefixLift 7677255
  have htrace : WordTrace (prefixWord ++ tailWord_7677255) baseStart_7677255 baseEnd_7677255 := by
    simpa [prefixWord, tailWord_7677255, baseEnd_7677255] using wordTrace_append hprefix tailTrace_7677255
  have hstable : (prefixWord ++ tailWord_7677255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677255).length < 2 ^ (prefixWord ++ tailWord_7677255).sum := by decide
  have hdescent : baseEnd_7677255 < baseStart_7677255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677258 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 3, 2, 3]
def baseStart_7677258 : Nat := 118140960795 + 7677258 * 2 ^ 59
def prefixEnd_7677258 : Nat := 4983230072969 + 3 ^ 40 * 7677258 * 2
def baseEnd_7677258 : Nat := 3942123462575428926467939

theorem tailTrace_7677258 : CollatzResearch.WordTrace tailWord_7677258 prefixEnd_7677258 3942123462575428926467939 := by
  unfold tailWord_7677258
  simp only [CollatzResearch.WordTrace]
  refine ⟨70003150805153228030958107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186675068813741941415888285 70003150805153228030958107)
  ·
    refine ⟨105004726207729842046437161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70003150805153228030958107 105004726207729842046437161)
    ·
      refine ⟨78753544655797381534827871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105004726207729842046437161 78753544655797381534827871)
      ·
        refine ⟨118130316983696072302241807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78753544655797381534827871 118130316983696072302241807)
        ·
          refine ⟨177195475475544108453362711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118130316983696072302241807 177195475475544108453362711)
          ·
            refine ⟨265793213213316162680044067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177195475475544108453362711 265793213213316162680044067)
            ·
              refine ⟨398689819819974244020066101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265793213213316162680044067 398689819819974244020066101)
              ·
                refine ⟨37377170608122585376881197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 398689819819974244020066101 37377170608122585376881197)
                ·
                  refine ⟨14016438978045969516330449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37377170608122585376881197 14016438978045969516330449)
                  ·
                    refine ⟨10512329233534477137247837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14016438978045969516330449 10512329233534477137247837)
                    ·
                      refine ⟨3942123462575428926467939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10512329233534477137247837 3942123462575428926467939)
                      ·
                        rfl

theorem cell23_7677258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 3, 2, 3].length) (baseStart_7677258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677258 prefixEnd_7677258 := by exact prefixLift 7677258
  have htrace : WordTrace (prefixWord ++ tailWord_7677258) baseStart_7677258 baseEnd_7677258 := by
    simpa [prefixWord, tailWord_7677258, baseEnd_7677258] using wordTrace_append hprefix tailTrace_7677258
  have hstable : (prefixWord ++ tailWord_7677258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677258).length < 2 ^ (prefixWord ++ tailWord_7677258).sum := by decide
  have hdescent : baseEnd_7677258 < baseStart_7677258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677268 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 3, 2, 4]
def baseStart_7677268 : Nat := 118140960795 + 7677268 * 2 ^ 59
def prefixEnd_7677268 : Nat := 4983230072969 + 3 ^ 40 * 7677268 * 2
def baseEnd_7677268 : Nat := 3942128597381973887342893

theorem tailTrace_7677268 : CollatzResearch.WordTrace tailWord_7677268 prefixEnd_7677268 3942128597381973887342893 := by
  unfold tailWord_7677268
  simp only [CollatzResearch.WordTrace]
  refine ⟨140006483975288341915848229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186675311967051122554464305 140006483975288341915848229)
  ·
    refine ⟨26251215745366564109221543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140006483975288341915848229 26251215745366564109221543)
    ·
      refine ⟨39376823618049846163832315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26251215745366564109221543 39376823618049846163832315)
      ·
        refine ⟨59065235427074769245748473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39376823618049846163832315 59065235427074769245748473)
        ·
          refine ⟨44298926570306076934311355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59065235427074769245748473 44298926570306076934311355)
          ·
            refine ⟨66448389855459115401467033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44298926570306076934311355 66448389855459115401467033)
            ·
              refine ⟨49836292391594336551100275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66448389855459115401467033 49836292391594336551100275)
              ·
                refine ⟨74754438587391504826650413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49836292391594336551100275 74754438587391504826650413)
                ·
                  refine ⟨28032914470271814309993905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74754438587391504826650413 28032914470271814309993905)
                  ·
                    refine ⟨21024685852703860732495429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28032914470271814309993905 21024685852703860732495429)
                    ·
                      refine ⟨3942128597381973887342893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21024685852703860732495429 3942128597381973887342893)
                      ·
                        rfl

theorem cell23_7677268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 3, 2, 4].length) (baseStart_7677268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677268 prefixEnd_7677268 := by exact prefixLift 7677268
  have htrace : WordTrace (prefixWord ++ tailWord_7677268) baseStart_7677268 baseEnd_7677268 := by
    simpa [prefixWord, tailWord_7677268, baseEnd_7677268] using wordTrace_append hprefix tailTrace_7677268
  have hstable : (prefixWord ++ tailWord_7677268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677268).length < 2 ^ (prefixWord ++ tailWord_7677268).sum := by decide
  have hdescent : baseEnd_7677268 < baseStart_7677268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677338 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 2, 6]
def baseStart_7677338 : Nat := 118140960795 + 7677338 * 2 ^ 59
def prefixEnd_7677338 : Nat := 4983230072969 + 3 ^ 40 * 7677338 * 2
def baseEnd_7677338 : Nat := 1314054847009262871155857

theorem tailTrace_7677338 : CollatzResearch.WordTrace tailWord_7677338 prefixEnd_7677338 1314054847009262871155857 := by
  unfold tailWord_7677338
  simp only [CollatzResearch.WordTrace]
  refine ⟨70003880265080771446686167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186677014040215390524496445 70003880265080771446686167)
  ·
    refine ⟨105005820397621157170029251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70003880265080771446686167 105005820397621157170029251)
    ·
      refine ⟨157508730596431735755043877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105005820397621157170029251 157508730596431735755043877)
      ·
        refine ⟨29532886986830950454070727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157508730596431735755043877 29532886986830950454070727)
        ·
          refine ⟨44299330480246425681106091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29532886986830950454070727 44299330480246425681106091)
          ·
            refine ⟨66448995720369638521659137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44299330480246425681106091 66448995720369638521659137)
            ·
              refine ⟨49836746790277228891244353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66448995720369638521659137 49836746790277228891244353)
              ·
                refine ⟨37377560092707921668433265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49836746790277228891244353 37377560092707921668433265)
                ·
                  refine ⟨28033170069530941251324949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37377560092707921668433265 28033170069530941251324949)
                  ·
                    refine ⟨1314054847009262871155857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28033170069530941251324949 1314054847009262871155857)
                    ·
                      rfl

theorem cell23_7677338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 2, 6].length) (baseStart_7677338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677338 prefixEnd_7677338 := by exact prefixLift 7677338
  have htrace : WordTrace (prefixWord ++ tailWord_7677338) baseStart_7677338 baseEnd_7677338 := by
    simpa [prefixWord, tailWord_7677338, baseEnd_7677338] using wordTrace_append hprefix tailTrace_7677338
  have hstable : (prefixWord ++ tailWord_7677338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677338).length < 2 ^ (prefixWord ++ tailWord_7677338).sum := by decide
  have hdescent : baseEnd_7677338 < baseStart_7677338 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677340 : List Nat := [2, 2, 3, 4, 1, 2, 2, 2, 1, 2, 2]
def baseStart_7677340 : Nat := 118140960795 + 7677340 * 2 ^ 59
def prefixEnd_7677340 : Nat := 4983230072969 + 3 ^ 40 * 7677340 * 2
def baseEnd_7677340 : Nat := 3942165567989097605642563

theorem tailTrace_7677340 : CollatzResearch.WordTrace tailWord_7677340 prefixEnd_7677340 3942165567989097605642563 := by
  unfold tailWord_7677340
  simp only [CollatzResearch.WordTrace]
  refine ⟨140007797003157920064158737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186677062670877226752211649 140007797003157920064158737)
  ·
    refine ⟨105005847752368440048119053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140007797003157920064158737 105005847752368440048119053)
    ·
      refine ⟨39377192907138165018044645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105005847752368440048119053 39377192907138165018044645)
      ·
        refine ⟨7383223670088405940883371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39377192907138165018044645 7383223670088405940883371)
        ·
          refine ⟨11074835505132608911325057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7383223670088405940883371 11074835505132608911325057)
          ·
            refine ⟨8306126628849456683493793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11074835505132608911325057 8306126628849456683493793)
            ·
              refine ⟨6229594971637092512620345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8306126628849456683493793 6229594971637092512620345)
              ·
                refine ⟨4672196228727819384465259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6229594971637092512620345 4672196228727819384465259)
                ·
                  refine ⟨7008294343091729076697889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4672196228727819384465259 7008294343091729076697889)
                  ·
                    refine ⟨5256220757318796807523417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7008294343091729076697889 5256220757318796807523417)
                    ·
                      refine ⟨3942165567989097605642563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5256220757318796807523417 3942165567989097605642563)
                      ·
                        rfl

theorem cell23_7677340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_7677340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677340 prefixEnd_7677340 := by exact prefixLift 7677340
  have htrace : WordTrace (prefixWord ++ tailWord_7677340) baseStart_7677340 baseEnd_7677340 := by
    simpa [prefixWord, tailWord_7677340, baseEnd_7677340] using wordTrace_append hprefix tailTrace_7677340
  have hstable : (prefixWord ++ tailWord_7677340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677340).length < 2 ^ (prefixWord ++ tailWord_7677340).sum := by decide
  have hdescent : baseEnd_7677340 < baseStart_7677340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677448 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_7677448 : Nat := 118140960795 + 7677448 * 2 ^ 59
def prefixEnd_7677448 : Nat := 4983230072969 + 3 ^ 40 * 7677448 * 2
def baseEnd_7677448 : Nat := 3942221023899783183092065

theorem tailTrace_7677448 : CollatzResearch.WordTrace tailWord_7677448 prefixEnd_7677448 3942221023899783183092065 := by
  unfold tailWord_7677448
  simp only [CollatzResearch.WordTrace]
  refine ⟨140009766544962287286624499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186679688726616383048832665 140009766544962287286624499)
  ·
    refine ⟨210014649817443430929936749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140009766544962287286624499 210014649817443430929936749)
    ·
      refine ⟨78755493681541286598726281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210014649817443430929936749 78755493681541286598726281)
      ·
        refine ⟨59066620261155964949044711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78755493681541286598726281 59066620261155964949044711)
        ·
          refine ⟨88599930391733947423567067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59066620261155964949044711 88599930391733947423567067)
          ·
            refine ⟨132899895587600921135350601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88599930391733947423567067 132899895587600921135350601)
            ·
              refine ⟨99674921690700690851512951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132899895587600921135350601 99674921690700690851512951)
              ·
                refine ⟨149512382536051036277269427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99674921690700690851512951 149512382536051036277269427)
                ·
                  refine ⟨224268573804076554415904141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149512382536051036277269427 224268573804076554415904141)
                  ·
                    refine ⟨84100715176528707905964053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224268573804076554415904141 84100715176528707905964053)
                    ·
                      refine ⟨3942221023899783183092065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84100715176528707905964053 3942221023899783183092065)
                      ·
                        rfl

theorem cell23_7677448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_7677448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677448 prefixEnd_7677448 := by exact prefixLift 7677448
  have htrace : WordTrace (prefixWord ++ tailWord_7677448) baseStart_7677448 baseEnd_7677448 := by
    simpa [prefixWord, tailWord_7677448, baseEnd_7677448] using wordTrace_append hprefix tailTrace_7677448
  have hstable : (prefixWord ++ tailWord_7677448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677448).length < 2 ^ (prefixWord ++ tailWord_7677448).sum := by decide
  have hdescent : baseEnd_7677448 < baseStart_7677448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677452 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 2, 1, 4]
def baseStart_7677452 : Nat := 118140960795 + 7677452 * 2 ^ 59
def prefixEnd_7677452 : Nat := 4983230072969 + 3 ^ 40 * 7677452 * 2
def baseEnd_7677452 : Nat := 3942223077822401167442047

theorem tailTrace_7677452 : CollatzResearch.WordTrace tailWord_7677452 prefixEnd_7677452 3942223077822401167442047 := by
  unfold tailWord_7677452
  simp only [CollatzResearch.WordTrace]
  refine ⟨140009839490955041628197305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186679785987940055504263073 140009839490955041628197305)
  ·
    refine ⟨105007379618216281221147979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140009839490955041628197305 105007379618216281221147979)
    ·
      refine ⟨157511069427324421831721969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105007379618216281221147979 157511069427324421831721969)
      ·
        refine ⟨118133302070493316373791477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157511069427324421831721969 118133302070493316373791477)
        ·
          refine ⟨11074997069108748410042951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118133302070493316373791477 11074997069108748410042951)
          ·
            refine ⟨16612495603663122615064427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11074997069108748410042951 16612495603663122615064427)
            ·
              refine ⟨24918743405494683922596641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16612495603663122615064427 24918743405494683922596641)
              ·
                refine ⟨18689057554121012941947481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24918743405494683922596641 18689057554121012941947481)
                ·
                  refine ⟨14016793165590759706460611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18689057554121012941947481 14016793165590759706460611)
                  ·
                    refine ⟨21025189748386139559690917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14016793165590759706460611 21025189748386139559690917)
                    ·
                      refine ⟨3942223077822401167442047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21025189748386139559690917 3942223077822401167442047)
                      ·
                        rfl

theorem cell23_7677452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_7677452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677452 prefixEnd_7677452 := by exact prefixLift 7677452
  have htrace : WordTrace (prefixWord ++ tailWord_7677452) baseStart_7677452 baseEnd_7677452 := by
    simpa [prefixWord, tailWord_7677452, baseEnd_7677452] using wordTrace_append hprefix tailTrace_7677452
  have hstable : (prefixWord ++ tailWord_7677452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677452).length < 2 ^ (prefixWord ++ tailWord_7677452).sum := by decide
  have hdescent : baseEnd_7677452 < baseStart_7677452 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677453 : List Nat := [1, 7, 1, 1, 2, 1, 3, 2, 5]
def baseStart_7677453 : Nat := 118140960795 + 7677453 * 2 ^ 59
def prefixEnd_7677453 : Nat := 4983230072969 + 3 ^ 40 * 7677453 * 2
def baseEnd_7677453 : Nat := 438024843478117295947727

theorem tailTrace_7677453 : CollatzResearch.WordTrace tailWord_7677453 prefixEnd_7677453 438024843478117295947727 := by
  unfold tailWord_7677453
  simp only [CollatzResearch.WordTrace]
  refine ⟨280019715454906460427181013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186679810303270973618120675 280019715454906460427181013)
  ·
    refine ⟨6562962080974370166262055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 280019715454906460427181013 6562962080974370166262055)
    ·
      refine ⟨9844443121461555249393083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6562962080974370166262055 9844443121461555249393083)
      ·
        refine ⟨14766664682192332874089625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9844443121461555249393083 14766664682192332874089625)
        ·
          refine ⟨11074998511644249655567219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14766664682192332874089625 11074998511644249655567219)
          ·
            refine ⟨16612497767466374483350829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11074998511644249655567219 16612497767466374483350829)
            ·
              refine ⟨6229686662799890431256561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16612497767466374483350829 6229686662799890431256561)
              ·
                refine ⟨4672264997099917823442421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6229686662799890431256561 4672264997099917823442421)
                ·
                  refine ⟨438024843478117295947727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4672264997099917823442421 438024843478117295947727)
                  ·
                    rfl

theorem cell23_7677453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_7677453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677453 prefixEnd_7677453 := by exact prefixLift 7677453
  have htrace : WordTrace (prefixWord ++ tailWord_7677453) baseStart_7677453 baseEnd_7677453 := by
    simpa [prefixWord, tailWord_7677453, baseEnd_7677453] using wordTrace_append hprefix tailTrace_7677453
  have hstable : (prefixWord ++ tailWord_7677453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677453).length < 2 ^ (prefixWord ++ tailWord_7677453).sum := by decide
  have hdescent : baseEnd_7677453 < baseStart_7677453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677535 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 8, 4]
def baseStart_7677535 : Nat := 118140960795 + 7677535 * 2 ^ 59
def prefixEnd_7677535 : Nat := 4983230072969 + 3 ^ 40 * 7677535 * 2
def baseEnd_7677535 : Nat := 1314088565572241447568055

theorem tailTrace_7677535 : CollatzResearch.WordTrace tailWord_7677535 prefixEnd_7677535 1314088565572241447568055 := by
  unfold tailWord_7677535
  simp only [CollatzResearch.WordTrace]
  refine ⟨280022706240609388431666059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186681804160406258954444039 280022706240609388431666059)
  ·
    refine ⟨420034059360914082647499089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280022706240609388431666059 420034059360914082647499089)
    ·
      refine ⟨315025544520685561985624317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420034059360914082647499089 315025544520685561985624317)
      ·
        refine ⟨118134579195257085744609119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315025544520685561985624317 118134579195257085744609119)
        ·
          refine ⟨177201868792885628616913679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118134579195257085744609119 177201868792885628616913679)
          ·
            refine ⟨265802803189328442925370519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177201868792885628616913679 265802803189328442925370519)
            ·
              refine ⟨398704204783992664388055779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265802803189328442925370519 398704204783992664388055779)
              ·
                refine ⟨598056307175988996582083669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398704204783992664388055779 598056307175988996582083669)
                ·
                  refine ⟨7008472349718621053696293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 598056307175988996582083669 7008472349718621053696293)
                  ·
                    refine ⟨1314088565572241447568055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7008472349718621053696293 1314088565572241447568055)
                    ·
                      rfl

theorem cell23_7677535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 4].length) (baseStart_7677535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677535 prefixEnd_7677535 := by exact prefixLift 7677535
  have htrace : WordTrace (prefixWord ++ tailWord_7677535) baseStart_7677535 baseEnd_7677535 := by
    simpa [prefixWord, tailWord_7677535, baseEnd_7677535] using wordTrace_append hprefix tailTrace_7677535
  have hstable : (prefixWord ++ tailWord_7677535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677535).length < 2 ^ (prefixWord ++ tailWord_7677535).sum := by decide
  have hdescent : baseEnd_7677535 < baseStart_7677535 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677546 : List Nat := [3, 1, 3, 2, 1, 4, 1, 1, 2, 3, 2]
def baseStart_7677546 : Nat := 118140960795 + 7677546 * 2 ^ 59
def prefixEnd_7677546 : Nat := 4983230072969 + 3 ^ 40 * 7677546 * 2
def baseEnd_7677546 : Nat := 3942271345003923799666615

theorem tailTrace_7677546 : CollatzResearch.WordTrace tailWord_7677546 prefixEnd_7677546 3942271345003923799666615 := by
  unfold tailWord_7677546
  simp only [CollatzResearch.WordTrace]
  refine ⟨70005776860892384327579123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186682071629046358206877661 70005776860892384327579123)
  ·
    refine ⟨105008665291338576491368685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70005776860892384327579123 105008665291338576491368685)
    ·
      refine ⟨39378249484251966184263257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105008665291338576491368685 39378249484251966184263257)
      ·
        refine ⟨29533687113188974638197443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39378249484251966184263257 29533687113188974638197443)
        ·
          refine ⟨44300530669783461957296165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29533687113188974638197443 44300530669783461957296165)
          ·
            refine ⟨8306349500584399116993031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44300530669783461957296165 8306349500584399116993031)
            ·
              refine ⟨12459524250876598675489547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8306349500584399116993031 12459524250876598675489547)
              ·
                refine ⟨18689286376314898013234321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12459524250876598675489547 18689286376314898013234321)
                ·
                  refine ⟨14016964782236173509925741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18689286376314898013234321 14016964782236173509925741)
                  ·
                    refine ⟨5256361793338565066222153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14016964782236173509925741 5256361793338565066222153)
                    ·
                      refine ⟨3942271345003923799666615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5256361793338565066222153 3942271345003923799666615)
                      ·
                        rfl

theorem cell23_7677546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_7677546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677546 prefixEnd_7677546 := by exact prefixLift 7677546
  have htrace : WordTrace (prefixWord ++ tailWord_7677546) baseStart_7677546 baseEnd_7677546 := by
    simpa [prefixWord, tailWord_7677546, baseEnd_7677546] using wordTrace_append hprefix tailTrace_7677546
  have hstable : (prefixWord ++ tailWord_7677546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677546).length < 2 ^ (prefixWord ++ tailWord_7677546).sum := by decide
  have hdescent : baseEnd_7677546 < baseStart_7677546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677565 : List Nat := [1, 4, 1, 1, 4, 2, 10]
def baseStart_7677565 : Nat := 118140960795 + 7677565 * 2 ^ 59
def prefixEnd_7677565 : Nat := 4983230072969 + 3 ^ 40 * 7677565 * 2
def baseEnd_7677565 : Nat := 48670137051066163275667

theorem tailTrace_7677565 : CollatzResearch.WordTrace tailWord_7677565 prefixEnd_7677565 48670137051066163275667 := by
  unfold tailWord_7677565
  simp only [CollatzResearch.WordTrace]
  refine ⟨280023800430500703555258149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186682533620333802370172099 280023800430500703555258149)
  ·
    refine ⟨52504462580718881916610903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280023800430500703555258149 52504462580718881916610903)
    ·
      refine ⟨78756693871078322874916355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52504462580718881916610903 78756693871078322874916355)
      ·
        refine ⟨118135040806617484312374533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78756693871078322874916355 118135040806617484312374533)
        ·
          refine ⟨22150320151240778308570225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118135040806617484312374533 22150320151240778308570225)
          ·
            refine ⟨16612740113430583731427669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22150320151240778308570225 16612740113430583731427669)
            ·
              refine ⟨48670137051066163275667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16612740113430583731427669 48670137051066163275667)
              ·
                rfl

theorem cell23_7677565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 10].length) (baseStart_7677565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677565 prefixEnd_7677565 := by exact prefixLift 7677565
  have htrace : WordTrace (prefixWord ++ tailWord_7677565) baseStart_7677565 baseEnd_7677565 := by
    simpa [prefixWord, tailWord_7677565, baseEnd_7677565] using wordTrace_append hprefix tailTrace_7677565
  have hstable : (prefixWord ++ tailWord_7677565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677565).length < 2 ^ (prefixWord ++ tailWord_7677565).sum := by decide
  have hdescent : baseEnd_7677565 < baseStart_7677565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677569 : List Nat := [1, 2, 4, 2, 1, 2, 3, 2, 2, 4]
def baseStart_7677569 : Nat := 118140960795 + 7677569 * 2 ^ 59
def prefixEnd_7677569 : Nat := 4983230072969 + 3 ^ 40 * 7677569 * 2
def baseEnd_7677569 : Nat := 1314094385019659069893003

theorem tailTrace_7677569 : CollatzResearch.WordTrace tailWord_7677569 prefixEnd_7677569 1314094385019659069893003 := by
  unfold tailWord_7677569
  simp only [CollatzResearch.WordTrace]
  refine ⟨280023946322486212238403761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186682630881657474825602507 280023946322486212238403761)
  ·
    refine ⟨210017959741864659178802821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280023946322486212238403761 210017959741864659178802821)
    ·
      refine ⟨39378367451599623596025529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210017959741864659178802821 39378367451599623596025529)
      ·
        refine ⟨29533775588699717697019147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39378367451599623596025529 29533775588699717697019147)
        ·
          refine ⟨44300663383049576545528721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29533775588699717697019147 44300663383049576545528721)
          ·
            refine ⟨33225497537287182409146541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44300663383049576545528721 33225497537287182409146541)
            ·
              refine ⟨12459561576482693403429953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33225497537287182409146541 12459561576482693403429953)
              ·
                refine ⟨9344671182362020052572465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12459561576482693403429953 9344671182362020052572465)
                ·
                  refine ⟨7008503386771515039429349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9344671182362020052572465 7008503386771515039429349)
                  ·
                    refine ⟨1314094385019659069893003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7008503386771515039429349 1314094385019659069893003)
                    ·
                      rfl

theorem cell23_7677569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_7677569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677569 prefixEnd_7677569 := by exact prefixLift 7677569
  have htrace : WordTrace (prefixWord ++ tailWord_7677569) baseStart_7677569 baseEnd_7677569 := by
    simpa [prefixWord, tailWord_7677569, baseEnd_7677569] using wordTrace_append hprefix tailTrace_7677569
  have hstable : (prefixWord ++ tailWord_7677569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677569).length < 2 ^ (prefixWord ++ tailWord_7677569).sum := by decide
  have hdescent : baseEnd_7677569 < baseStart_7677569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677586 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 1, 6]
def baseStart_7677586 : Nat := 118140960795 + 7677586 * 2 ^ 59
def prefixEnd_7677586 : Nat := 4983230072969 + 3 ^ 40 * 7677586 * 2
def baseEnd_7677586 : Nat := 1314097294743367881055477

theorem tailTrace_7677586 : CollatzResearch.WordTrace tailWord_7677586 prefixEnd_7677586 1314097294743367881055477 := by
  unfold tailWord_7677586
  simp only [CollatzResearch.WordTrace]
  refine ⟨70006141590856156035443153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186683044242283082761181741 70006141590856156035443153)
  ·
    refine ⟨52504606193142117026582365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70006141590856156035443153 52504606193142117026582365)
    ·
      refine ⟨19689227322428293884968387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52504606193142117026582365 19689227322428293884968387)
      ·
        refine ⟨29533840983642440827452581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19689227322428293884968387 29533840983642440827452581)
        ·
          refine ⟨5537595184432957655147359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29533840983642440827452581 5537595184432957655147359)
          ·
            refine ⟨8306392776649436482721039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5537595184432957655147359 8306392776649436482721039)
            ·
              refine ⟨12459589164974154724081559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8306392776649436482721039 12459589164974154724081559)
              ·
                refine ⟨18689383747461232086122339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12459589164974154724081559 18689383747461232086122339)
                ·
                  refine ⟨28034075621191848129183509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18689383747461232086122339 28034075621191848129183509)
                  ·
                    refine ⟨1314097294743367881055477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28034075621191848129183509 1314097294743367881055477)
                    ·
                      rfl

theorem cell23_7677586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_7677586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677586 prefixEnd_7677586 := by exact prefixLift 7677586
  have htrace : WordTrace (prefixWord ++ tailWord_7677586) baseStart_7677586 baseEnd_7677586 := by
    simpa [prefixWord, tailWord_7677586, baseEnd_7677586] using wordTrace_append hprefix tailTrace_7677586
  have hstable : (prefixWord ++ tailWord_7677586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677586).length < 2 ^ (prefixWord ++ tailWord_7677586).sum := by decide
  have hdescent : baseEnd_7677586 < baseStart_7677586 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677596 : List Nat := [2, 2, 3, 2, 3, 1, 2, 2, 1, 2, 3]
def baseStart_7677596 : Nat := 118140960795 + 7677596 * 2 ^ 59
def prefixEnd_7677596 : Nat := 4983230072969 + 3 ^ 40 * 7677596 * 2
def baseEnd_7677596 : Nat := 3942297019036648604041385

theorem tailTrace_7677596 : CollatzResearch.WordTrace tailWord_7677596 prefixEnd_7677596 3942297019036648604041385 := by
  unfold tailWord_7677596
  simp only [CollatzResearch.WordTrace]
  refine ⟨140012465546694197924818321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186683287395592263899757761 140012465546694197924818321)
  ·
    refine ⟨105009349160020648443613741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140012465546694197924818321 105009349160020648443613741)
    ·
      refine ⟨39378505935007743166355153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105009349160020648443613741 39378505935007743166355153)
      ·
        refine ⟨29533879451255807374766365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39378505935007743166355153 29533879451255807374766365)
        ·
          refine ⟨11075204794220927765537387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29533879451255807374766365 11075204794220927765537387)
          ·
            refine ⟨16612807191331391648306081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11075204794220927765537387 16612807191331391648306081)
            ·
              refine ⟨12459605393498543736229561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16612807191331391648306081 12459605393498543736229561)
              ·
                refine ⟨9344704045123907802172171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12459605393498543736229561 9344704045123907802172171)
                ·
                  refine ⟨14017056067685861703258257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9344704045123907802172171 14017056067685861703258257)
                  ·
                    refine ⟨10512792050764396277443693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14017056067685861703258257 10512792050764396277443693)
                    ·
                      refine ⟨3942297019036648604041385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10512792050764396277443693 3942297019036648604041385)
                      ·
                        rfl

theorem cell23_7677596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 1, 2, 3].length) (baseStart_7677596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677596 prefixEnd_7677596 := by exact prefixLift 7677596
  have htrace : WordTrace (prefixWord ++ tailWord_7677596) baseStart_7677596 baseEnd_7677596 := by
    simpa [prefixWord, tailWord_7677596, baseEnd_7677596] using wordTrace_append hprefix tailTrace_7677596
  have hstable : (prefixWord ++ tailWord_7677596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677596).length < 2 ^ (prefixWord ++ tailWord_7677596).sum := by decide
  have hdescent : baseEnd_7677596 < baseStart_7677596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677605 : List Nat := [1, 3, 1, 2, 1, 2, 3, 1, 2, 2, 5]
def baseStart_7677605 : Nat := 118140960795 + 7677605 * 2 ^ 59
def prefixEnd_7677605 : Nat := 4983230072969 + 3 ^ 40 * 7677605 * 2
def baseEnd_7677605 : Nat := 3942301640362539068828843

theorem tailTrace_7677605 : CollatzResearch.WordTrace tailWord_7677605 prefixEnd_7677605 3942301640362539068828843 := by
  unfold tailWord_7677605
  simp only [CollatzResearch.WordTrace]
  refine ⟨280025259350355790386714269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186683506233570526924476179 280025259350355790386714269)
  ·
    refine ⟨105009472256383421395017851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280025259350355790386714269 105009472256383421395017851)
    ·
      refine ⟨157514208384575132092526777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105009472256383421395017851 157514208384575132092526777)
      ·
        refine ⟨118135656288431349069395083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157514208384575132092526777 118135656288431349069395083)
        ·
          refine ⟨177203484432647023604092625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118135656288431349069395083 177203484432647023604092625)
          ·
            refine ⟨132902613324485267703069469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177203484432647023604092625 132902613324485267703069469)
            ·
              refine ⟨49838479996681975388651051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132902613324485267703069469 49838479996681975388651051)
              ·
                refine ⟨74757719995022963082976577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49838479996681975388651051 74757719995022963082976577)
                ·
                  refine ⟨56068289996267222312232433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74757719995022963082976577 56068289996267222312232433)
                  ·
                    refine ⟨42051217497200416734174325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56068289996267222312232433 42051217497200416734174325)
                    ·
                      refine ⟨3942301640362539068828843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42051217497200416734174325 3942301640362539068828843)
                      ·
                        rfl

theorem cell23_7677605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_7677605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677605 prefixEnd_7677605 := by exact prefixLift 7677605
  have htrace : WordTrace (prefixWord ++ tailWord_7677605) baseStart_7677605 baseEnd_7677605 := by
    simpa [prefixWord, tailWord_7677605, baseEnd_7677605] using wordTrace_append hprefix tailTrace_7677605
  have hstable : (prefixWord ++ tailWord_7677605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677605).length < 2 ^ (prefixWord ++ tailWord_7677605).sum := by decide
  have hdescent : baseEnd_7677605 < baseStart_7677605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677619 : List Nat := [1, 1, 1, 2, 3, 3, 1, 5, 1, 3, 2]
def baseStart_7677619 : Nat := 118140960795 + 7677619 * 2 ^ 59
def prefixEnd_7677619 : Nat := 4983230072969 + 3 ^ 40 * 7677619 * 2
def baseEnd_7677619 : Nat := 3942308829091702014053779

theorem tailTrace_7677619 : CollatzResearch.WordTrace tailWord_7677619 prefixEnd_7677619 3942308829091702014053779 := by
  unfold tailWord_7677619
  simp only [CollatzResearch.WordTrace]
  refine ⟨280025769972305070777723911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186683846648203380518482607 280025769972305070777723911)
  ·
    refine ⟨420038654958457606166585867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280025769972305070777723911 420038654958457606166585867)
    ·
      refine ⟨630057982437686409249878801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420038654958457606166585867 630057982437686409249878801)
      ·
        refine ⟨472543486828264806937409101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630057982437686409249878801 472543486828264806937409101)
        ·
          refine ⟨177203807560599302601528413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472543486828264806937409101 177203807560599302601528413)
          ·
            refine ⟨66451427835224738475573155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177203807560599302601528413 66451427835224738475573155)
            ·
              refine ⟨99677141752837107713359733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66451427835224738475573155 99677141752837107713359733)
              ·
                refine ⟨9344732039328478848127475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99677141752837107713359733 9344732039328478848127475)
                ·
                  refine ⟨14017098058992718272191213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9344732039328478848127475 14017098058992718272191213)
                  ·
                    refine ⟨5256411772122269352071705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14017098058992718272191213 5256411772122269352071705)
                    ·
                      refine ⟨3942308829091702014053779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5256411772122269352071705 3942308829091702014053779)
                      ·
                        rfl

theorem cell23_7677619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 5, 1, 3, 2].length) (baseStart_7677619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677619 prefixEnd_7677619 := by exact prefixLift 7677619
  have htrace : WordTrace (prefixWord ++ tailWord_7677619) baseStart_7677619 baseEnd_7677619 := by
    simpa [prefixWord, tailWord_7677619, baseEnd_7677619] using wordTrace_append hprefix tailTrace_7677619
  have hstable : (prefixWord ++ tailWord_7677619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677619).length < 2 ^ (prefixWord ++ tailWord_7677619).sum := by decide
  have hdescent : baseEnd_7677619 < baseStart_7677619 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677625 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 4, 6]
def baseStart_7677625 : Nat := 118140960795 + 7677625 * 2 ^ 59
def prefixEnd_7677625 : Nat := 4983230072969 + 3 ^ 40 * 7677625 * 2
def baseEnd_7677625 : Nat := 1314103969991876330192917

theorem tailTrace_7677625 : CollatzResearch.WordTrace tailWord_7677625 prefixEnd_7677625 1314103969991876330192917 := by
  unfold tailWord_7677625
  simp only [CollatzResearch.WordTrace]
  refine ⟨280025988810283333802442329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186683992540188889201628219 280025988810283333802442329)
  ·
    refine ⟨210019491607712500351831747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280025988810283333802442329 210019491607712500351831747)
    ·
      refine ⟨315029237411568750527747621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210019491607712500351831747 315029237411568750527747621)
      ·
        refine ⟨59067982014669140723952679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315029237411568750527747621 59067982014669140723952679)
        ·
          refine ⟨88601973022003711085929019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59067982014669140723952679 88601973022003711085929019)
          ·
            refine ⟨132902959533005566628893529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88601973022003711085929019 132902959533005566628893529)
            ·
              refine ⟨99677219649754174971670147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132902959533005566628893529 99677219649754174971670147)
              ·
                refine ⟨149515829474631262457505221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99677219649754174971670147 149515829474631262457505221)
                ·
                  refine ⟨28034218026493361710782229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149515829474631262457505221 28034218026493361710782229)
                  ·
                    refine ⟨1314103969991876330192917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28034218026493361710782229 1314103969991876330192917)
                    ·
                      rfl

theorem cell23_7677625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 6].length) (baseStart_7677625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677625 prefixEnd_7677625 := by exact prefixLift 7677625
  have htrace : WordTrace (prefixWord ++ tailWord_7677625) baseStart_7677625 baseEnd_7677625 := by
    simpa [prefixWord, tailWord_7677625, baseEnd_7677625] using wordTrace_append hprefix tailTrace_7677625
  have hstable : (prefixWord ++ tailWord_7677625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677625).length < 2 ^ (prefixWord ++ tailWord_7677625).sum := by decide
  have hdescent : baseEnd_7677625 < baseStart_7677625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677655 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 9]
def baseStart_7677655 : Nat := 118140960795 + 7677655 * 2 ^ 59
def prefixEnd_7677655 : Nat := 4983230072969 + 3 ^ 40 * 7677655 * 2
def baseEnd_7677655 : Nat := 438036368266140430355957

theorem tailTrace_7677655 : CollatzResearch.WordTrace tailWord_7677655 prefixEnd_7677655 438036368266140430355957 := by
  unfold tailWord_7677655
  simp only [CollatzResearch.WordTrace]
  refine ⟨280027083000174648926034419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186684722000116432617356279 280027083000174648926034419)
  ·
    refine ⟨420040624500261973389051629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280027083000174648926034419 420040624500261973389051629)
    ·
      refine ⟨157515234187598240020894361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420040624500261973389051629 157515234187598240020894361)
      ·
        refine ⟨118136425640698680015670771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157515234187598240020894361 118136425640698680015670771)
        ·
          refine ⟨177204638461048020023506157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118136425640698680015670771 177204638461048020023506157)
          ·
            refine ⟨66451739422893007508814809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177204638461048020023506157 66451739422893007508814809)
            ·
              refine ⟨49838804567169755631611107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66451739422893007508814809 49838804567169755631611107)
              ·
                refine ⟨74758206850754633447416661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49838804567169755631611107 74758206850754633447416661)
                ·
                  refine ⟨438036368266140430355957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74758206850754633447416661 438036368266140430355957)
                  ·
                    rfl

theorem cell23_7677655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 9].length) (baseStart_7677655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677655 prefixEnd_7677655 := by exact prefixLift 7677655
  have htrace : WordTrace (prefixWord ++ tailWord_7677655) baseStart_7677655 baseEnd_7677655 := by
    simpa [prefixWord, tailWord_7677655, baseEnd_7677655] using wordTrace_append hprefix tailTrace_7677655
  have hstable : (prefixWord ++ tailWord_7677655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677655).length < 2 ^ (prefixWord ++ tailWord_7677655).sum := by decide
  have hdescent : baseEnd_7677655 < baseStart_7677655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677715 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 1, 10]
def baseStart_7677715 : Nat := 118140960795 + 7677715 * 2 ^ 59
def prefixEnd_7677715 : Nat := 4983230072969 + 3 ^ 40 * 7677715 * 2
def baseEnd_7677715 : Nat := 1314119374411511212817779

theorem tailTrace_7677715 : CollatzResearch.WordTrace tailWord_7677715 prefixEnd_7677715 1314119374411511212817779 := by
  unfold tailWord_7677715
  simp only [CollatzResearch.WordTrace]
  refine ⟨280029271379957279173218599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186686180919971519448812399 280029271379957279173218599)
  ·
    refine ⟨420043907069935918759827899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280029271379957279173218599 420043907069935918759827899)
    ·
      refine ⟨630065860604903878139741849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420043907069935918759827899 630065860604903878139741849)
      ·
        refine ⟨472549395453677908604806387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630065860604903878139741849 472549395453677908604806387)
        ·
          refine ⟨708824093180516862907209581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472549395453677908604806387 708824093180516862907209581)
          ·
            refine ⟨265809034942693823590203593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 708824093180516862907209581 265809034942693823590203593)
            ·
              refine ⟨199356776207020367692652695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265809034942693823590203593 199356776207020367692652695)
              ·
                refine ⟨299035164310530551538979043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199356776207020367692652695 299035164310530551538979043)
                ·
                  refine ⟨448552746465795827308468565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299035164310530551538979043 448552746465795827308468565)
                  ·
                    refine ⟨1314119374411511212817779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 448552746465795827308468565 1314119374411511212817779)
                    ·
                      rfl

theorem cell23_7677715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 10].length) (baseStart_7677715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677715 prefixEnd_7677715 := by exact prefixLift 7677715
  have htrace : WordTrace (prefixWord ++ tailWord_7677715) baseStart_7677715 baseEnd_7677715 := by
    simpa [prefixWord, tailWord_7677715, baseEnd_7677715] using wordTrace_append hprefix tailTrace_7677715
  have hstable : (prefixWord ++ tailWord_7677715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677715).length < 2 ^ (prefixWord ++ tailWord_7677715).sum := by decide
  have hdescent : baseEnd_7677715 < baseStart_7677715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677719 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 2, 5]
def baseStart_7677719 : Nat := 118140960795 + 7677719 * 2 ^ 59
def prefixEnd_7677719 : Nat := 4983230072969 + 3 ^ 40 * 7677719 * 2
def baseEnd_7677719 : Nat := 1314120059052383874267773

theorem tailTrace_7677719 : CollatzResearch.WordTrace tailWord_7677719 prefixEnd_7677719 1314120059052383874267773 := by
  unfold tailWord_7677719
  simp only [CollatzResearch.WordTrace]
  refine ⟨280029417271942787856364211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186686278181295191904242807 280029417271942787856364211)
  ·
    refine ⟨420044125907914181784546317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280029417271942787856364211 420044125907914181784546317)
    ·
      refine ⟨157516547215467818169204869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420044125907914181784546317 157516547215467818169204869)
      ·
        refine ⟨29534352602900215906725913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157516547215467818169204869 29534352602900215906725913)
        ·
          refine ⟨22150764452175161930044435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29534352602900215906725913 22150764452175161930044435)
          ·
            refine ⟨33226146678262742895066653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22150764452175161930044435 33226146678262742895066653)
            ·
              refine ⟨12459805004348528585649995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33226146678262742895066653 12459805004348528585649995)
              ·
                refine ⟨18689707506522792878474993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12459805004348528585649995 18689707506522792878474993)
                ·
                  refine ⟨14017280629892094658856245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18689707506522792878474993 14017280629892094658856245)
                  ·
                    refine ⟨1314120059052383874267773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14017280629892094658856245 1314120059052383874267773)
                    ·
                      rfl

theorem cell23_7677719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_7677719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677719 prefixEnd_7677719 := by exact prefixLift 7677719
  have htrace : WordTrace (prefixWord ++ tailWord_7677719) baseStart_7677719 baseEnd_7677719 := by
    simpa [prefixWord, tailWord_7677719, baseEnd_7677719] using wordTrace_append hprefix tailTrace_7677719
  have hstable : (prefixWord ++ tailWord_7677719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677719).length < 2 ^ (prefixWord ++ tailWord_7677719).sum := by decide
  have hdescent : baseEnd_7677719 < baseStart_7677719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677829 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 3, 1, 4]
def baseStart_7677829 : Nat := 118140960795 + 7677829 * 2 ^ 59
def prefixEnd_7677829 : Nat := 4983230072969 + 3 ^ 40 * 7677829 * 2
def baseEnd_7677829 : Nat := 3942416660029146192427813

theorem tailTrace_7677829 : CollatzResearch.WordTrace tailWord_7677829 prefixEnd_7677829 3942416660029146192427813 := by
  unfold tailWord_7677829
  simp only [CollatzResearch.WordTrace]
  refine ⟨280033429301544276642868541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186688952867696184428579027 280033429301544276642868541)
  ·
    refine ⟨105012535988079103741075703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280033429301544276642868541 105012535988079103741075703)
    ·
      refine ⟨157518803982118655611613555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105012535988079103741075703 157518803982118655611613555)
      ·
        refine ⟨236278205973177983417420333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157518803982118655611613555 236278205973177983417420333)
        ·
          refine ⟨88604327239941743781532625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236278205973177983417420333 88604327239941743781532625)
          ·
            refine ⟨66453245429956307836149469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88604327239941743781532625 66453245429956307836149469)
            ·
              refine ⟨24919967036233615438556051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66453245429956307836149469 24919967036233615438556051)
              ·
                refine ⟨37379950554350423157834077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24919967036233615438556051 37379950554350423157834077)
                ·
                  refine ⟨14017481457881408684187779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37379950554350423157834077 14017481457881408684187779)
                  ·
                    refine ⟨21026222186822113026281669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14017481457881408684187779 21026222186822113026281669)
                    ·
                      refine ⟨3942416660029146192427813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21026222186822113026281669 3942416660029146192427813)
                      ·
                        rfl

theorem cell23_7677829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_7677829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677829 prefixEnd_7677829 := by exact prefixLift 7677829
  have htrace : WordTrace (prefixWord ++ tailWord_7677829) baseStart_7677829 baseEnd_7677829 := by
    simpa [prefixWord, tailWord_7677829, baseEnd_7677829] using wordTrace_append hprefix tailTrace_7677829
  have hstable : (prefixWord ++ tailWord_7677829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677829).length < 2 ^ (prefixWord ++ tailWord_7677829).sum := by decide
  have hdescent : baseEnd_7677829 < baseStart_7677829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677849 : List Nat := [1, 2, 1, 2, 1, 3, 5, 1, 1, 1, 5]
def baseStart_7677849 : Nat := 118140960795 + 7677849 * 2 ^ 59
def prefixEnd_7677849 : Nat := 4983230072969 + 3 ^ 40 * 7677849 * 2
def baseEnd_7677849 : Nat := 3942426929642236114177721

theorem tailTrace_7677849 : CollatzResearch.WordTrace tailWord_7677849 prefixEnd_7677849 3942426929642236114177721 := by
  unfold tailWord_7677849
  simp only [CollatzResearch.WordTrace]
  refine ⟨280034158761471820058596601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186689439174314546705731067 280034158761471820058596601)
  ·
    refine ⟨210025619071103865043947451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280034158761471820058596601 210025619071103865043947451)
    ·
      refine ⟨315038428606655797565921177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210025619071103865043947451 315038428606655797565921177)
      ·
        refine ⟨236278821454991848174440883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315038428606655797565921177 236278821454991848174440883)
        ·
          refine ⟨354418232182487772261661325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236278821454991848174440883 354418232182487772261661325)
          ·
            refine ⟨132906837068432914598122997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354418232182487772261661325 132906837068432914598122997)
            ·
              refine ⟨12460015975165585743574031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132906837068432914598122997 12460015975165585743574031)
              ·
                refine ⟨18690023962748378615361047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12460015975165585743574031 18690023962748378615361047)
                ·
                  refine ⟨28035035944122567923041571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18690023962748378615361047 28035035944122567923041571)
                  ·
                    refine ⟨42052553916183851884562357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28035035944122567923041571 42052553916183851884562357)
                    ·
                      refine ⟨3942426929642236114177721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42052553916183851884562357 3942426929642236114177721)
                      ·
                        rfl

theorem cell23_7677849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_7677849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677849 prefixEnd_7677849 := by exact prefixLift 7677849
  have htrace : WordTrace (prefixWord ++ tailWord_7677849) baseStart_7677849 baseEnd_7677849 := by
    simpa [prefixWord, tailWord_7677849, baseEnd_7677849] using wordTrace_append hprefix tailTrace_7677849
  have hstable : (prefixWord ++ tailWord_7677849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677849).length < 2 ^ (prefixWord ++ tailWord_7677849).sum := by decide
  have hdescent : baseEnd_7677849 < baseStart_7677849 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677886 : List Nat := [4, 2, 1, 1, 1, 4, 3, 7]
def baseStart_7677886 : Nat := 118140960795 + 7677886 * 2 ^ 59
def prefixEnd_7677886 : Nat := 4983230072969 + 3 ^ 40 * 7677886 * 2
def baseEnd_7677886 : Nat := 146016515867646387756113

theorem tailTrace_7677886 : CollatzResearch.WordTrace tailWord_7677886 prefixEnd_7677886 146016515867646387756113 := by
  unfold tailWord_7677886
  simp only [CollatzResearch.WordTrace]
  refine ⟨35004438532792221922211689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186690338841558516918462341 35004438532792221922211689)
  ·
    refine ⟨26253328899594166441658767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35004438532792221922211689 26253328899594166441658767)
    ·
      refine ⟨39379993349391249662488151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26253328899594166441658767 39379993349391249662488151)
      ·
        refine ⟨59069990024086874493732227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39379993349391249662488151 59069990024086874493732227)
        ·
          refine ⟨88604985036130311740598341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59069990024086874493732227 88604985036130311740598341)
          ·
            refine ⟨16613434694274433451362189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 88604985036130311740598341 16613434694274433451362189)
            ·
              refine ⟨6230038010352912544260821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16613434694274433451362189 6230038010352912544260821)
              ·
                refine ⟨146016515867646387756113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6230038010352912544260821 146016515867646387756113)
                ·
                  rfl

theorem cell23_7677886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 3, 7].length) (baseStart_7677886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677886 prefixEnd_7677886 := by exact prefixLift 7677886
  have htrace : WordTrace (prefixWord ++ tailWord_7677886) baseStart_7677886 baseEnd_7677886 := by
    simpa [prefixWord, tailWord_7677886, baseEnd_7677886] using wordTrace_append hprefix tailTrace_7677886
  have hstable : (prefixWord ++ tailWord_7677886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677886).length < 2 ^ (prefixWord ++ tailWord_7677886).sum := by decide
  have hdescent : baseEnd_7677886 < baseStart_7677886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677896 : List Nat := [2, 1, 3, 1, 4, 1, 2, 2, 1, 3, 3]
def baseStart_7677896 : Nat := 118140960795 + 7677896 * 2 ^ 59
def prefixEnd_7677896 : Nat := 4983230072969 + 3 ^ 40 * 7677896 * 2
def baseEnd_7677896 : Nat := 3942451063232997430290005

theorem tailTrace_7677896 : CollatzResearch.WordTrace tailWord_7677896 prefixEnd_7677896 3942451063232997430290005 := by
  unfold tailWord_7677896
  simp only [CollatzResearch.WordTrace]
  refine ⟨140017936496150773542778771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186690581994867698057038361 140017936496150773542778771)
  ·
    refine ⟨210026904744226160314168157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140017936496150773542778771 210026904744226160314168157)
    ·
      refine ⟨78760089279084810117813059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210026904744226160314168157 78760089279084810117813059)
      ·
        refine ⟨118140133918627215176719589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78760089279084810117813059 118140133918627215176719589)
        ·
          refine ⟨22151275109742602845634923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118140133918627215176719589 22151275109742602845634923)
          ·
            refine ⟨33226912664613904268452385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22151275109742602845634923 33226912664613904268452385)
            ·
              refine ⟨24920184498460428201339289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33226912664613904268452385 24920184498460428201339289)
              ·
                refine ⟨18690138373845321151004467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24920184498460428201339289 18690138373845321151004467)
                ·
                  refine ⟨28035207560767981726506701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18690138373845321151004467 28035207560767981726506701)
                  ·
                    refine ⟨10513202835287993147440013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28035207560767981726506701 10513202835287993147440013)
                    ·
                      refine ⟨3942451063232997430290005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10513202835287993147440013 3942451063232997430290005)
                      ·
                        rfl

theorem cell23_7677896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_7677896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677896 prefixEnd_7677896 := by exact prefixLift 7677896
  have htrace : WordTrace (prefixWord ++ tailWord_7677896) baseStart_7677896 baseEnd_7677896 := by
    simpa [prefixWord, tailWord_7677896, baseEnd_7677896] using wordTrace_append hprefix tailTrace_7677896
  have hstable : (prefixWord ++ tailWord_7677896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677896).length < 2 ^ (prefixWord ++ tailWord_7677896).sum := by decide
  have hdescent : baseEnd_7677896 < baseStart_7677896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677900 : List Nat := [2, 2, 1, 4, 1, 4, 2, 1, 1, 2, 3]
def baseStart_7677900 : Nat := 118140960795 + 7677900 * 2 ^ 59
def prefixEnd_7677900 : Nat := 4983230072969 + 3 ^ 40 * 7677900 * 2
def baseEnd_7677900 : Nat := 3942453117155615414639987

theorem tailTrace_7677900 : CollatzResearch.WordTrace tailWord_7677900 prefixEnd_7677900 3942453117155615414639987 := by
  unfold tailWord_7677900
  simp only [CollatzResearch.WordTrace]
  refine ⟨140018009442143527884351577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186690679256191370512468769 140018009442143527884351577)
  ·
    refine ⟨105013507081607645913263683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140018009442143527884351577 105013507081607645913263683)
    ·
      refine ⟨157520260622411468869895525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105013507081607645913263683 157520260622411468869895525)
      ·
        refine ⟨29535048866702150413105411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157520260622411468869895525 29535048866702150413105411)
        ·
          refine ⟨44302573300053225619658117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29535048866702150413105411 44302573300053225619658117)
          ·
            refine ⟨8306732493759979803685897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 44302573300053225619658117 8306732493759979803685897)
            ·
              refine ⟨6230049370319984852764423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8306732493759979803685897 6230049370319984852764423)
              ·
                refine ⟨9345074055479977279146635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6230049370319984852764423 9345074055479977279146635)
                ·
                  refine ⟨14017611083219965918719953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9345074055479977279146635 14017611083219965918719953)
                  ·
                    refine ⟨10513208312414974439039965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14017611083219965918719953 10513208312414974439039965)
                    ·
                      refine ⟨3942453117155615414639987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10513208312414974439039965 3942453117155615414639987)
                      ·
                        rfl

theorem cell23_7677900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_7677900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677900 prefixEnd_7677900 := by exact prefixLift 7677900
  have htrace : WordTrace (prefixWord ++ tailWord_7677900) baseStart_7677900 baseEnd_7677900 := by
    simpa [prefixWord, tailWord_7677900, baseEnd_7677900] using wordTrace_append hprefix tailTrace_7677900
  have hstable : (prefixWord ++ tailWord_7677900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677900).length < 2 ^ (prefixWord ++ tailWord_7677900).sum := by decide
  have hdescent : baseEnd_7677900 < baseStart_7677900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677913 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 4, 1, 3]
def baseStart_7677913 : Nat := 118140960795 + 7677913 * 2 ^ 59
def prefixEnd_7677913 : Nat := 4983230072969 + 3 ^ 40 * 7677913 * 2
def baseEnd_7677913 : Nat := 3942459792404123863777427

theorem tailTrace_7677913 : CollatzResearch.WordTrace tailWord_7677913 prefixEnd_7677913 3942459792404123863777427 := by
  unfold tailWord_7677913
  simp only [CollatzResearch.WordTrace]
  refine ⟨280036493033239958988926393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186690995355493305992617595 280036493033239958988926393)
  ·
    refine ⟨210027369774929969241694795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280036493033239958988926393 210027369774929969241694795)
    ·
      refine ⟨315041054662394953862542193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210027369774929969241694795 315041054662394953862542193)
      ·
        refine ⟨236280790996796215396906645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315041054662394953862542193 236280790996796215396906645)
        ·
          refine ⟨11075662077974822596729999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 236280790996796215396906645 11075662077974822596729999)
          ·
            refine ⟨16613493116962233895094999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11075662077974822596729999 16613493116962233895094999)
            ·
              refine ⟨24920239675443350842642499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16613493116962233895094999 24920239675443350842642499)
              ·
                refine ⟨37380359513165026263963749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24920239675443350842642499 37380359513165026263963749)
                ·
                  refine ⟨7008817408718442424493203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37380359513165026263963749 7008817408718442424493203)
                  ·
                    refine ⟨10513226113077663636739805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7008817408718442424493203 10513226113077663636739805)
                    ·
                      refine ⟨3942459792404123863777427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10513226113077663636739805 3942459792404123863777427)
                      ·
                        rfl

theorem cell23_7677913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 4, 1, 3].length) (baseStart_7677913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677913 prefixEnd_7677913 := by exact prefixLift 7677913
  have htrace : WordTrace (prefixWord ++ tailWord_7677913) baseStart_7677913 baseEnd_7677913 := by
    simpa [prefixWord, tailWord_7677913, baseEnd_7677913] using wordTrace_append hprefix tailTrace_7677913
  have hstable : (prefixWord ++ tailWord_7677913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677913).length < 2 ^ (prefixWord ++ tailWord_7677913).sum := by decide
  have hdescent : baseEnd_7677913 < baseStart_7677913 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677930 : List Nat := [3, 1, 3, 1, 2, 1, 5, 1, 2, 1, 3]
def baseStart_7677930 : Nat := 118140960795 + 7677930 * 2 ^ 59
def prefixEnd_7677930 : Nat := 4983230072969 + 3 ^ 40 * 7677930 * 2
def baseEnd_7677930 : Nat := 3942468521575250297264849

theorem tailTrace_7677930 : CollatzResearch.WordTrace tailWord_7677930 prefixEnd_7677930 3942468521575250297264849 := by
  unfold tailWord_7677930
  simp only [CollatzResearch.WordTrace]
  refine ⟨70009278268544592723073811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186691408716118913928196829 70009278268544592723073811)
  ·
    refine ⟨105013917402816889084610717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70009278268544592723073811 105013917402816889084610717)
    ·
      refine ⟨39380219026056333406729019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105013917402816889084610717 39380219026056333406729019)
      ·
        refine ⟨59070328539084500110093529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39380219026056333406729019 59070328539084500110093529)
        ·
          refine ⟨44302746404313375082570147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59070328539084500110093529 44302746404313375082570147)
          ·
            refine ⟨66454119606470062623855221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44302746404313375082570147 66454119606470062623855221)
            ·
              refine ⟨6230073713106568370986427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66454119606470062623855221 6230073713106568370986427)
              ·
                refine ⟨9345110569659852556479641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6230073713106568370986427 9345110569659852556479641)
                ·
                  refine ⟨7008832927244889417359731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9345110569659852556479641 7008832927244889417359731)
                  ·
                    refine ⟨10513249390867334126039597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7008832927244889417359731 10513249390867334126039597)
                    ·
                      refine ⟨3942468521575250297264849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10513249390867334126039597 3942468521575250297264849)
                      ·
                        rfl

theorem cell23_7677930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 1, 2, 1, 3].length) (baseStart_7677930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677930 prefixEnd_7677930 := by exact prefixLift 7677930
  have htrace : WordTrace (prefixWord ++ tailWord_7677930) baseStart_7677930 baseEnd_7677930 := by
    simpa [prefixWord, tailWord_7677930, baseEnd_7677930] using wordTrace_append hprefix tailTrace_7677930
  have hstable : (prefixWord ++ tailWord_7677930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677930).length < 2 ^ (prefixWord ++ tailWord_7677930).sum := by decide
  have hdescent : baseEnd_7677930 < baseStart_7677930 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677939 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 3]
def baseStart_7677939 : Nat := 118140960795 + 7677939 * 2 ^ 59
def prefixEnd_7677939 : Nat := 4983230072969 + 3 ^ 40 * 7677939 * 2
def baseEnd_7677939 : Nat := 3942473142901140762052307

theorem tailTrace_7677939 : CollatzResearch.WordTrace tailWord_7677939 prefixEnd_7677939 3942473142901140762052307 := by
  unfold tailWord_7677939
  simp only [CollatzResearch.WordTrace]
  refine ⟨280037441331145765429372871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186691627554097176952915247 280037441331145765429372871)
  ·
    refine ⟨420056161996718648144059307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280037441331145765429372871 420056161996718648144059307)
    ·
      refine ⟨630084242995077972216088961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420056161996718648144059307 630084242995077972216088961)
      ·
        refine ⟨472563182246308479162066721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630084242995077972216088961 472563182246308479162066721)
        ·
          refine ⟨354422386684731359371550041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472563182246308479162066721 354422386684731359371550041)
          ·
            refine ⟨265816790013548519528662531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354422386684731359371550041 265816790013548519528662531)
            ·
              refine ⟨398725185020322779292993797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265816790013548519528662531 398725185020322779292993797)
              ·
                refine ⟨74760972191310521117436337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 398725185020322779292993797 74760972191310521117436337)
                ·
                  refine ⟨56070729143482890838077253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74760972191310521117436337 56070729143482890838077253)
                  ·
                    refine ⟨10513261714403042032139485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56070729143482890838077253 10513261714403042032139485)
                    ·
                      refine ⟨3942473142901140762052307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10513261714403042032139485 3942473142901140762052307)
                      ·
                        rfl

theorem cell23_7677939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4, 3].length) (baseStart_7677939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677939 prefixEnd_7677939 := by exact prefixLift 7677939
  have htrace : WordTrace (prefixWord ++ tailWord_7677939) baseStart_7677939 baseEnd_7677939 := by
    simpa [prefixWord, tailWord_7677939, baseEnd_7677939] using wordTrace_append hprefix tailTrace_7677939
  have hstable : (prefixWord ++ tailWord_7677939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677939).length < 2 ^ (prefixWord ++ tailWord_7677939).sum := by decide
  have hdescent : baseEnd_7677939 < baseStart_7677939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677949 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 1, 4, 4]
def baseStart_7677949 : Nat := 118140960795 + 7677949 * 2 ^ 59
def prefixEnd_7677949 : Nat := 4983230072969 + 3 ^ 40 * 7677949 * 2
def baseEnd_7677949 : Nat := 3942478277707685722927261

theorem tailTrace_7677949 : CollatzResearch.WordTrace tailWord_7677949 prefixEnd_7677949 3942478277707685722927261 := by
  unfold tailWord_7677949
  simp only [CollatzResearch.WordTrace]
  refine ⟨280037806061109537137236901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186691870707406358091491267 280037806061109537137236901)
  ·
    refine ⟨52507088636458038213231919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280037806061109537137236901 52507088636458038213231919)
    ·
      refine ⟨78760632954687057319847879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52507088636458038213231919 78760632954687057319847879)
      ·
        refine ⟨118140949432030585979771819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78760632954687057319847879 118140949432030585979771819)
        ·
          refine ⟨177211424148045878969657729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118140949432030585979771819 177211424148045878969657729)
          ·
            refine ⟨132908568111034409227243297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177211424148045878969657729 132908568111034409227243297)
            ·
              refine ⟨99681426083275806920432473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132908568111034409227243297 99681426083275806920432473)
              ·
                refine ⟨74761069562456855190324355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99681426083275806920432473 74761069562456855190324355)
                ·
                  refine ⟨112141604343685282785486533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74761069562456855190324355 112141604343685282785486533)
                  ·
                    refine ⟨21026550814440990522278725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 112141604343685282785486533 21026550814440990522278725)
                    ·
                      refine ⟨3942478277707685722927261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21026550814440990522278725 3942478277707685722927261)
                      ·
                        rfl

theorem cell23_7677949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_7677949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677949 prefixEnd_7677949 := by exact prefixLift 7677949
  have htrace : WordTrace (prefixWord ++ tailWord_7677949) baseStart_7677949 baseEnd_7677949 := by
    simpa [prefixWord, tailWord_7677949, baseEnd_7677949] using wordTrace_append hprefix tailTrace_7677949
  have hstable : (prefixWord ++ tailWord_7677949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677949).length < 2 ^ (prefixWord ++ tailWord_7677949).sum := by decide
  have hdescent : baseEnd_7677949 < baseStart_7677949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677953 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 6, 2, 2]
def baseStart_7677953 : Nat := 118140960795 + 7677953 * 2 ^ 59
def prefixEnd_7677953 : Nat := 4983230072969 + 3 ^ 40 * 7677953 * 2
def baseEnd_7677953 : Nat := 3942480331630303707277243

theorem tailTrace_7677953 : CollatzResearch.WordTrace tailWord_7677953 prefixEnd_7677953 3942480331630303707277243 := by
  unfold tailWord_7677953
  simp only [CollatzResearch.WordTrace]
  refine ⟨280037951953095045820382513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186691967968730030546921675 280037951953095045820382513)
  ·
    refine ⟨210028463964821284365286885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280037951953095045820382513 210028463964821284365286885)
    ·
      refine ⟨39380336993403990818491291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210028463964821284365286885 39380336993403990818491291)
      ·
        refine ⟨59070505490105986227736937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39380336993403990818491291 59070505490105986227736937)
        ·
          refine ⟨44302879117579489670802703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59070505490105986227736937 44302879117579489670802703)
          ·
            refine ⟨66454318676369234506204055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44302879117579489670802703 66454318676369234506204055)
            ·
              refine ⟨99681478014553851759306083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66454318676369234506204055 99681478014553851759306083)
              ·
                refine ⟨149522217021830777638959125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99681478014553851759306083 149522217021830777638959125)
                ·
                  refine ⟨7008853922898317701826209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 149522217021830777638959125 7008853922898317701826209)
                  ·
                    refine ⟨5256640442173738276369657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7008853922898317701826209 5256640442173738276369657)
                    ·
                      refine ⟨3942480331630303707277243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5256640442173738276369657 3942480331630303707277243)
                      ·
                        rfl

theorem cell23_7677953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 6, 2, 2].length) (baseStart_7677953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677953 prefixEnd_7677953 := by exact prefixLift 7677953
  have htrace : WordTrace (prefixWord ++ tailWord_7677953) baseStart_7677953 baseEnd_7677953 := by
    simpa [prefixWord, tailWord_7677953, baseEnd_7677953] using wordTrace_append hprefix tailTrace_7677953
  have hstable : (prefixWord ++ tailWord_7677953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677953).length < 2 ^ (prefixWord ++ tailWord_7677953).sum := by decide
  have hdescent : baseEnd_7677953 < baseStart_7677953 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677986 : List Nat := [3, 3, 1, 1, 1, 2, 2, 1, 1, 5, 3]
def baseStart_7677986 : Nat := 118140960795 + 7677986 * 2 ^ 59
def prefixEnd_7677986 : Nat := 4983230072969 + 3 ^ 40 * 7677986 * 2
def baseEnd_7677986 : Nat := 3942497276491902078164591

theorem tailTrace_7677986 : CollatzResearch.WordTrace tailWord_7677986 prefixEnd_7677986 3942497276491902078164591 := by
  unfold tailWord_7677986
  simp only [CollatzResearch.WordTrace]
  refine ⟨70009788890493873114083453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186692770374650328304222541 70009788890493873114083453)
  ·
    refine ⟨26253670833935202417781295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70009788890493873114083453 26253670833935202417781295)
    ·
      refine ⟨39380506250902803626671943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26253670833935202417781295 39380506250902803626671943)
      ·
        refine ⟨59070759376354205440007915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39380506250902803626671943 59070759376354205440007915)
        ·
          refine ⟨88606139064531308160011873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59070759376354205440007915 88606139064531308160011873)
          ·
            refine ⟨66454604298398481120008905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88606139064531308160011873 66454604298398481120008905)
            ·
              refine ⟨49840953223798860840006679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66454604298398481120008905 49840953223798860840006679)
              ·
                refine ⟨74761429835698291260010019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49840953223798860840006679 74761429835698291260010019)
                ·
                  refine ⟨112142144753547436890015029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74761429835698291260010019 112142144753547436890015029)
                  ·
                    refine ⟨10513326070645072208438909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 112142144753547436890015029 10513326070645072208438909)
                    ·
                      refine ⟨3942497276491902078164591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10513326070645072208438909 3942497276491902078164591)
                      ·
                        rfl

theorem cell23_7677986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_7677986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677986 prefixEnd_7677986 := by exact prefixLift 7677986
  have htrace : WordTrace (prefixWord ++ tailWord_7677986) baseStart_7677986 baseEnd_7677986 := by
    simpa [prefixWord, tailWord_7677986, baseEnd_7677986] using wordTrace_append hprefix tailTrace_7677986
  have hstable : (prefixWord ++ tailWord_7677986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677986).length < 2 ^ (prefixWord ++ tailWord_7677986).sum := by decide
  have hdescent : baseEnd_7677986 < baseStart_7677986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7677996 : List Nat := [2, 2, 1, 1, 1, 2, 2, 1, 4, 5, 2]
def baseStart_7677996 : Nat := 118140960795 + 7677996 * 2 ^ 59
def prefixEnd_7677996 : Nat := 4983230072969 + 3 ^ 40 * 7677996 * 2
def baseEnd_7677996 : Nat := 3942502411298447039039545

theorem tailTrace_7677996 : CollatzResearch.WordTrace tailWord_7677996 prefixEnd_7677996 3942502411298447039039545 := by
  unfold tailWord_7677996
  simp only [CollatzResearch.WordTrace]
  refine ⟨140019760145969632082098921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186693013527959509442798561 140019760145969632082098921)
  ·
    refine ⟨105014820109477224061574191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140019760145969632082098921 105014820109477224061574191)
    ·
      refine ⟨157522230164215836092361287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105014820109477224061574191 157522230164215836092361287)
      ·
        refine ⟨236283345246323754138541931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157522230164215836092361287 236283345246323754138541931)
        ·
          refine ⟨354425017869485631207812897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236283345246323754138541931 354425017869485631207812897)
          ·
            refine ⟨265818763402114223405859673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354425017869485631207812897 265818763402114223405859673)
            ·
              refine ⟨199364072551585667554394755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265818763402114223405859673 199364072551585667554394755)
              ·
                refine ⟨299046108827378501331592133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199364072551585667554394755 299046108827378501331592133)
                ·
                  refine ⟨56071145405133468999673525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 299046108827378501331592133 56071145405133468999673525)
                  ·
                    refine ⟨5256669881731262718719393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56071145405133468999673525 5256669881731262718719393)
                    ·
                      refine ⟨3942502411298447039039545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5256669881731262718719393 3942502411298447039039545)
                      ·
                        rfl

theorem cell23_7677996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 5, 2].length) (baseStart_7677996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7677996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7677996 prefixEnd_7677996 := by exact prefixLift 7677996
  have htrace : WordTrace (prefixWord ++ tailWord_7677996) baseStart_7677996 baseEnd_7677996 := by
    simpa [prefixWord, tailWord_7677996, baseEnd_7677996] using wordTrace_append hprefix tailTrace_7677996
  have hstable : (prefixWord ++ tailWord_7677996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7677996).length < 2 ^ (prefixWord ++ tailWord_7677996).sum := by decide
  have hdescent : baseEnd_7677996 < baseStart_7677996 := by decide
  rcases family_descends (prefixWord ++ tailWord_7677996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678049 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 10]
def baseStart_7678049 : Nat := 118140960795 + 7678049 * 2 ^ 59
def prefixEnd_7678049 : Nat := 4983230072969 + 3 ^ 40 * 7678049 * 2
def baseEnd_7678049 : Nat := 438058847308126147964089

theorem tailTrace_7678049 : CollatzResearch.WordTrace tailWord_7678049 prefixEnd_7678049 438058847308126147964089 := by
  unfold tailWord_7678049
  simp only [CollatzResearch.WordTrace]
  refine ⟨280041453360747254215877201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186694302240498169477251467 280041453360747254215877201)
  ·
    refine ⟨210031090020560440661907901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280041453360747254215877201 210031090020560440661907901)
    ·
      refine ⟨78761658757710165248215463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210031090020560440661907901 78761658757710165248215463)
      ·
        refine ⟨118142488136565247872323195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78761658757710165248215463 118142488136565247872323195)
        ·
          refine ⟨177213732204847871808484793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118142488136565247872323195 177213732204847871808484793)
          ·
            refine ⟨132910299153635903856363595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177213732204847871808484793 132910299153635903856363595)
            ·
              refine ⟨199365448730453855784545393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132910299153635903856363595 199365448730453855784545393)
              ·
                refine ⟨149524086547840391838409045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199365448730453855784545393 149524086547840391838409045)
                ·
                  refine ⟨438058847308126147964089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 149524086547840391838409045 438058847308126147964089)
                  ·
                    rfl

theorem cell23_7678049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 10].length) (baseStart_7678049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678049 prefixEnd_7678049 := by exact prefixLift 7678049
  have htrace : WordTrace (prefixWord ++ tailWord_7678049) baseStart_7678049 baseEnd_7678049 := by
    simpa [prefixWord, tailWord_7678049, baseEnd_7678049] using wordTrace_append hprefix tailTrace_7678049
  have hstable : (prefixWord ++ tailWord_7678049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678049).length < 2 ^ (prefixWord ++ tailWord_7678049).sum := by decide
  have hdescent : baseEnd_7678049 < baseStart_7678049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678053 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 3, 4]
def baseStart_7678053 : Nat := 118140960795 + 7678053 * 2 ^ 59
def prefixEnd_7678053 : Nat := 4983230072969 + 3 ^ 40 * 7678053 * 2
def baseEnd_7678053 : Nat := 1314177226565251105342261

theorem tailTrace_7678053 : CollatzResearch.WordTrace tailWord_7678053 prefixEnd_7678053 1314177226565251105342261 := by
  unfold tailWord_7678053
  simp only [CollatzResearch.WordTrace]
  refine ⟨280041599252732762899022813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186694399501821841932681875 280041599252732762899022813)
  ·
    refine ⟨105015599719774786087133555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280041599252732762899022813 105015599719774786087133555)
    ·
      refine ⟨157523399579662179130700333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105015599719774786087133555 157523399579662179130700333)
      ·
        refine ⟨59071274842373317174012625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157523399579662179130700333 59071274842373317174012625)
        ·
          refine ⟨44303456131779987880509469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59071274842373317174012625 44303456131779987880509469)
          ·
            refine ⟨16613796049417495455191051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44303456131779987880509469 16613796049417495455191051)
            ·
              refine ⟨24920694074126243182786577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16613796049417495455191051 24920694074126243182786577)
              ·
                refine ⟨18690520555594682387089933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24920694074126243182786577 18690520555594682387089933)
                ·
                  refine ⟨7008945208348005895158725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18690520555594682387089933 7008945208348005895158725)
                  ·
                    refine ⟨1314177226565251105342261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7008945208348005895158725 1314177226565251105342261)
                    ·
                      rfl

theorem cell23_7678053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_7678053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678053 prefixEnd_7678053 := by exact prefixLift 7678053
  have htrace : WordTrace (prefixWord ++ tailWord_7678053) baseStart_7678053 baseEnd_7678053 := by
    simpa [prefixWord, tailWord_7678053, baseEnd_7678053] using wordTrace_append hprefix tailTrace_7678053
  have hstable : (prefixWord ++ tailWord_7678053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678053).length < 2 ^ (prefixWord ++ tailWord_7678053).sum := by decide
  have hdescent : baseEnd_7678053 < baseStart_7678053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678063 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 3]
def baseStart_7678063 : Nat := 118140960795 + 7678063 * 2 ^ 59
def prefixEnd_7678063 : Nat := 4983230072969 + 3 ^ 40 * 7678063 * 2
def baseEnd_7678063 : Nat := 3942536814502298276901737

theorem tailTrace_7678063 : CollatzResearch.WordTrace tailWord_7678063 prefixEnd_7678063 3942536814502298276901737 := by
  unfold tailWord_7678063
  simp only [CollatzResearch.WordTrace]
  refine ⟨280041963982696534606886843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186694642655131023071257895 280041963982696534606886843)
  ·
    refine ⟨420062945974044801910330265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280041963982696534606886843 420062945974044801910330265)
    ·
      refine ⟨315047209480533601432747699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420062945974044801910330265 315047209480533601432747699)
      ·
        refine ⟨472570814220800402149121549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315047209480533601432747699 472570814220800402149121549)
        ·
          refine ⟨177214055332800150805920581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472570814220800402149121549 177214055332800150805920581)
          ·
            refine ⟨33227635374900028276110109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177214055332800150805920581 33227635374900028276110109)
            ·
              refine ⟨12460363265587510603541291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33227635374900028276110109 12460363265587510603541291)
              ·
                refine ⟨18690544898381265905311937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12460363265587510603541291 18690544898381265905311937)
                ·
                  refine ⟨14017908673785949428983953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18690544898381265905311937 14017908673785949428983953)
                  ·
                    refine ⟨10513431505339462071737965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14017908673785949428983953 10513431505339462071737965)
                    ·
                      refine ⟨3942536814502298276901737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10513431505339462071737965 3942536814502298276901737)
                      ·
                        rfl

theorem cell23_7678063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 2, 2, 3].length) (baseStart_7678063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678063 prefixEnd_7678063 := by exact prefixLift 7678063
  have htrace : WordTrace (prefixWord ++ tailWord_7678063) baseStart_7678063 baseEnd_7678063 := by
    simpa [prefixWord, tailWord_7678063, baseEnd_7678063] using wordTrace_append hprefix tailTrace_7678063
  have hstable : (prefixWord ++ tailWord_7678063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678063).length < 2 ^ (prefixWord ++ tailWord_7678063).sum := by decide
  have hdescent : baseEnd_7678063 < baseStart_7678063 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678083 : List Nat := [1, 1, 1, 3, 3, 5, 1, 2, 6]
def baseStart_7678083 : Nat := 118140960795 + 7678083 * 2 ^ 59
def prefixEnd_7678083 : Nat := 4983230072969 + 3 ^ 40 * 7678083 * 2
def baseEnd_7678083 : Nat := 438060787123932022072405

theorem tailTrace_7678083 : CollatzResearch.WordTrace tailWord_7678083 prefixEnd_7678083 438060787123932022072405 := by
  unfold tailWord_7678083
  simp only [CollatzResearch.WordTrace]
  refine ⟨280042693442624078022614903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186695128961749385348409935 280042693442624078022614903)
  ·
    refine ⟨420064040163936117033922355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280042693442624078022614903 420064040163936117033922355)
    ·
      refine ⟨630096060245904175550883533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420064040163936117033922355 630096060245904175550883533)
      ·
        refine ⟨236286022592214065831581325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 630096060245904175550883533 236286022592214065831581325)
        ·
          refine ⟨88607258472080274686842997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236286022592214065831581325 88607258472080274686842997)
          ·
            refine ⟨8306930481757525751891531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 88607258472080274686842997 8306930481757525751891531)
            ·
              refine ⟨12460395722636288627837297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8306930481757525751891531 12460395722636288627837297)
              ·
                refine ⟨9345296791977216470877973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12460395722636288627837297 9345296791977216470877973)
                ·
                  refine ⟨438060787123932022072405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9345296791977216470877973 438060787123932022072405)
                  ·
                    rfl

theorem cell23_7678083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 6].length) (baseStart_7678083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678083 prefixEnd_7678083 := by exact prefixLift 7678083
  have htrace : WordTrace (prefixWord ++ tailWord_7678083) baseStart_7678083 baseEnd_7678083 := by
    simpa [prefixWord, tailWord_7678083, baseEnd_7678083] using wordTrace_append hprefix tailTrace_7678083
  have hstable : (prefixWord ++ tailWord_7678083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678083).length < 2 ^ (prefixWord ++ tailWord_7678083).sum := by decide
  have hdescent : baseEnd_7678083 < baseStart_7678083 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678113 : List Nat := [1, 2, 3, 3, 1, 2, 1, 4, 1, 5]
def baseStart_7678113 : Nat := 118140960795 + 7678113 * 2 ^ 59
def prefixEnd_7678113 : Nat := 4983230072969 + 3 ^ 40 * 7678113 * 2
def baseEnd_7678113 : Nat := 1314187496178341027092169

theorem tailTrace_7678113 : CollatzResearch.WordTrace tailWord_7678113 prefixEnd_7678113 1314187496178341027092169 := by
  unfold tailWord_7678113
  simp only [CollatzResearch.WordTrace]
  refine ⟨280043787632515393146206993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186695858421676928764137995 280043787632515393146206993)
  ·
    refine ⟨210032840724386544859655245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280043787632515393146206993 210032840724386544859655245)
    ·
      refine ⟨78762315271644954322370717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210032840724386544859655245 78762315271644954322370717)
      ·
        refine ⟨29535868226866857870889019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78762315271644954322370717 29535868226866857870889019)
        ·
          refine ⟨44303802340300286806333529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29535868226866857870889019 44303802340300286806333529)
          ·
            refine ⟨33227851755225215104750147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44303802340300286806333529 33227851755225215104750147)
            ·
              refine ⟨49841777632837822657125221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33227851755225215104750147 49841777632837822657125221)
              ·
                refine ⟨9345333306157091748210979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49841777632837822657125221 9345333306157091748210979)
                ·
                  refine ⟨14017999959235637622316469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9345333306157091748210979 14017999959235637622316469)
                  ·
                    refine ⟨1314187496178341027092169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14017999959235637622316469 1314187496178341027092169)
                    ·
                      rfl

theorem cell23_7678113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_7678113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678113 prefixEnd_7678113 := by exact prefixLift 7678113
  have htrace : WordTrace (prefixWord ++ tailWord_7678113) baseStart_7678113 baseEnd_7678113 := by
    simpa [prefixWord, tailWord_7678113, baseEnd_7678113] using wordTrace_append hprefix tailTrace_7678113
  have hstable : (prefixWord ++ tailWord_7678113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678113).length < 2 ^ (prefixWord ++ tailWord_7678113).sum := by decide
  have hdescent : baseEnd_7678113 < baseStart_7678113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678143 : List Nat := [1, 1, 2, 2, 2, 2, 1, 6, 2, 4]
def baseStart_7678143 : Nat := 118140960795 + 7678143 * 2 ^ 59
def prefixEnd_7678143 : Nat := 4983230072969 + 3 ^ 40 * 7678143 * 2
def baseEnd_7678143 : Nat := 1314192630984885987967123

theorem tailTrace_7678143 : CollatzResearch.WordTrace tailWord_7678143 prefixEnd_7678143 1314192630984885987967123 := by
  unfold tailWord_7678143
  simp only [CollatzResearch.WordTrace]
  refine ⟨280044881822406708269799083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186696587881604472179866055 280044881822406708269799083)
  ·
    refine ⟨420067322733610062404698625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280044881822406708269799083 420067322733610062404698625)
    ·
      refine ⟨315050492050207546803523969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420067322733610062404698625 315050492050207546803523969)
      ·
        refine ⟨236287869037655660102642977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315050492050207546803523969 236287869037655660102642977)
        ·
          refine ⟨177215901778241745076982233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236287869037655660102642977 177215901778241745076982233)
          ·
            refine ⟨132911926333681308807736675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177215901778241745076982233 132911926333681308807736675)
            ·
              refine ⟨199367889500521963211605013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132911926333681308807736675 199367889500521963211605013)
              ·
                refine ⟨9345369820336967025543985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 199367889500521963211605013 9345369820336967025543985)
                ·
                  refine ⟨7009027365252725269157989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9345369820336967025543985 7009027365252725269157989)
                  ·
                    refine ⟨1314192630984885987967123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7009027365252725269157989 1314192630984885987967123)
                    ·
                      rfl

theorem cell23_7678143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 4].length) (baseStart_7678143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678143 prefixEnd_7678143 := by exact prefixLift 7678143
  have htrace : WordTrace (prefixWord ++ tailWord_7678143) baseStart_7678143 baseEnd_7678143 := by
    simpa [prefixWord, tailWord_7678143, baseEnd_7678143] using wordTrace_append hprefix tailTrace_7678143
  have hstable : (prefixWord ++ tailWord_7678143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678143).length < 2 ^ (prefixWord ++ tailWord_7678143).sum := by decide
  have hdescent : baseEnd_7678143 < baseStart_7678143 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678144 : List Nat := [2, 1, 1, 2, 5, 2, 3, 2, 1, 1, 3]
def baseStart_7678144 : Nat := 118140960795 + 7678144 * 2 ^ 59
def prefixEnd_7678144 : Nat := 4983230072969 + 3 ^ 40 * 7678144 * 2
def baseEnd_7678144 : Nat := 3942578406435312459988865

theorem tailTrace_7678144 : CollatzResearch.WordTrace tailWord_7678144 prefixEnd_7678144 3942578406435312459988865 := by
  unfold tailWord_7678144
  simp only [CollatzResearch.WordTrace]
  refine ⟨140022459147701542720292743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186696612196935390293723657 140022459147701542720292743)
  ·
    refine ⟨210033688721552314080439115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140022459147701542720292743 210033688721552314080439115)
    ·
      refine ⟨315050533082328471120658673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210033688721552314080439115 315050533082328471120658673)
      ·
        refine ⟨236287899811746353340494005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315050533082328471120658673 236287899811746353340494005)
        ·
          refine ⟨22151990607351220625671313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 236287899811746353340494005 22151990607351220625671313)
          ·
            refine ⟨16613992955513415469253485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22151990607351220625671313 16613992955513415469253485)
            ·
              refine ⟨6230247358317530800970057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16613992955513415469253485 6230247358317530800970057)
              ·
                refine ⟨4672685518738148100727543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6230247358317530800970057 4672685518738148100727543)
                ·
                  refine ⟨7009028278107222151091315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4672685518738148100727543 7009028278107222151091315)
                  ·
                    refine ⟨10513542417160833226636973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7009028278107222151091315 10513542417160833226636973)
                    ·
                      refine ⟨3942578406435312459988865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10513542417160833226636973 3942578406435312459988865)
                      ·
                        rfl

theorem cell23_7678144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 2, 1, 1, 3].length) (baseStart_7678144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678144 prefixEnd_7678144 := by exact prefixLift 7678144
  have htrace : WordTrace (prefixWord ++ tailWord_7678144) baseStart_7678144 baseEnd_7678144 := by
    simpa [prefixWord, tailWord_7678144, baseEnd_7678144] using wordTrace_append hprefix tailTrace_7678144
  have hstable : (prefixWord ++ tailWord_7678144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678144).length < 2 ^ (prefixWord ++ tailWord_7678144).sum := by decide
  have hdescent : baseEnd_7678144 < baseStart_7678144 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678170 : List Nat := [3, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3]
def baseStart_7678170 : Nat := 118140960795 + 7678170 * 2 ^ 59
def prefixEnd_7678170 : Nat := 4983230072969 + 3 ^ 40 * 7678170 * 2
def baseEnd_7678170 : Nat := 3942591756932329358263745

theorem tailTrace_7678170 : CollatzResearch.WordTrace tailWord_7678170 prefixEnd_7678170 3942591756932329358263745 := by
  unfold tailWord_7678170
  simp only [CollatzResearch.WordTrace]
  refine ⟨70011466648327222970257991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186697244395539261254021309 70011466648327222970257991)
  ·
    refine ⟨105017199972490834455386987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70011466648327222970257991 105017199972490834455386987)
    ·
      refine ⟨157525799958736251683080481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105017199972490834455386987 157525799958736251683080481)
      ·
        refine ⟨118144349969052188762310361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157525799958736251683080481 118144349969052188762310361)
        ·
          refine ⟨88608262476789141571732771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118144349969052188762310361 88608262476789141571732771)
          ·
            refine ⟨132912393715183712357599157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88608262476789141571732771 132912393715183712357599157)
            ·
              refine ⟨12460536910798473033524921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 132912393715183712357599157 12460536910798473033524921)
              ·
                refine ⟨9345402683098854775143691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12460536910798473033524921 9345402683098854775143691)
                ·
                  refine ⟨14018104024648282162715537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9345402683098854775143691 14018104024648282162715537)
                  ·
                    refine ⟨10513578018486211622036653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14018104024648282162715537 10513578018486211622036653)
                    ·
                      refine ⟨3942591756932329358263745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10513578018486211622036653 3942591756932329358263745)
                      ·
                        rfl

theorem cell23_7678170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3].length) (baseStart_7678170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678170 prefixEnd_7678170 := by exact prefixLift 7678170
  have htrace : WordTrace (prefixWord ++ tailWord_7678170) baseStart_7678170 baseEnd_7678170 := by
    simpa [prefixWord, tailWord_7678170, baseEnd_7678170] using wordTrace_append hprefix tailTrace_7678170
  have hstable : (prefixWord ++ tailWord_7678170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678170).length < 2 ^ (prefixWord ++ tailWord_7678170).sum := by decide
  have hdescent : baseEnd_7678170 < baseStart_7678170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678173 : List Nat := [1, 4, 3, 2, 1, 1, 2, 9]
def baseStart_7678173 : Nat := 118140960795 + 7678173 * 2 ^ 59
def prefixEnd_7678173 : Nat := 4983230072969 + 3 ^ 40 * 7678173 * 2
def baseEnd_7678173 : Nat := 146021973976825660982453

theorem tailTrace_7678173 : CollatzResearch.WordTrace tailWord_7678173 prefixEnd_7678173 146021973976825660982453 := by
  unfold tailWord_7678173
  simp only [CollatzResearch.WordTrace]
  refine ⟨280045976012298023393391173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186697317341532015595594115 280045976012298023393391173)
  ·
    refine ⟨52508620502305879386260845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280045976012298023393391173 52508620502305879386260845)
    ·
      refine ⟨19690732688364704769847817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52508620502305879386260845 19690732688364704769847817)
      ·
        refine ⟨14768049516273528577385863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19690732688364704769847817 14768049516273528577385863)
        ·
          refine ⟨22152074274410292866078795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14768049516273528577385863 22152074274410292866078795)
          ·
            refine ⟨33228111411615439299118193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22152074274410292866078795 33228111411615439299118193)
            ·
              refine ⟨24921083558711579474338645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33228111411615439299118193 24921083558711579474338645)
              ·
                refine ⟨146021973976825660982453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24921083558711579474338645 146021973976825660982453)
                ·
                  rfl

theorem cell23_7678173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 9].length) (baseStart_7678173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678173 prefixEnd_7678173 := by exact prefixLift 7678173
  have htrace : WordTrace (prefixWord ++ tailWord_7678173) baseStart_7678173 baseEnd_7678173 := by
    simpa [prefixWord, tailWord_7678173, baseEnd_7678173] using wordTrace_append hprefix tailTrace_7678173
  have hstable : (prefixWord ++ tailWord_7678173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678173).length < 2 ^ (prefixWord ++ tailWord_7678173).sum := by decide
  have hdescent : baseEnd_7678173 < baseStart_7678173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678244 : List Nat := [2, 3, 1, 3, 1, 2, 4, 1, 1, 3, 2]
def baseStart_7678244 : Nat := 118140960795 + 7678244 * 2 ^ 59
def prefixEnd_7678244 : Nat := 4983230072969 + 3 ^ 40 * 7678244 * 2
def baseEnd_7678244 : Nat := 3942629754500762068738405

theorem tailTrace_7678244 : CollatzResearch.WordTrace tailWord_7678244 prefixEnd_7678244 3942629754500762068738405 := by
  unfold tailWord_7678244
  simp only [CollatzResearch.WordTrace]
  refine ⟨140024282797520401259612893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186699043730027201679483857 140024282797520401259612893)
  ·
    refine ⟨52509106049070150472354835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140024282797520401259612893 52509106049070150472354835)
    ·
      refine ⟨78763659073605225708532253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52509106049070150472354835 78763659073605225708532253)
      ·
        refine ⟨29536372152601959640699595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78763659073605225708532253 29536372152601959640699595)
        ·
          refine ⟨44304558228902939461049393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29536372152601959640699595 44304558228902939461049393)
          ·
            refine ⟨33228418671677204595787045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44304558228902939461049393 33228418671677204595787045)
            ·
              refine ⟨6230328500939475861710071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33228418671677204595787045 6230328500939475861710071)
              ·
                refine ⟨9345492751409213792565107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6230328500939475861710071 9345492751409213792565107)
                ·
                  refine ⟨14018239127113820688847661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9345492751409213792565107 14018239127113820688847661)
                  ·
                    refine ⟨5256839672667682758317873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14018239127113820688847661 5256839672667682758317873)
                    ·
                      refine ⟨3942629754500762068738405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5256839672667682758317873 3942629754500762068738405)
                      ·
                        rfl

theorem cell23_7678244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_7678244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678244 prefixEnd_7678244 := by exact prefixLift 7678244
  have htrace : WordTrace (prefixWord ++ tailWord_7678244) baseStart_7678244 baseEnd_7678244 := by
    simpa [prefixWord, tailWord_7678244, baseEnd_7678244] using wordTrace_append hprefix tailTrace_7678244
  have hstable : (prefixWord ++ tailWord_7678244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678244).length < 2 ^ (prefixWord ++ tailWord_7678244).sum := by decide
  have hdescent : baseEnd_7678244 < baseStart_7678244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678256 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 9]
def baseStart_7678256 : Nat := 118140960795 + 7678256 * 2 ^ 59
def prefixEnd_7678256 : Nat := 4983230072969 + 3 ^ 40 * 7678256 * 2
def baseEnd_7678256 : Nat := 3942635916268616021788349

theorem tailTrace_7678256 : CollatzResearch.WordTrace tailWord_7678256 prefixEnd_7678256 3942635916268616021788349 := by
  unfold tailWord_7678256
  simp only [CollatzResearch.WordTrace]
  refine ⟨140024501635498664284331311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186699335513998219045775081 140024501635498664284331311)
  ·
    refine ⟨210036752453247996426496967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140024501635498664284331311 210036752453247996426496967)
    ·
      refine ⟨315055128679871994639745451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210036752453247996426496967 315055128679871994639745451)
      ·
        refine ⟨472582693019807991959618177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315055128679871994639745451 472582693019807991959618177)
        ·
          refine ⟨354437019764855993969713633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472582693019807991959618177 354437019764855993969713633)
          ·
            refine ⟨265827764823641995477285225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354437019764855993969713633 265827764823641995477285225)
            ·
              refine ⟨199370823617731496607963919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265827764823641995477285225 199370823617731496607963919)
              ·
                refine ⟨299056235426597244911945879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199370823617731496607963919 299056235426597244911945879)
                ·
                  refine ⟨448584353139895867367918819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 299056235426597244911945879 448584353139895867367918819)
                  ·
                    refine ⟨672876529709843801051878229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 448584353139895867367918819 672876529709843801051878229)
                    ·
                      refine ⟨3942635916268616021788349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 672876529709843801051878229 3942635916268616021788349)
                      ·
                        rfl

theorem cell23_7678256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_7678256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678256 prefixEnd_7678256 := by exact prefixLift 7678256
  have htrace : WordTrace (prefixWord ++ tailWord_7678256) baseStart_7678256 baseEnd_7678256 := by
    simpa [prefixWord, tailWord_7678256, baseEnd_7678256] using wordTrace_append hprefix tailTrace_7678256
  have hstable : (prefixWord ++ tailWord_7678256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678256).length < 2 ^ (prefixWord ++ tailWord_7678256).sum := by decide
  have hdescent : baseEnd_7678256 < baseStart_7678256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678270 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_7678270 : Nat := 118140960795 + 7678270 * 2 ^ 59
def prefixEnd_7678270 : Nat := 4983230072969 + 3 ^ 40 * 7678270 * 2
def baseEnd_7678270 : Nat := 3942643104997778967013285

theorem tailTrace_7678270 : CollatzResearch.WordTrace tailWord_7678270 prefixEnd_7678270 3942643104997778967013285 := by
  unfold tailWord_7678270
  simp only [CollatzResearch.WordTrace]
  refine ⟨35006189236618326119959033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186699675928631072639781509 35006189236618326119959033)
  ·
    refine ⟨26254641927463744589969275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35006189236618326119959033 26254641927463744589969275)
    ·
      refine ⟨39381962891195616884953913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26254641927463744589969275 39381962891195616884953913)
      ·
        refine ⟨29536472168396712663715435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39381962891195616884953913 29536472168396712663715435)
        ·
          refine ⟨44304708252595068995573153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29536472168396712663715435 44304708252595068995573153)
          ·
            refine ⟨33228531189446301746679865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44304708252595068995573153 33228531189446301746679865)
            ·
              refine ⟨24921398392084726310009899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33228531189446301746679865 24921398392084726310009899)
              ·
                refine ⟨37382097588127089465014849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24921398392084726310009899 37382097588127089465014849)
                ·
                  refine ⟨28036573191095317098761137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37382097588127089465014849 28036573191095317098761137)
                  ·
                    refine ⟨21027429893321487824070853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28036573191095317098761137 21027429893321487824070853)
                    ·
                      refine ⟨3942643104997778967013285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21027429893321487824070853 3942643104997778967013285)
                      ·
                        rfl

theorem cell23_7678270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_7678270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678270 prefixEnd_7678270 := by exact prefixLift 7678270
  have htrace : WordTrace (prefixWord ++ tailWord_7678270) baseStart_7678270 baseEnd_7678270 := by
    simpa [prefixWord, tailWord_7678270, baseEnd_7678270] using wordTrace_append hprefix tailTrace_7678270
  have hstable : (prefixWord ++ tailWord_7678270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678270).length < 2 ^ (prefixWord ++ tailWord_7678270).sum := by decide
  have hdescent : baseEnd_7678270 < baseStart_7678270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678314 : List Nat := [3, 1, 3, 3, 1, 2, 3, 2, 5]
def baseStart_7678314 : Nat := 118140960795 + 7678314 * 2 ^ 59
def prefixEnd_7678314 : Nat := 4983230072969 + 3 ^ 40 * 7678314 * 2
def baseEnd_7678314 : Nat := 438073966460730754984787

theorem tailTrace_7678314 : CollatzResearch.WordTrace tailWord_7678314 prefixEnd_7678314 438073966460730754984787 := by
  unfold tailWord_7678314
  simp only [CollatzResearch.WordTrace]
  refine ⟨70012779676196801118568499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186700745803191469649515997 70012779676196801118568499)
  ·
    refine ⟨105019169514295201677852749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70012779676196801118568499 105019169514295201677852749)
    ·
      refine ⟨39382188567860700629194781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105019169514295201677852749 39382188567860700629194781)
      ·
        refine ⟨14768320712947762735948043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39382188567860700629194781 14768320712947762735948043)
        ·
          refine ⟨22152481069421644103922065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14768320712947762735948043 22152481069421644103922065)
          ·
            refine ⟨16614360802066233077941549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22152481069421644103922065 16614360802066233077941549)
            ·
              refine ⟨6230385300774837404228081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16614360802066233077941549 6230385300774837404228081)
              ·
                refine ⟨4672788975581128053171061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6230385300774837404228081 4672788975581128053171061)
                ·
                  refine ⟨438073966460730754984787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4672788975581128053171061 438073966460730754984787)
                  ·
                    rfl

theorem cell23_7678314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 5].length) (baseStart_7678314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678314 prefixEnd_7678314 := by exact prefixLift 7678314
  have htrace : WordTrace (prefixWord ++ tailWord_7678314) baseStart_7678314 baseEnd_7678314 := by
    simpa [prefixWord, tailWord_7678314, baseEnd_7678314] using wordTrace_append hprefix tailTrace_7678314
  have hstable : (prefixWord ++ tailWord_7678314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678314).length < 2 ^ (prefixWord ++ tailWord_7678314).sum := by decide
  have hdescent : baseEnd_7678314 < baseStart_7678314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678340 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 5, 4]
def baseStart_7678340 : Nat := 118140960795 + 7678340 * 2 ^ 59
def prefixEnd_7678340 : Nat := 4983230072969 + 3 ^ 40 * 7678340 * 2
def baseEnd_7678340 : Nat := 1314226349547864564379321

theorem tailTrace_7678340 : CollatzResearch.WordTrace tailWord_7678340 prefixEnd_7678340 1314226349547864564379321 := by
  unfold tailWord_7678340
  simp only [CollatzResearch.WordTrace]
  refine ⟨140026033501346505457360237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186701378001795340609813649 140026033501346505457360237)
  ·
    refine ⟨52509762563004939546510089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140026033501346505457360237 52509762563004939546510089)
    ·
      refine ⟨39382321922253704659882567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52509762563004939546510089 39382321922253704659882567)
      ·
        refine ⟨59073482883380556989823851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39382321922253704659882567 59073482883380556989823851)
        ·
          refine ⟨88610224325070835484735777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59073482883380556989823851 88610224325070835484735777)
          ·
            refine ⟨66457668243803126613551833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88610224325070835484735777 66457668243803126613551833)
            ·
              refine ⟨49843251182852344960163875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66457668243803126613551833 49843251182852344960163875)
              ·
                refine ⟨74764876774278517440245813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49843251182852344960163875 74764876774278517440245813)
                ·
                  refine ⟨7009207197588611010023045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74764876774278517440245813 7009207197588611010023045)
                  ·
                    refine ⟨1314226349547864564379321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7009207197588611010023045 1314226349547864564379321)
                    ·
                      rfl

theorem cell23_7678340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_7678340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678340 prefixEnd_7678340 := by exact prefixLift 7678340
  have htrace : WordTrace (prefixWord ++ tailWord_7678340) baseStart_7678340 baseEnd_7678340 := by
    simpa [prefixWord, tailWord_7678340, baseEnd_7678340] using wordTrace_append hprefix tailTrace_7678340
  have hstable : (prefixWord ++ tailWord_7678340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678340).length < 2 ^ (prefixWord ++ tailWord_7678340).sum := by decide
  have hdescent : baseEnd_7678340 < baseStart_7678340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678357 : List Nat := [1, 3, 2, 1, 1, 2, 1, 7, 1, 4]
def baseStart_7678357 : Nat := 118140960795 + 7678357 * 2 ^ 59
def prefixEnd_7678357 : Nat := 4983230072969 + 3 ^ 40 * 7678357 * 2
def baseEnd_7678357 : Nat := 1314229259271573375541795

theorem tailTrace_7678357 : CollatzResearch.WordTrace tailWord_7678357 prefixEnd_7678357 1314229259271573375541795 := by
  unfold tailWord_7678357
  simp only [CollatzResearch.WordTrace]
  refine ⟨280052687043631422818089325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186701791362420948545392883 280052687043631422818089325)
  ·
    refine ⟨105019757641361783556783497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280052687043631422818089325 105019757641361783556783497)
    ·
      refine ⟨78764818231021337667587623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105019757641361783556783497 78764818231021337667587623)
      ·
        refine ⟨118147227346532006501381435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78764818231021337667587623 118147227346532006501381435)
        ·
          refine ⟨177220841019798009752072153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118147227346532006501381435 177220841019798009752072153)
          ·
            refine ⟨132915630764848507314054115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177220841019798009752072153 132915630764848507314054115)
            ·
              refine ⟨199373446147272760971081173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132915630764848507314054115 199373446147272760971081173)
              ·
                refine ⟨4672815144076705335259715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 199373446147272760971081173 4672815144076705335259715)
                ·
                  refine ⟨7009222716115058002889573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4672815144076705335259715 7009222716115058002889573)
                  ·
                    refine ⟨1314229259271573375541795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7009222716115058002889573 1314229259271573375541795)
                    ·
                      rfl

theorem cell23_7678357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_7678357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678357 prefixEnd_7678357 := by exact prefixLift 7678357
  have htrace : WordTrace (prefixWord ++ tailWord_7678357) baseStart_7678357 baseEnd_7678357 := by
    simpa [prefixWord, tailWord_7678357, baseEnd_7678357] using wordTrace_append hprefix tailTrace_7678357
  have hstable : (prefixWord ++ tailWord_7678357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678357).length < 2 ^ (prefixWord ++ tailWord_7678357).sum := by decide
  have hdescent : baseEnd_7678357 < baseStart_7678357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678373 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 1, 2, 6]
def baseStart_7678373 : Nat := 118140960795 + 7678373 * 2 ^ 59
def prefixEnd_7678373 : Nat := 4983230072969 + 3 ^ 40 * 7678373 * 2
def baseEnd_7678373 : Nat := 3942695993505192064025311

theorem tailTrace_7678373 : CollatzResearch.WordTrace tailWord_7678373 prefixEnd_7678373 3942695993505192064025311 := by
  unfold tailWord_7678373
  simp only [CollatzResearch.WordTrace]
  refine ⟨280053270611573457550671773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186702180407715638367114515 280053270611573457550671773)
  ·
    refine ⟨105019976479340046581501915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280053270611573457550671773 105019976479340046581501915)
    ·
      refine ⟨157529964719010069872252873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105019976479340046581501915 157529964719010069872252873)
      ·
        refine ⟨118147473539257552404189655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157529964719010069872252873 118147473539257552404189655)
        ·
          refine ⟨177221210308886328606284483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118147473539257552404189655 177221210308886328606284483)
          ·
            refine ⟨265831815463329492909426725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177221210308886328606284483 265831815463329492909426725)
            ·
              refine ⟨49843465399374279920517511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265831815463329492909426725 49843465399374279920517511)
              ·
                refine ⟨74765198099061419880776267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49843465399374279920517511 74765198099061419880776267)
                ·
                  refine ⟨112147797148592129821164401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74765198099061419880776267 112147797148592129821164401)
                  ·
                    refine ⟨84110847861444097365873301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112147797148592129821164401 84110847861444097365873301)
                    ·
                      refine ⟨3942695993505192064025311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84110847861444097365873301 3942695993505192064025311)
                      ·
                        rfl

theorem cell23_7678373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_7678373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678373 prefixEnd_7678373 := by exact prefixLift 7678373
  have htrace : WordTrace (prefixWord ++ tailWord_7678373) baseStart_7678373 baseEnd_7678373 := by
    simpa [prefixWord, tailWord_7678373, baseEnd_7678373] using wordTrace_append hprefix tailTrace_7678373
  have hstable : (prefixWord ++ tailWord_7678373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678373).length < 2 ^ (prefixWord ++ tailWord_7678373).sum := by decide
  have hdescent : baseEnd_7678373 < baseStart_7678373 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678397 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 5, 1, 3]
def baseStart_7678397 : Nat := 118140960795 + 7678397 * 2 ^ 59
def prefixEnd_7678397 : Nat := 4983230072969 + 3 ^ 40 * 7678397 * 2
def baseEnd_7678397 : Nat := 3942708317040899970125201

theorem tailTrace_7678397 : CollatzResearch.WordTrace tailWord_7678397 prefixEnd_7678397 3942708317040899970125201 := by
  unfold tailWord_7678397
  simp only [CollatzResearch.WordTrace]
  refine ⟨280054145963486509649545445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186702763975657673099696963 280054145963486509649545445)
  ·
    refine ⟨52510152368153720559289771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280054145963486509649545445 52510152368153720559289771)
    ·
      refine ⟨78765228552230580838934657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52510152368153720559289771 78765228552230580838934657)
      ·
        refine ⟨59073921414172935629200993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78765228552230580838934657 59073921414172935629200993)
        ·
          refine ⟨44305441060629701721900745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59073921414172935629200993 44305441060629701721900745)
          ·
            refine ⟨33229080795472276291425559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44305441060629701721900745 33229080795472276291425559)
            ·
              refine ⟨49843621193208414437138339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33229080795472276291425559 49843621193208414437138339)
              ·
                refine ⟨74765431789812621655707509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49843621193208414437138339 74765431789812621655707509)
                ·
                  refine ⟨7009259230294933280222579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74765431789812621655707509 7009259230294933280222579)
                  ·
                    refine ⟨10513888845442399920333869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7009259230294933280222579 10513888845442399920333869)
                    ·
                      refine ⟨3942708317040899970125201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10513888845442399920333869 3942708317040899970125201)
                      ·
                        rfl

theorem cell23_7678397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_7678397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678397 prefixEnd_7678397 := by exact prefixLift 7678397
  have htrace : WordTrace (prefixWord ++ tailWord_7678397) baseStart_7678397 baseEnd_7678397 := by
    simpa [prefixWord, tailWord_7678397, baseEnd_7678397] using wordTrace_append hprefix tailTrace_7678397
  have hstable : (prefixWord ++ tailWord_7678397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678397).length < 2 ^ (prefixWord ++ tailWord_7678397).sum := by decide
  have hdescent : baseEnd_7678397 < baseStart_7678397 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678400 : List Nat := [2, 1, 1, 2, 3, 1, 1, 6, 1, 5]
def baseStart_7678400 : Nat := 118140960795 + 7678400 * 2 ^ 59
def prefixEnd_7678400 : Nat := 4983230072969 + 3 ^ 40 * 7678400 * 2
def baseEnd_7678400 : Nat := 1314236619160954486129229

theorem tailTrace_7678400 : CollatzResearch.WordTrace tailWord_7678400 prefixEnd_7678400 1314236619160954486129229 := by
  unfold tailWord_7678400
  simp only [CollatzResearch.WordTrace]
  refine ⟨140027127691237820580952327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186702836921650427441269769 140027127691237820580952327)
  ·
    refine ⟨210040691536856730871428491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140027127691237820580952327 210040691536856730871428491)
    ·
      refine ⟨315061037305285096307142737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210040691536856730871428491 315061037305285096307142737)
      ·
        refine ⟨236295777978963822230357053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315061037305285096307142737 236295777978963822230357053)
        ·
          refine ⟨88610916742111433336383895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236295777978963822230357053 88610916742111433336383895)
          ·
            refine ⟨132916375113167150004575843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88610916742111433336383895 132916375113167150004575843)
            ·
              refine ⟨199374562669750725006863765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132916375113167150004575843 199374562669750725006863765)
              ·
                refine ⟨9345682625144565234696739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 199374562669750725006863765 9345682625144565234696739)
                ·
                  refine ⟨14018523937716847852045109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9345682625144565234696739 14018523937716847852045109)
                  ·
                    refine ⟨1314236619160954486129229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14018523937716847852045109 1314236619160954486129229)
                    ·
                      rfl

theorem cell23_7678400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 1, 5].length) (baseStart_7678400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678400 prefixEnd_7678400 := by exact prefixLift 7678400
  have htrace : WordTrace (prefixWord ++ tailWord_7678400) baseStart_7678400 baseEnd_7678400 := by
    simpa [prefixWord, tailWord_7678400, baseEnd_7678400] using wordTrace_append hprefix tailTrace_7678400
  have hstable : (prefixWord ++ tailWord_7678400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678400).length < 2 ^ (prefixWord ++ tailWord_7678400).sum := by decide
  have hdescent : baseEnd_7678400 < baseStart_7678400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678401 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_7678401 : Nat := 118140960795 + 7678401 * 2 ^ 59
def prefixEnd_7678401 : Nat := 4983230072969 + 3 ^ 40 * 7678401 * 2
def baseEnd_7678401 : Nat := 3942710370963517954475183

theorem tailTrace_7678401 : CollatzResearch.WordTrace tailWord_7678401 prefixEnd_7678401 3942710370963517954475183 := by
  unfold tailWord_7678401
  simp only [CollatzResearch.WordTrace]
  refine ⟨280054291855472018332691057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186702861236981345555127371 280054291855472018332691057)
  ·
    refine ⟨210040718891604013749518293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280054291855472018332691057 210040718891604013749518293)
    ·
      refine ⟨4922829349021969072254335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 210040718891604013749518293 4922829349021969072254335)
      ·
        refine ⟨7384244023532953608381503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4922829349021969072254335 7384244023532953608381503)
        ·
          refine ⟨11076366035299430412572255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7384244023532953608381503 11076366035299430412572255)
          ·
            refine ⟨16614549052949145618858383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11076366035299430412572255 16614549052949145618858383)
            ·
              refine ⟨24921823579423718428287575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16614549052949145618858383 24921823579423718428287575)
              ·
                refine ⟨37382735369135577642431363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24921823579423718428287575 37382735369135577642431363)
                ·
                  refine ⟨56074103053703366463647045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37382735369135577642431363 56074103053703366463647045)
                  ·
                    refine ⟨10513894322569381211933821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56074103053703366463647045 10513894322569381211933821)
                    ·
                      refine ⟨3942710370963517954475183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10513894322569381211933821 3942710370963517954475183)
                      ·
                        rfl

theorem cell23_7678401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_7678401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678401 prefixEnd_7678401 := by exact prefixLift 7678401
  have htrace : WordTrace (prefixWord ++ tailWord_7678401) baseStart_7678401 baseEnd_7678401 := by
    simpa [prefixWord, tailWord_7678401, baseEnd_7678401] using wordTrace_append hprefix tailTrace_7678401
  have hstable : (prefixWord ++ tailWord_7678401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678401).length < 2 ^ (prefixWord ++ tailWord_7678401).sum := by decide
  have hdescent : baseEnd_7678401 < baseStart_7678401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678407 : List Nat := [1, 1, 4, 1, 1, 5, 1, 1, 1, 5, 2]
def baseStart_7678407 : Nat := 118140960795 + 7678407 * 2 ^ 59
def prefixEnd_7678407 : Nat := 4983230072969 + 3 ^ 40 * 7678407 * 2
def baseEnd_7678407 : Nat := 3942713451847444931000155

theorem tailTrace_7678407 : CollatzResearch.WordTrace tailWord_7678407 prefixEnd_7678407 3942713451847444931000155 := by
  unfold tailWord_7678407
  simp only [CollatzResearch.WordTrace]
  refine ⟨280054510693450281357409475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186703007128966854238272983 280054510693450281357409475)
  ·
    refine ⟨420081766040175422036114213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280054510693450281357409475 420081766040175422036114213)
    ·
      refine ⟨78765331132532891631771415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 420081766040175422036114213 78765331132532891631771415)
      ·
        refine ⟨118147996698799337447657123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78765331132532891631771415 118147996698799337447657123)
        ·
          refine ⟨177221995048199006171485685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118147996698799337447657123 177221995048199006171485685)
          ·
            refine ⟨16614562035768656828576783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 177221995048199006171485685 16614562035768656828576783)
            ·
              refine ⟨24921843053652985242865175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16614562035768656828576783 24921843053652985242865175)
              ·
                refine ⟨37382764580479477864297763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24921843053652985242865175 37382764580479477864297763)
                ·
                  refine ⟨56074146870719216796446645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37382764580479477864297763 56074146870719216796446645)
                  ·
                    refine ⟨5256951269129926574666873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56074146870719216796446645 5256951269129926574666873)
                    ·
                      refine ⟨3942713451847444931000155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5256951269129926574666873 3942713451847444931000155)
                      ·
                        rfl

theorem cell23_7678407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 5, 2].length) (baseStart_7678407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678407 prefixEnd_7678407 := by exact prefixLift 7678407
  have htrace : WordTrace (prefixWord ++ tailWord_7678407) baseStart_7678407 baseEnd_7678407 := by
    simpa [prefixWord, tailWord_7678407, baseEnd_7678407] using wordTrace_append hprefix tailTrace_7678407
  have hstable : (prefixWord ++ tailWord_7678407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678407).length < 2 ^ (prefixWord ++ tailWord_7678407).sum := by decide
  have hdescent : baseEnd_7678407 < baseStart_7678407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678440 : List Nat := [2, 1, 4, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_7678440 : Nat := 118140960795 + 7678440 * 2 ^ 59
def prefixEnd_7678440 : Nat := 4983230072969 + 3 ^ 40 * 7678440 * 2
def baseEnd_7678440 : Nat := 3942730396709043301887503

theorem tailTrace_7678440 : CollatzResearch.WordTrace tailWord_7678440 prefixEnd_7678440 3942730396709043301887503 := by
  unfold tailWord_7678440
  simp only [CollatzResearch.WordTrace]
  refine ⟨140027857151165363996680387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186703809534887151995573849 140027857151165363996680387)
  ·
    refine ⟨210041785726748045995020581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140027857151165363996680387 210041785726748045995020581)
    ·
      refine ⟨39382834823765258624066359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210041785726748045995020581 39382834823765258624066359)
      ·
        refine ⟨59074252235647887936099539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39382834823765258624066359 59074252235647887936099539)
        ·
          refine ⟨88611378353471831904149309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59074252235647887936099539 88611378353471831904149309)
          ·
            refine ⟨33229266882551936964055991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88611378353471831904149309 33229266882551936964055991)
            ·
              refine ⟨49843900323827905446083987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33229266882551936964055991 49843900323827905446083987)
              ·
                refine ⟨74765850485741858169125981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49843900323827905446083987 74765850485741858169125981)
                ·
                  refine ⟨28037193932153196813422243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74765850485741858169125981 28037193932153196813422243)
                  ·
                    refine ⟨42055790898229795220133365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28037193932153196813422243 42055790898229795220133365)
                    ·
                      refine ⟨3942730396709043301887503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42055790898229795220133365 3942730396709043301887503)
                      ·
                        rfl

theorem cell23_7678440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_7678440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678440 prefixEnd_7678440 := by exact prefixLift 7678440
  have htrace : WordTrace (prefixWord ++ tailWord_7678440) baseStart_7678440 baseEnd_7678440 := by
    simpa [prefixWord, tailWord_7678440, baseEnd_7678440] using wordTrace_append hprefix tailTrace_7678440
  have hstable : (prefixWord ++ tailWord_7678440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678440).length < 2 ^ (prefixWord ++ tailWord_7678440).sum := by decide
  have hdescent : baseEnd_7678440 < baseStart_7678440 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678443 : List Nat := [1, 1, 1, 1, 2, 3, 4, 10]
def baseStart_7678443 : Nat := 118140960795 + 7678443 * 2 ^ 59
def prefixEnd_7678443 : Nat := 4983230072969 + 3 ^ 40 * 7678443 * 2
def baseEnd_7678443 : Nat := 146027108783370621857407

theorem tailTrace_7678443 : CollatzResearch.WordTrace tailWord_7678443 prefixEnd_7678443 146027108783370621857407 := by
  unfold tailWord_7678443
  simp only [CollatzResearch.WordTrace]
  refine ⟨280055823721319859505719983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186703882480879906337146655 280055823721319859505719983)
  ·
    refine ⟨420083735581979789258579975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280055823721319859505719983 420083735581979789258579975)
    ·
      refine ⟨630125603372969683887869963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420083735581979789258579975 630125603372969683887869963)
      ·
        refine ⟨945188405059454525831804945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630125603372969683887869963 945188405059454525831804945)
        ·
          refine ⟨708891303794590894373853709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 945188405059454525831804945 708891303794590894373853709)
          ·
            refine ⟨265834238922971585390195141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 708891303794590894373853709 265834238922971585390195141)
            ·
              refine ⟨49843919798057172260661589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265834238922971585390195141 49843919798057172260661589)
              ·
                refine ⟨146027108783370621857407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 49843919798057172260661589 146027108783370621857407)
                ·
                  rfl

theorem cell23_7678443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 10].length) (baseStart_7678443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678443 prefixEnd_7678443 := by exact prefixLift 7678443
  have htrace : WordTrace (prefixWord ++ tailWord_7678443) baseStart_7678443 baseEnd_7678443 := by
    simpa [prefixWord, tailWord_7678443, baseEnd_7678443] using wordTrace_append hprefix tailTrace_7678443
  have hstable : (prefixWord ++ tailWord_7678443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678443).length < 2 ^ (prefixWord ++ tailWord_7678443).sum := by decide
  have hdescent : baseEnd_7678443 < baseStart_7678443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678454 : List Nat := [5, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_7678454 : Nat := 118140960795 + 7678454 * 2 ^ 59
def prefixEnd_7678454 : Nat := 4983230072969 + 3 ^ 40 * 7678454 * 2
def baseEnd_7678454 : Nat := 3942737585438206247112439

theorem tailTrace_7678454 : CollatzResearch.WordTrace tailWord_7678454 prefixEnd_7678454 3942737585438206247112439 := by
  unfold tailWord_7678454
  simp only [CollatzResearch.WordTrace]
  refine ⟨17503514057767500524023151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186704149949520005589580277 17503514057767500524023151)
  ·
    refine ⟨26255271086651250786034727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17503514057767500524023151 26255271086651250786034727)
    ·
      refine ⟨39382906629976876179052091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26255271086651250786034727 39382906629976876179052091)
      ·
        refine ⟨59074359944965314268578137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39382906629976876179052091 59074359944965314268578137)
        ·
          refine ⟨44305769958723985701433603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59074359944965314268578137 44305769958723985701433603)
          ·
            refine ⟨66458654938085978552150405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44305769958723985701433603 66458654938085978552150405)
            ·
              refine ⟨12460997800891120978528201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66458654938085978552150405 12460997800891120978528201)
              ·
                refine ⟨9345748350668340733896151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12460997800891120978528201 9345748350668340733896151)
                ·
                  refine ⟨14018622526002511100844227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9345748350668340733896151 14018622526002511100844227)
                  ·
                    refine ⟨21027933789003766651266341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14018622526002511100844227 21027933789003766651266341)
                    ·
                      refine ⟨3942737585438206247112439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21027933789003766651266341 3942737585438206247112439)
                      ·
                        rfl

theorem cell23_7678454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_7678454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678454 prefixEnd_7678454 := by exact prefixLift 7678454
  have htrace : WordTrace (prefixWord ++ tailWord_7678454) baseStart_7678454 baseEnd_7678454 := by
    simpa [prefixWord, tailWord_7678454, baseEnd_7678454] using wordTrace_append hprefix tailTrace_7678454
  have hstable : (prefixWord ++ tailWord_7678454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678454).length < 2 ^ (prefixWord ++ tailWord_7678454).sum := by decide
  have hdescent : baseEnd_7678454 < baseStart_7678454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678457 : List Nat := [1, 2, 1, 3, 1, 2, 3, 4, 1, 2, 3]
def baseStart_7678457 : Nat := 118140960795 + 7678457 * 2 ^ 59
def prefixEnd_7678457 : Nat := 4983230072969 + 3 ^ 40 * 7678457 * 2
def baseEnd_7678457 : Nat := 3942739125880169735374925

theorem tailTrace_7678457 : CollatzResearch.WordTrace tailWord_7678457 prefixEnd_7678457 3942739125880169735374925 := by
  unfold tailWord_7678457
  simp only [CollatzResearch.WordTrace]
  refine ⟨280056334343269139896729625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186704222895512759931153083 280056334343269139896729625)
  ·
    refine ⟨210042250757451854922547219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280056334343269139896729625 210042250757451854922547219)
    ·
      refine ⟨315063376136177782383820829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210042250757451854922547219 315063376136177782383820829)
      ·
        refine ⟨118148766051066668393932811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315063376136177782383820829 118148766051066668393932811)
        ·
          refine ⟨177223149076600002590899217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118148766051066668393932811 177223149076600002590899217)
          ·
            refine ⟨132917361807450001943174413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177223149076600002590899217 132917361807450001943174413)
            ·
              refine ⟨49844010677793750728690405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132917361807450001943174413 49844010677793750728690405)
              ·
                refine ⟨9345752002086328261629451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49844010677793750728690405 9345752002086328261629451)
                ·
                  refine ⟨14018628003129492392444177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9345752002086328261629451 14018628003129492392444177)
                  ·
                    refine ⟨10513971002347119294333133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14018628003129492392444177 10513971002347119294333133)
                    ·
                      refine ⟨3942739125880169735374925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10513971002347119294333133 3942739125880169735374925)
                      ·
                        rfl

theorem cell23_7678457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_7678457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678457 prefixEnd_7678457 := by exact prefixLift 7678457
  have htrace : WordTrace (prefixWord ++ tailWord_7678457) baseStart_7678457 baseEnd_7678457 := by
    simpa [prefixWord, tailWord_7678457, baseEnd_7678457] using wordTrace_append hprefix tailTrace_7678457
  have hstable : (prefixWord ++ tailWord_7678457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678457).length < 2 ^ (prefixWord ++ tailWord_7678457).sum := by decide
  have hdescent : baseEnd_7678457 < baseStart_7678457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678561 : List Nat := [1, 2, 3, 1, 1, 4, 2, 3, 2, 2, 2]
def baseStart_7678561 : Nat := 118140960795 + 7678561 * 2 ^ 59
def prefixEnd_7678561 : Nat := 4983230072969 + 3 ^ 40 * 7678561 * 2
def baseEnd_7678561 : Nat := 3942792527868237328474447

theorem tailTrace_7678561 : CollatzResearch.WordTrace tailWord_7678561 prefixEnd_7678561 3942792527868237328474447 := by
  unfold tailWord_7678561
  simp only [CollatzResearch.WordTrace]
  refine ⟨280060127534892365658515537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186706751689928243772343691 280060127534892365658515537)
  ·
    refine ⟨210045095651169274243886653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280060127534892365658515537 210045095651169274243886653)
    ·
      refine ⟨78766910869188477841457495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210045095651169274243886653 78766910869188477841457495)
      ·
        refine ⟨118150366303782716762186243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78766910869188477841457495 118150366303782716762186243)
        ·
          refine ⟨177225549455674075143279365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118150366303782716762186243 177225549455674075143279365)
          ·
            refine ⟨33229790522938889089364881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177225549455674075143279365 33229790522938889089364881)
            ·
              refine ⟨24922342892204166817023661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33229790522938889089364881 24922342892204166817023661)
              ·
                refine ⟨9345878584576562556383873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24922342892204166817023661 9345878584576562556383873)
                ·
                  refine ⟨7009408938432421917287905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9345878584576562556383873 7009408938432421917287905)
                  ·
                    refine ⟨5257056703824316437965929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7009408938432421917287905 5257056703824316437965929)
                    ·
                      refine ⟨3942792527868237328474447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5257056703824316437965929 3942792527868237328474447)
                      ·
                        rfl

theorem cell23_7678561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 3, 2, 2, 2].length) (baseStart_7678561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678561 prefixEnd_7678561 := by exact prefixLift 7678561
  have htrace : WordTrace (prefixWord ++ tailWord_7678561) baseStart_7678561 baseEnd_7678561 := by
    simpa [prefixWord, tailWord_7678561, baseEnd_7678561] using wordTrace_append hprefix tailTrace_7678561
  have hstable : (prefixWord ++ tailWord_7678561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678561).length < 2 ^ (prefixWord ++ tailWord_7678561).sum := by decide
  have hdescent : baseEnd_7678561 < baseStart_7678561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678582 : List Nat := [5, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2]
def baseStart_7678582 : Nat := 118140960795 + 7678582 * 2 ^ 59
def prefixEnd_7678582 : Nat := 4983230072969 + 3 ^ 40 * 7678582 * 2
def baseEnd_7678582 : Nat := 3942803310961981746311851

theorem tailTrace_7678582 : CollatzResearch.WordTrace tailWord_7678582 prefixEnd_7678582 3942803310961981746311851 := by
  unfold tailWord_7678582
  simp only [CollatzResearch.WordTrace]
  refine ⟨17503805841738517890314375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186707262311877524163353333 17503805841738517890314375)
  ·
    refine ⟨26255708762607776835471563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17503805841738517890314375 26255708762607776835471563)
    ·
      refine ⟨39383563143911665253207345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26255708762607776835471563 39383563143911665253207345)
      ·
        refine ⟨29537672357933748939905509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39383563143911665253207345 29537672357933748939905509)
        ·
          refine ⟨5538313567112577926232283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 29537672357933748939905509 5538313567112577926232283)
          ·
            refine ⟨8307470350668866889348425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5538313567112577926232283 8307470350668866889348425)
            ·
              refine ⟨6230602763001650167011319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8307470350668866889348425 6230602763001650167011319)
              ·
                refine ⟨9345904144502475250516979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6230602763001650167011319 9345904144502475250516979)
                ·
                  refine ⟨14018856216753712875775469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9345904144502475250516979 14018856216753712875775469)
                  ·
                    refine ⟨5257071081282642328415801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14018856216753712875775469 5257071081282642328415801)
                    ·
                      refine ⟨3942803310961981746311851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5257071081282642328415801 3942803310961981746311851)
                      ·
                        rfl

theorem cell23_7678582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_7678582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678582 prefixEnd_7678582 := by exact prefixLift 7678582
  have htrace : WordTrace (prefixWord ++ tailWord_7678582) baseStart_7678582 baseEnd_7678582 := by
    simpa [prefixWord, tailWord_7678582, baseEnd_7678582] using wordTrace_append hprefix tailTrace_7678582
  have hstable : (prefixWord ++ tailWord_7678582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678582).length < 2 ^ (prefixWord ++ tailWord_7678582).sum := by decide
  have hdescent : baseEnd_7678582 < baseStart_7678582 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678587 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 1, 7, 2]
def baseStart_7678587 : Nat := 118140960795 + 7678587 * 2 ^ 59
def prefixEnd_7678587 : Nat := 4983230072969 + 3 ^ 40 * 7678587 * 2
def baseEnd_7678587 : Nat := 3942805878365254226749327

theorem tailTrace_7678587 : CollatzResearch.WordTrace tailWord_7678587 prefixEnd_7678587 3942805878365254226749327 := by
  unfold tailWord_7678587
  simp only [CollatzResearch.WordTrace]
  refine ⟨280061075832798172098962015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186707383888532114732641343 280061075832798172098962015)
  ·
    refine ⟨420091613749197258148443023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280061075832798172098962015 420091613749197258148443023)
    ·
      refine ⟨630137420623795887222664535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420091613749197258148443023 630137420623795887222664535)
      ·
        refine ⟨945206130935693830833996803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630137420623795887222664535 945206130935693830833996803)
        ·
          refine ⟨1417809196403540746250995205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945206130935693830833996803 1417809196403540746250995205)
          ·
            refine ⟨265839224325663889922061601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1417809196403540746250995205 265839224325663889922061601)
            ·
              refine ⟨199379418244247917441546201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265839224325663889922061601 199379418244247917441546201)
              ·
                refine ⟨149534563683185938081159651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199379418244247917441546201 149534563683185938081159651)
                ·
                  refine ⟨224301845524778907121739477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149534563683185938081159651 224301845524778907121739477)
                  ·
                    refine ⟨5257074504487005635665769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 224301845524778907121739477 5257074504487005635665769)
                    ·
                      refine ⟨3942805878365254226749327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5257074504487005635665769 3942805878365254226749327)
                      ·
                        rfl

theorem cell23_7678587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 7, 2].length) (baseStart_7678587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678587 prefixEnd_7678587 := by exact prefixLift 7678587
  have htrace : WordTrace (prefixWord ++ tailWord_7678587) baseStart_7678587 baseEnd_7678587 := by
    simpa [prefixWord, tailWord_7678587, baseEnd_7678587] using wordTrace_append hprefix tailTrace_7678587
  have hstable : (prefixWord ++ tailWord_7678587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678587).length < 2 ^ (prefixWord ++ tailWord_7678587).sum := by decide
  have hdescent : baseEnd_7678587 < baseStart_7678587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678627 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 5, 4]
def baseStart_7678627 : Nat := 118140960795 + 7678627 * 2 ^ 59
def prefixEnd_7678627 : Nat := 4983230072969 + 3 ^ 40 * 7678627 * 2
def baseEnd_7678627 : Nat := 1314275472530478023416381

theorem tailTrace_7678627 : CollatzResearch.WordTrace tailWord_7678627 prefixEnd_7678627 1314275472530478023416381 := by
  unfold tailWord_7678627
  simp only [CollatzResearch.WordTrace]
  refine ⟨280062534752653258930418135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186708356501768839286945423 280062534752653258930418135)
  ·
    refine ⟨420093802128979888395627203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280062534752653258930418135 420093802128979888395627203)
    ·
      refine ⟨630140703193469832593440805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420093802128979888395627203 630140703193469832593440805)
      ·
        refine ⟨118151381848775593611270151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 630140703193469832593440805 118151381848775593611270151)
        ·
          refine ⟨177227072773163390416905227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118151381848775593611270151 177227072773163390416905227)
          ·
            refine ⟨265840609159745085625357841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177227072773163390416905227 265840609159745085625357841)
            ·
              refine ⟨199380456869808814219018381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265840609159745085625357841 199380456869808814219018381)
              ·
                refine ⟨74767671326178305332131893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199380456869808814219018381 74767671326178305332131893)
                ·
                  refine ⟨7009469186829216124887365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74767671326178305332131893 7009469186829216124887365)
                  ·
                    refine ⟨1314275472530478023416381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7009469186829216124887365 1314275472530478023416381)
                    ·
                      rfl

theorem cell23_7678627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 4].length) (baseStart_7678627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678627 prefixEnd_7678627 := by exact prefixLift 7678627
  have htrace : WordTrace (prefixWord ++ tailWord_7678627) baseStart_7678627 baseEnd_7678627 := by
    simpa [prefixWord, tailWord_7678627, baseEnd_7678627] using wordTrace_append hprefix tailTrace_7678627
  have hstable : (prefixWord ++ tailWord_7678627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678627).length < 2 ^ (prefixWord ++ tailWord_7678627).sum := by decide
  have hdescent : baseEnd_7678627 < baseStart_7678627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678717 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 3, 6]
def baseStart_7678717 : Nat := 118140960795 + 7678717 * 2 ^ 59
def prefixEnd_7678717 : Nat := 4983230072969 + 3 ^ 40 * 7678717 * 2
def baseEnd_7678717 : Nat := 1314290876950112906041243

theorem tailTrace_7678717 : CollatzResearch.WordTrace tailWord_7678717 prefixEnd_7678717 1314290876950112906041243 := by
  unfold tailWord_7678717
  simp only [CollatzResearch.WordTrace]
  refine ⟨280065817322327204301194405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186710544881551469534129603 280065817322327204301194405)
  ·
    refine ⟨52512340747936350806473951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280065817322327204301194405 52512340747936350806473951)
    ·
      refine ⟨78768511121904526209710927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52512340747936350806473951 78768511121904526209710927)
      ·
        refine ⟨118152766682856789314566391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78768511121904526209710927 118152766682856789314566391)
        ·
          refine ⟨177229150024285183971849587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118152766682856789314566391 177229150024285183971849587)
          ·
            refine ⟨265843725036427775957774381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177229150024285183971849587 265843725036427775957774381)
            ·
              refine ⟨99691396888660415984165393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265843725036427775957774381 99691396888660415984165393)
              ·
                refine ⟨74768547666495311988124045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99691396888660415984165393 74768547666495311988124045)
                ·
                  refine ⟨28038205374935741995546517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74768547666495311988124045 28038205374935741995546517)
                  ·
                    refine ⟨1314290876950112906041243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28038205374935741995546517 1314290876950112906041243)
                    ·
                      rfl

theorem cell23_7678717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_7678717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678717 prefixEnd_7678717 := by exact prefixLift 7678717
  have htrace : WordTrace (prefixWord ++ tailWord_7678717) baseStart_7678717 baseEnd_7678717 := by
    simpa [prefixWord, tailWord_7678717, baseEnd_7678717] using wordTrace_append hprefix tailTrace_7678717
  have hstable : (prefixWord ++ tailWord_7678717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678717).length < 2 ^ (prefixWord ++ tailWord_7678717).sum := by decide
  have hdescent : baseEnd_7678717 < baseStart_7678717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678724 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 5, 1, 4]
def baseStart_7678724 : Nat := 118140960795 + 7678724 * 2 ^ 59
def prefixEnd_7678724 : Nat := 4983230072969 + 3 ^ 40 * 7678724 * 2
def baseEnd_7678724 : Nat := 3942876225214920190736197

theorem tailTrace_7678724 : CollatzResearch.WordTrace tailWord_7678724 prefixEnd_7678724 3942876225214920190736197 := by
  unfold tailWord_7678724
  simp only [CollatzResearch.WordTrace]
  refine ⟨140033036316650922248349613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186710715088867896331132817 140033036316650922248349613)
  ·
    refine ⟨52512388618744095843131105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140033036316650922248349613 52512388618744095843131105)
    ·
      refine ⟨39384291464058071882348329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52512388618744095843131105 39384291464058071882348329)
      ·
        refine ⟨29538218598043553911761247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39384291464058071882348329 29538218598043553911761247)
        ·
          refine ⟨44307327897065330867641871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29538218598043553911761247 44307327897065330867641871)
          ·
            refine ⟨66460991845597996301462807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44307327897065330867641871 66460991845597996301462807)
            ·
              refine ⟨99691487768396994452194211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66460991845597996301462807 99691487768396994452194211)
              ·
                refine ⟨149537231652595491678291317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99691487768396994452194211 149537231652595491678291317)
                ·
                  refine ⟨14019115467430827344839811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149537231652595491678291317 14019115467430827344839811)
                  ·
                    refine ⟨21028673201146241017259717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14019115467430827344839811 21028673201146241017259717)
                    ·
                      refine ⟨3942876225214920190736197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21028673201146241017259717 3942876225214920190736197)
                      ·
                        rfl

theorem cell23_7678724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_7678724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678724 prefixEnd_7678724 := by exact prefixLift 7678724
  have htrace : WordTrace (prefixWord ++ tailWord_7678724) baseStart_7678724 baseEnd_7678724 := by
    simpa [prefixWord, tailWord_7678724, baseEnd_7678724] using wordTrace_append hprefix tailTrace_7678724
  have hstable : (prefixWord ++ tailWord_7678724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678724).length < 2 ^ (prefixWord ++ tailWord_7678724).sum := by decide
  have hdescent : baseEnd_7678724 < baseStart_7678724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678734 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 6, 4]
def baseStart_7678734 : Nat := 118140960795 + 7678734 * 2 ^ 59
def prefixEnd_7678734 : Nat := 4983230072969 + 3 ^ 40 * 7678734 * 2
def baseEnd_7678734 : Nat := 1314293786673821717203717

theorem tailTrace_7678734 : CollatzResearch.WordTrace tailWord_7678734 prefixEnd_7678734 1314293786673821717203717 := by
  unfold tailWord_7678734
  simp only [CollatzResearch.WordTrace]
  refine ⟨35008304670408202025570407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186710958242177077469708837 35008304670408202025570407)
  ·
    refine ⟨52512457005612303038355611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35008304670408202025570407 52512457005612303038355611)
    ·
      refine ⟨78768685508418454557533417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52512457005612303038355611 78768685508418454557533417)
      ·
        refine ⟨59076514131313840918150063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78768685508418454557533417 59076514131313840918150063)
        ·
          refine ⟨88614771196970761377225095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59076514131313840918150063 88614771196970761377225095)
          ·
            refine ⟨132922156795456142065837643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88614771196970761377225095 132922156795456142065837643)
            ·
              refine ⟨199383235193184213098756465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132922156795456142065837643 199383235193184213098756465)
              ·
                refine ⟨149537426394888159824067349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199383235193184213098756465 149537426394888159824067349)
                ·
                  refine ⟨7009566862260382491753157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 149537426394888159824067349 7009566862260382491753157)
                  ·
                    refine ⟨1314293786673821717203717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7009566862260382491753157 1314293786673821717203717)
                    ·
                      rfl

theorem cell23_7678734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_7678734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678734 prefixEnd_7678734 := by exact prefixLift 7678734
  have htrace : WordTrace (prefixWord ++ tailWord_7678734) baseStart_7678734 baseEnd_7678734 := by
    simpa [prefixWord, tailWord_7678734, baseEnd_7678734] using wordTrace_append hprefix tailTrace_7678734
  have hstable : (prefixWord ++ tailWord_7678734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678734).length < 2 ^ (prefixWord ++ tailWord_7678734).sum := by decide
  have hdescent : baseEnd_7678734 < baseStart_7678734 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678737 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 6]
def baseStart_7678737 : Nat := 118140960795 + 7678737 * 2 ^ 59
def prefixEnd_7678737 : Nat := 4983230072969 + 3 ^ 40 * 7678737 * 2
def baseEnd_7678737 : Nat := 3942882900463428639873637

theorem tailTrace_7678737 : CollatzResearch.WordTrace tailWord_7678737 prefixEnd_7678737 3942882900463428639873637 := by
  unfold tailWord_7678737
  simp only [CollatzResearch.WordTrace]
  refine ⟨280066546782254747716922465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186711031188169831811281643 280066546782254747716922465)
  ·
    refine ⟨210049910086691060787691849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280066546782254747716922465 210049910086691060787691849)
    ·
      refine ⟨157537432565018295590768887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210049910086691060787691849 157537432565018295590768887)
      ·
        refine ⟨236306148847527443386153331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157537432565018295590768887 236306148847527443386153331)
        ·
          refine ⟨354459223271291165079229997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236306148847527443386153331 354459223271291165079229997)
          ·
            refine ⟨132922208726734186904711249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354459223271291165079229997 132922208726734186904711249)
            ·
              refine ⟨99691656545050640178533437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132922208726734186904711249 99691656545050640178533437)
              ·
                refine ⟨37384371204393990066950039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99691656545050640178533437 37384371204393990066950039)
                ·
                  refine ⟨56076556806590985100425059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37384371204393990066950039 56076556806590985100425059)
                  ·
                    refine ⟨84114835209886477650637589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56076556806590985100425059 84114835209886477650637589)
                    ·
                      refine ⟨3942882900463428639873637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84114835209886477650637589 3942882900463428639873637)
                      ·
                        rfl

theorem cell23_7678737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 6].length) (baseStart_7678737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678737 prefixEnd_7678737 := by exact prefixLift 7678737
  have htrace : WordTrace (prefixWord ++ tailWord_7678737) baseStart_7678737 baseEnd_7678737 := by
    simpa [prefixWord, tailWord_7678737, baseEnd_7678737] using wordTrace_append hprefix tailTrace_7678737
  have hstable : (prefixWord ++ tailWord_7678737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678737).length < 2 ^ (prefixWord ++ tailWord_7678737).sum := by decide
  have hdescent : baseEnd_7678737 < baseStart_7678737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678785 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 1, 6]
def baseStart_7678785 : Nat := 118140960795 + 7678785 * 2 ^ 59
def prefixEnd_7678785 : Nat := 4983230072969 + 3 ^ 40 * 7678785 * 2
def baseEnd_7678785 : Nat := 1314302515844948150691139

theorem tailTrace_7678785 : CollatzResearch.WordTrace tailWord_7678785 prefixEnd_7678785 1314302515844948150691139 := by
  unfold tailWord_7678785
  simp only [CollatzResearch.WordTrace]
  refine ⟨280068297486080851914669809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186712198324053901276446539 280068297486080851914669809)
  ·
    refine ⟨210051223114560638936002357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280068297486080851914669809 210051223114560638936002357)
    ·
      refine ⟨19692302166990059900250221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 210051223114560638936002357 19692302166990059900250221)
      ·
        refine ⟨7384613312621272462593833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19692302166990059900250221 7384613312621272462593833)
        ·
          refine ⟨5538459984465954346945375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7384613312621272462593833 5538459984465954346945375)
          ·
            refine ⟨8307689976698931520418063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5538459984465954346945375 8307689976698931520418063)
            ·
              refine ⟨12461534965048397280627095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8307689976698931520418063 12461534965048397280627095)
              ·
                refine ⟨18692302447572595920940643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12461534965048397280627095 18692302447572595920940643)
                ·
                  refine ⟨28038453671358893881410965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18692302447572595920940643 28038453671358893881410965)
                  ·
                    refine ⟨1314302515844948150691139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28038453671358893881410965 1314302515844948150691139)
                    ·
                      rfl

theorem cell23_7678785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_7678785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678785 prefixEnd_7678785 := by exact prefixLift 7678785
  have htrace : WordTrace (prefixWord ++ tailWord_7678785) baseStart_7678785 baseEnd_7678785 := by
    simpa [prefixWord, tailWord_7678785, baseEnd_7678785] using wordTrace_append hprefix tailTrace_7678785
  have hstable : (prefixWord ++ tailWord_7678785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678785).length < 2 ^ (prefixWord ++ tailWord_7678785).sum := by decide
  have hdescent : baseEnd_7678785 < baseStart_7678785 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678788 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 1, 1, 6]
def baseStart_7678788 : Nat := 118140960795 + 7678788 * 2 ^ 59
def prefixEnd_7678788 : Nat := 4983230072969 + 3 ^ 40 * 7678788 * 2
def baseEnd_7678788 : Nat := 3942909087976807940335903

theorem tailTrace_7678788 : CollatzResearch.WordTrace tailWord_7678788 prefixEnd_7678788 3942909087976807940335903 := by
  unfold tailWord_7678788
  simp only [CollatzResearch.WordTrace]
  refine ⟨140034203452534991713514509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186712271270046655618019345 140034203452534991713514509)
  ·
    refine ⟨52512826294700621892567941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140034203452534991713514509 52512826294700621892567941)
    ·
      refine ⟨9846154930256366604856489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 52512826294700621892567941 9846154930256366604856489)
      ·
        refine ⟨7384616197692274953642367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9846154930256366604856489 7384616197692274953642367)
        ·
          refine ⟨11076924296538412430463551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7384616197692274953642367 11076924296538412430463551)
          ·
            refine ⟨16615386444807618645695327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11076924296538412430463551 16615386444807618645695327)
            ·
              refine ⟨24923079667211427968542991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16615386444807618645695327 24923079667211427968542991)
              ·
                refine ⟨37384619500817141952814487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24923079667211427968542991 37384619500817141952814487)
                ·
                  refine ⟨56076929251225712929221731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37384619500817141952814487 56076929251225712929221731)
                  ·
                    refine ⟨84115393876838569393832597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56076929251225712929221731 84115393876838569393832597)
                    ·
                      refine ⟨3942909087976807940335903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84115393876838569393832597 3942909087976807940335903)
                      ·
                        rfl

theorem cell23_7678788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_7678788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678788 prefixEnd_7678788 := by exact prefixLift 7678788
  have htrace : WordTrace (prefixWord ++ tailWord_7678788) baseStart_7678788 baseEnd_7678788 := by
    simpa [prefixWord, tailWord_7678788, baseEnd_7678788] using wordTrace_append hprefix tailTrace_7678788
  have hstable : (prefixWord ++ tailWord_7678788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678788).length < 2 ^ (prefixWord ++ tailWord_7678788).sum := by decide
  have hdescent : baseEnd_7678788 < baseStart_7678788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678844 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 2, 2, 4]
def baseStart_7678844 : Nat := 118140960795 + 7678844 * 2 ^ 59
def prefixEnd_7678844 : Nat := 4983230072969 + 3 ^ 40 * 7678844 * 2
def baseEnd_7678844 : Nat := 3942937842893459721235645

theorem tailTrace_7678844 : CollatzResearch.WordTrace tailWord_7678844 prefixEnd_7678844 3942937842893459721235645 := by
  unfold tailWord_7678844
  simp only [CollatzResearch.WordTrace]
  refine ⟨140035224696433552495533793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186713632928578069994045057 140035224696433552495533793)
  ·
    refine ⟨105026418522325164371650345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140035224696433552495533793 105026418522325164371650345)
    ·
      refine ⟨78769813891743873278737759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105026418522325164371650345 78769813891743873278737759)
      ·
        refine ⟨118154720837615809918106639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78769813891743873278737759 118154720837615809918106639)
        ·
          refine ⟨177232081256423714877159959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118154720837615809918106639 177232081256423714877159959)
          ·
            refine ⟨265848121884635572315739939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177232081256423714877159959 265848121884635572315739939)
            ·
              refine ⟨398772182826953358473609909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265848121884635572315739939 398772182826953358473609909)
              ·
                refine ⟨37384892140026877356900929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 398772182826953358473609909 37384892140026877356900929)
                ·
                  refine ⟨28038669105020158017675697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37384892140026877356900929 28038669105020158017675697)
                  ·
                    refine ⟨21029001828765118513256773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28038669105020158017675697 21029001828765118513256773)
                    ·
                      refine ⟨3942937842893459721235645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21029001828765118513256773 3942937842893459721235645)
                      ·
                        rfl

theorem cell23_7678844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_7678844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678844 prefixEnd_7678844 := by exact prefixLift 7678844
  have htrace : WordTrace (prefixWord ++ tailWord_7678844) baseStart_7678844 baseEnd_7678844 := by
    simpa [prefixWord, tailWord_7678844, baseEnd_7678844] using wordTrace_append hprefix tailTrace_7678844
  have hstable : (prefixWord ++ tailWord_7678844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678844).length < 2 ^ (prefixWord ++ tailWord_7678844).sum := by decide
  have hdescent : baseEnd_7678844 < baseStart_7678844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678871 : List Nat := [1, 1, 3, 3, 1, 2, 2, 5, 5]
def baseStart_7678871 : Nat := 118140960795 + 7678871 * 2 ^ 59
def prefixEnd_7678871 : Nat := 4983230072969 + 3 ^ 40 * 7678871 * 2
def baseEnd_7678871 : Nat := 438105745207903457288669

theorem tailTrace_7678871 : CollatzResearch.WordTrace tailWord_7678871 prefixEnd_7678871 438105745207903457288669 := by
  unfold tailWord_7678871
  simp only [CollatzResearch.WordTrace]
  refine ⟨280071434163769288602300467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186714289442512859068200311 280071434163769288602300467)
  ·
    refine ⟨420107151245653932903450701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280071434163769288602300467 420107151245653932903450701)
    ·
      refine ⟨157540181717120224838794013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420107151245653932903450701 157540181717120224838794013)
      ·
        refine ⟨59077568143920084314547755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157540181717120224838794013 59077568143920084314547755)
        ·
          refine ⟨88616352215880126471821633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59077568143920084314547755 88616352215880126471821633)
          ·
            refine ⟨66462264161910094853866225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88616352215880126471821633 66462264161910094853866225)
            ·
              refine ⟨49846698121432571140399669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66462264161910094853866225 49846698121432571140399669)
              ·
                refine ⟨4673127948884303544412469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49846698121432571140399669 4673127948884303544412469)
                ·
                  refine ⟨438105745207903457288669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4673127948884303544412469 438105745207903457288669)
                  ·
                    rfl

theorem cell23_7678871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 5].length) (baseStart_7678871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678871 prefixEnd_7678871 := by exact prefixLift 7678871
  have htrace : WordTrace (prefixWord ++ tailWord_7678871) baseStart_7678871 baseEnd_7678871 := by
    simpa [prefixWord, tailWord_7678871, baseEnd_7678871] using wordTrace_append hprefix tailTrace_7678871
  have hstable : (prefixWord ++ tailWord_7678871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678871).length < 2 ^ (prefixWord ++ tailWord_7678871).sum := by decide
  have hdescent : baseEnd_7678871 < baseStart_7678871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678882 : List Nat := [3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2]
def baseStart_7678882 : Nat := 118140960795 + 7678882 * 2 ^ 59
def prefixEnd_7678882 : Nat := 4983230072969 + 3 ^ 40 * 7678882 * 2
def baseEnd_7678882 : Nat := 3942957355158330572560471

theorem tailTrace_7678882 : CollatzResearch.WordTrace tailWord_7678882 prefixEnd_7678882 3942957355158330572560471 := by
  unfold tailWord_7678882
  simp only [CollatzResearch.WordTrace]
  refine ⟨70017958841682359370237725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186714556911152958320633933 70017958841682359370237725)
  ·
    refine ⟨26256734565630884763839147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70017958841682359370237725 26256734565630884763839147)
    ·
      refine ⟨39385101848446327145758721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26256734565630884763839147 39385101848446327145758721)
      ·
        refine ⟨29538826386334745359319041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39385101848446327145758721 29538826386334745359319041)
        ·
          refine ⟨22154119789751059019489281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29538826386334745359319041 22154119789751059019489281)
          ·
            refine ⟨16615589842313294264616961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22154119789751059019489281 16615589842313294264616961)
            ·
              refine ⟨12461692381734970698462721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16615589842313294264616961 12461692381734970698462721)
              ·
                refine ⟨9346269286301228023847041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12461692381734970698462721 9346269286301228023847041)
                ·
                  refine ⟨7009701964725921017885281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9346269286301228023847041 7009701964725921017885281)
                  ·
                    refine ⟨5257276473544440763413961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7009701964725921017885281 5257276473544440763413961)
                    ·
                      refine ⟨3942957355158330572560471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5257276473544440763413961 3942957355158330572560471)
                      ·
                        rfl

theorem cell23_7678882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 2, 2, 2, 2].length) (baseStart_7678882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678882 prefixEnd_7678882 := by exact prefixLift 7678882
  have htrace : WordTrace (prefixWord ++ tailWord_7678882) baseStart_7678882 baseEnd_7678882 := by
    simpa [prefixWord, tailWord_7678882, baseEnd_7678882] using wordTrace_append hprefix tailTrace_7678882
  have hstable : (prefixWord ++ tailWord_7678882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678882).length < 2 ^ (prefixWord ++ tailWord_7678882).sum := by decide
  have hdescent : baseEnd_7678882 < baseStart_7678882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678921 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 6, 4, 2]
def baseStart_7678921 : Nat := 118140960795 + 7678921 * 2 ^ 59
def prefixEnd_7678921 : Nat := 4983230072969 + 3 ^ 40 * 7678921 * 2
def baseEnd_7678921 : Nat := 3942977380903855919972791

theorem tailTrace_7678921 : CollatzResearch.WordTrace tailWord_7678921 prefixEnd_7678921 3942977380903855919972791 := by
  unfold tailWord_7678921
  simp only [CollatzResearch.WordTrace]
  refine ⟨280073257813588147141620617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186715505209058764761080411 280073257813588147141620617)
  ·
    refine ⟨210054943360191110356215463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280073257813588147141620617 210054943360191110356215463)
    ·
      refine ⟨315082415040286665534323195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210054943360191110356215463 315082415040286665534323195)
      ·
        refine ⟨472623622560429998301484793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315082415040286665534323195 472623622560429998301484793)
        ·
          refine ⟨354467716920322498726113595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472623622560429998301484793 354467716920322498726113595)
          ·
            refine ⟨531701575380483748089170393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354467716920322498726113595 531701575380483748089170393)
            ·
              refine ⟨398776181535362811066877795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531701575380483748089170393 398776181535362811066877795)
              ·
                refine ⟨598164272303044216600316693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398776181535362811066877795 598164272303044216600316693)
                ·
                  refine ⟨28038950264205197653139845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 598164272303044216600316693 28038950264205197653139845)
                  ·
                    refine ⟨5257303174538474559963721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28038950264205197653139845 5257303174538474559963721)
                    ·
                      refine ⟨3942977380903855919972791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5257303174538474559963721 3942977380903855919972791)
                      ·
                        rfl

theorem cell23_7678921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 4, 2].length) (baseStart_7678921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678921 prefixEnd_7678921 := by exact prefixLift 7678921
  have htrace : WordTrace (prefixWord ++ tailWord_7678921) baseStart_7678921 baseEnd_7678921 := by
    simpa [prefixWord, tailWord_7678921, baseEnd_7678921] using wordTrace_append hprefix tailTrace_7678921
  have hstable : (prefixWord ++ tailWord_7678921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678921).length < 2 ^ (prefixWord ++ tailWord_7678921).sum := by decide
  have hdescent : baseEnd_7678921 < baseStart_7678921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7678938 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2]
def baseStart_7678938 : Nat := 118140960795 + 7678938 * 2 ^ 59
def prefixEnd_7678938 : Nat := 4983230072969 + 3 ^ 40 * 7678938 * 2
def baseEnd_7678938 : Nat := 3942986110074982353460213

theorem tailTrace_7678938 : CollatzResearch.WordTrace tailWord_7678938 prefixEnd_7678938 3942986110074982353460213 := by
  unfold tailWord_7678938
  simp only [CollatzResearch.WordTrace]
  refine ⟨70018469463631639761247367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186715918569684372696659645 70018469463631639761247367)
  ·
    refine ⟨105027704195447459641871051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70018469463631639761247367 105027704195447459641871051)
    ·
      refine ⟨157541556293171189462806577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105027704195447459641871051 157541556293171189462806577)
      ·
        refine ⟨118156167219878392097104933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157541556293171189462806577 118156167219878392097104933)
        ·
          refine ⟨22154281353727198518207175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118156167219878392097104933 22154281353727198518207175)
          ·
            refine ⟨33231422030590797777310763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22154281353727198518207175 33231422030590797777310763)
            ·
              refine ⟨49847133045886196665966145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33231422030590797777310763 49847133045886196665966145)
              ·
                refine ⟨37385349784414647499474609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49847133045886196665966145 37385349784414647499474609)
                ·
                  refine ⟨28039012338310985624605957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37385349784414647499474609 28039012338310985624605957)
                  ·
                    refine ⟨5257314813433309804613617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28039012338310985624605957 5257314813433309804613617)
                    ·
                      refine ⟨3942986110074982353460213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5257314813433309804613617 3942986110074982353460213)
                      ·
                        rfl

theorem cell23_7678938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2].length) (baseStart_7678938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7678938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7678938 prefixEnd_7678938 := by exact prefixLift 7678938
  have htrace : WordTrace (prefixWord ++ tailWord_7678938) baseStart_7678938 baseEnd_7678938 := by
    simpa [prefixWord, tailWord_7678938, baseEnd_7678938] using wordTrace_append hprefix tailTrace_7678938
  have hstable : (prefixWord ++ tailWord_7678938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7678938).length < 2 ^ (prefixWord ++ tailWord_7678938).sum := by decide
  have hdescent : baseEnd_7678938 < baseStart_7678938 := by decide
  rcases family_descends (prefixWord ++ tailWord_7678938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679038 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_7679038 : Nat := 118140960795 + 7679038 * 2 ^ 59
def prefixEnd_7679038 : Nat := 4983230072969 + 3 ^ 40 * 7679038 * 2
def baseEnd_7679038 : Nat := 1314345819380143987403251

theorem tailTrace_7679038 : CollatzResearch.WordTrace tailWord_7679038 prefixEnd_7679038 1314345819380143987403251 := by
  unfold tailWord_7679038
  simp only [CollatzResearch.WordTrace]
  refine ⟨35009690644270534515453721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186718350102776184082419845 35009690644270534515453721)
  ·
    refine ⟨26257267983202900886590291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35009690644270534515453721 26257267983202900886590291)
    ·
      refine ⟨39385901974804351329885437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26257267983202900886590291 39385901974804351329885437)
      ·
        refine ⟨14769713240551631748707039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39385901974804351329885437 14769713240551631748707039)
        ·
          refine ⟨22154569860827447623060559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14769713240551631748707039 22154569860827447623060559)
          ·
            refine ⟨33231854791241171434590839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22154569860827447623060559 33231854791241171434590839)
            ·
              refine ⟨49847782186861757151886259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33231854791241171434590839 49847782186861757151886259)
              ·
                refine ⟨74771673280292635727829389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49847782186861757151886259 74771673280292635727829389)
                ·
                  refine ⟨28039377480109738397936021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74771673280292635727829389 28039377480109738397936021)
                  ·
                    refine ⟨1314345819380143987403251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28039377480109738397936021 1314345819380143987403251)
                    ·
                      rfl

theorem cell23_7679038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_7679038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679038 prefixEnd_7679038 := by exact prefixLift 7679038
  have htrace : WordTrace (prefixWord ++ tailWord_7679038) baseStart_7679038 baseEnd_7679038 := by
    simpa [prefixWord, tailWord_7679038, baseEnd_7679038] using wordTrace_append hprefix tailTrace_7679038
  have hstable : (prefixWord ++ tailWord_7679038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679038).length < 2 ^ (prefixWord ++ tailWord_7679038).sum := by decide
  have hdescent : baseEnd_7679038 < baseStart_7679038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679102 : List Nat := [4, 2, 4, 1, 1, 1, 10]
def baseStart_7679102 : Nat := 118140960795 + 7679102 * 2 ^ 59
def prefixEnd_7679102 : Nat := 4983230072969 + 3 ^ 40 * 7679102 * 2
def baseEnd_7679102 : Nat := 48679880504966910022339

theorem tailTrace_7679102 : CollatzResearch.WordTrace tailWord_7679102 prefixEnd_7679102 48679880504966910022339 := by
  unfold tailWord_7679102
  simp only [CollatzResearch.WordTrace]
  refine ⟨35009982428241551881744945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186719906283954943369306373 35009982428241551881744945)
  ·
    refine ⟨26257486821181163911308709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35009982428241551881744945 26257486821181163911308709)
    ·
      refine ⟨4923278778971468233370383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 26257486821181163911308709 4923278778971468233370383)
      ·
        refine ⟨7384918168457202350055575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4923278778971468233370383 7384918168457202350055575)
        ·
          refine ⟨11077377252685803525083363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7384918168457202350055575 11077377252685803525083363)
          ·
            refine ⟨16616065879028705287625045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11077377252685803525083363 16616065879028705287625045)
            ·
              refine ⟨48679880504966910022339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16616065879028705287625045 48679880504966910022339)
              ·
                rfl

theorem cell23_7679102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 10].length) (baseStart_7679102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679102 prefixEnd_7679102 := by exact prefixLift 7679102
  have htrace : WordTrace (prefixWord ++ tailWord_7679102) baseStart_7679102 baseEnd_7679102 := by
    simpa [prefixWord, tailWord_7679102, baseEnd_7679102] using wordTrace_append hprefix tailTrace_7679102
  have hstable : (prefixWord ++ tailWord_7679102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679102).length < 2 ^ (prefixWord ++ tailWord_7679102).sum := by decide
  have hdescent : baseEnd_7679102 < baseStart_7679102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679112 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 4, 1, 3]
def baseStart_7679112 : Nat := 118140960795 + 7679112 * 2 ^ 59
def prefixEnd_7679112 : Nat := 4983230072969 + 3 ^ 40 * 7679112 * 2
def baseEnd_7679112 : Nat := 3943075455708864672684413

theorem tailTrace_7679112 : CollatzResearch.WordTrace tailWord_7679112 prefixEnd_7679112 3943075455708864672684413 := by
  unfold tailWord_7679112
  simp only [CollatzResearch.WordTrace]
  refine ⟨140040112077948093380911795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186720149437264124507882393 140040112077948093380911795)
  ·
    refine ⟨210060168116922140071367693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140040112077948093380911795 210060168116922140071367693)
    ·
      refine ⟨78772563043845802526762885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210060168116922140071367693 78772563043845802526762885)
      ·
        refine ⟨14769855570721087973768041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78772563043845802526762885 14769855570721087973768041)
        ·
          refine ⟨11077391678040815980326031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14769855570721087973768041 11077391678040815980326031)
          ·
            refine ⟨16616087517061223970489047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11077391678040815980326031 16616087517061223970489047)
            ·
              refine ⟨24924131275591835955733571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16616087517061223970489047 24924131275591835955733571)
              ·
                refine ⟨37386196913387753933600357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24924131275591835955733571 37386196913387753933600357)
                ·
                  refine ⟨7009911921260203862550067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37386196913387753933600357 7009911921260203862550067)
                  ·
                    refine ⟨10514867881890305793825101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7009911921260203862550067 10514867881890305793825101)
                    ·
                      refine ⟨3943075455708864672684413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10514867881890305793825101 3943075455708864672684413)
                      ·
                        rfl

theorem cell23_7679112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_7679112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679112 prefixEnd_7679112 := by exact prefixLift 7679112
  have htrace : WordTrace (prefixWord ++ tailWord_7679112) baseStart_7679112 baseEnd_7679112 := by
    simpa [prefixWord, tailWord_7679112, baseEnd_7679112] using wordTrace_append hprefix tailTrace_7679112
  have hstable : (prefixWord ++ tailWord_7679112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679112).length < 2 ^ (prefixWord ++ tailWord_7679112).sum := by decide
  have hdescent : baseEnd_7679112 < baseStart_7679112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679128 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 2, 6]
def baseStart_7679128 : Nat := 118140960795 + 7679128 * 2 ^ 59
def prefixEnd_7679128 : Nat := 4983230072969 + 3 ^ 40 * 7679128 * 2
def baseEnd_7679128 : Nat := 1314361223799778870028113

theorem tailTrace_7679128 : CollatzResearch.WordTrace tailWord_7679128 prefixEnd_7679128 1314361223799778870028113 := by
  unfold tailWord_7679128
  simp only [CollatzResearch.WordTrace]
  refine ⟨140040403861919110747203019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186720538482558814329604025 140040403861919110747203019)
  ·
    refine ⟨210060605792878666120804529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140040403861919110747203019 210060605792878666120804529)
    ·
      refine ⟨157545454344658999590603397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210060605792878666120804529 157545454344658999590603397)
      ·
        refine ⟨29539772689623562423238137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 157545454344658999590603397 29539772689623562423238137)
        ·
          refine ⟨22154829517217671817428603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29539772689623562423238137 22154829517217671817428603)
          ·
            refine ⟨33232244275826507726142905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22154829517217671817428603 33232244275826507726142905)
            ·
              refine ⟨24924183206869880794607179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33232244275826507726142905 24924183206869880794607179)
              ·
                refine ⟨37386274810304821191910769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24924183206869880794607179 37386274810304821191910769)
                ·
                  refine ⟨28039706107728615893933077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37386274810304821191910769 28039706107728615893933077)
                  ·
                    refine ⟨1314361223799778870028113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28039706107728615893933077 1314361223799778870028113)
                    ·
                      rfl

theorem cell23_7679128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_7679128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679128 prefixEnd_7679128 := by exact prefixLift 7679128
  have htrace : WordTrace (prefixWord ++ tailWord_7679128) baseStart_7679128 baseEnd_7679128 := by
    simpa [prefixWord, tailWord_7679128, baseEnd_7679128] using wordTrace_append hprefix tailTrace_7679128
  have hstable : (prefixWord ++ tailWord_7679128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679128).length < 2 ^ (prefixWord ++ tailWord_7679128).sum := by decide
  have hdescent : baseEnd_7679128 < baseStart_7679128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679169 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_7679169 : Nat := 118140960795 + 7679169 * 2 ^ 59
def prefixEnd_7679169 : Nat := 4983230072969 + 3 ^ 40 * 7679169 * 2
def baseEnd_7679169 : Nat := 3943104724106170949671651

theorem tailTrace_7679169 : CollatzResearch.WordTrace tailWord_7679169 prefixEnd_7679169 3943104724106170949671651 := by
  unfold tailWord_7679169
  simp only [CollatzResearch.WordTrace]
  refine ⟨280082303116689685496648561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186721535411126456997765707 280082303116689685496648561)
  ·
    refine ⟨210061727337517264122486421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280082303116689685496648561 210061727337517264122486421)
    ·
      refine ⟨9846643468946121755741551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 210061727337517264122486421 9846643468946121755741551)
      ·
        refine ⟨14769965203419182633612327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9846643468946121755741551 14769965203419182633612327)
        ·
          refine ⟨22154947805128773950418491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14769965203419182633612327 22154947805128773950418491)
          ·
            refine ⟨33232421707693160925627737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22154947805128773950418491 33232421707693160925627737)
            ·
              refine ⟨24924316280769870694220803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33232421707693160925627737 24924316280769870694220803)
              ·
                refine ⟨37386474421154806041331205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24924316280769870694220803 37386474421154806041331205)
                ·
                  refine ⟨7009963953966526132749601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37386474421154806041331205 7009963953966526132749601)
                  ·
                    refine ⟨5257472965474894599562201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7009963953966526132749601 5257472965474894599562201)
                    ·
                      refine ⟨3943104724106170949671651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5257472965474894599562201 3943104724106170949671651)
                      ·
                        rfl

theorem cell23_7679169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_7679169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679169 prefixEnd_7679169 := by exact prefixLift 7679169
  have htrace : WordTrace (prefixWord ++ tailWord_7679169) baseStart_7679169 baseEnd_7679169 := by
    simpa [prefixWord, tailWord_7679169, baseEnd_7679169] using wordTrace_append hprefix tailTrace_7679169
  have hstable : (prefixWord ++ tailWord_7679169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679169).length < 2 ^ (prefixWord ++ tailWord_7679169).sum := by decide
  have hdescent : baseEnd_7679169 < baseStart_7679169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679171 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 3, 7]
def baseStart_7679171 : Nat := 118140960795 + 7679171 * 2 ^ 59
def prefixEnd_7679171 : Nat := 4983230072969 + 3 ^ 40 * 7679171 * 2
def baseEnd_7679171 : Nat := 1314368583689159980615547

theorem tailTrace_7679171 : CollatzResearch.WordTrace tailWord_7679171 prefixEnd_7679171 1314368583689159980615547 := by
  unfold tailWord_7679171
  simp only [CollatzResearch.WordTrace]
  refine ⟨280082376062682439838221367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186721584041788293225480911 280082376062682439838221367)
  ·
    refine ⟨420123564094023659757332051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280082376062682439838221367 420123564094023659757332051)
    ·
      refine ⟨630185346141035489635998077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420123564094023659757332051 630185346141035489635998077)
      ·
        refine ⟨236319504802888308613499279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 630185346141035489635998077 236319504802888308613499279)
        ·
          refine ⟨354479257204332462920248919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236319504802888308613499279 354479257204332462920248919)
          ·
            refine ⟨531718885806498694380373379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 354479257204332462920248919 531718885806498694380373379)
            ·
              refine ⟨797578328709748041570560069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 531718885806498694380373379 797578328709748041570560069)
              ·
                refine ⟨149545936633077757794480013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 797578328709748041570560069 149545936633077757794480013)
                ·
                  refine ⟨56079726237404159172930005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149545936633077757794480013 56079726237404159172930005)
                  ·
                    refine ⟨1314368583689159980615547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 56079726237404159172930005 1314368583689159980615547)
                    ·
                      rfl

theorem cell23_7679171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 7].length) (baseStart_7679171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679171 prefixEnd_7679171 := by exact prefixLift 7679171
  have htrace : WordTrace (prefixWord ++ tailWord_7679171) baseStart_7679171 baseEnd_7679171 := by
    simpa [prefixWord, tailWord_7679171, baseEnd_7679171] using wordTrace_append hprefix tailTrace_7679171
  have hstable : (prefixWord ++ tailWord_7679171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679171).length < 2 ^ (prefixWord ++ tailWord_7679171).sum := by decide
  have hdescent : baseEnd_7679171 < baseStart_7679171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679220 : List Nat := [2, 6, 1, 2, 1, 1, 2, 2, 2, 2, 2]
def baseStart_7679220 : Nat := 118140960795 + 7679220 * 2 ^ 59
def prefixEnd_7679220 : Nat := 4983230072969 + 3 ^ 40 * 7679220 * 2
def baseEnd_7679220 : Nat := 3943130911619550250133917

theorem tailTrace_7679220 : CollatzResearch.WordTrace tailWord_7679220 prefixEnd_7679220 3943130911619550250133917 := by
  unfold tailWord_7679220
  simp only [CollatzResearch.WordTrace]
  refine ⟨140042081619752460603377557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186722775493003280804503409 140042081619752460603377557)
  ·
    refine ⟨6564472575925896590783323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 140042081619752460603377557 6564472575925896590783323)
    ·
      refine ⟨9846708863888844886174985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6564472575925896590783323 9846708863888844886174985)
      ·
        refine ⟨7385031647916633664631239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9846708863888844886174985 7385031647916633664631239)
        ·
          refine ⟨11077547471874950496946859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7385031647916633664631239 11077547471874950496946859)
          ·
            refine ⟨16616321207812425745420289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11077547471874950496946859 16616321207812425745420289)
            ·
              refine ⟨12462240905859319309065217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16616321207812425745420289 12462240905859319309065217)
              ·
                refine ⟨9346680679394489481798913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12462240905859319309065217 9346680679394489481798913)
                ·
                  refine ⟨7010010509545867111349185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9346680679394489481798913 7010010509545867111349185)
                  ·
                    refine ⟨5257507882159400333511889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7010010509545867111349185 5257507882159400333511889)
                    ·
                      refine ⟨3943130911619550250133917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5257507882159400333511889 3943130911619550250133917)
                      ·
                        rfl

theorem cell23_7679220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_7679220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679220 prefixEnd_7679220 := by exact prefixLift 7679220
  have htrace : WordTrace (prefixWord ++ tailWord_7679220) baseStart_7679220 baseEnd_7679220 := by
    simpa [prefixWord, tailWord_7679220, baseEnd_7679220] using wordTrace_append hprefix tailTrace_7679220
  have hstable : (prefixWord ++ tailWord_7679220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679220).length < 2 ^ (prefixWord ++ tailWord_7679220).sum := by decide
  have hdescent : baseEnd_7679220 < baseStart_7679220 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679225 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 2, 4, 2]
def baseStart_7679225 : Nat := 118140960795 + 7679225 * 2 ^ 59
def prefixEnd_7679225 : Nat := 4983230072969 + 3 ^ 40 * 7679225 * 2
def baseEnd_7679225 : Nat := 3943133479022822730571393

theorem tailTrace_7679225 : CollatzResearch.WordTrace tailWord_7679225 prefixEnd_7679225 3943133479022822730571393 := by
  unfold tailWord_7679225
  simp only [CollatzResearch.WordTrace]
  refine ⟨280084345604486807060687129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186722897069657871373791419 280084345604486807060687129)
  ·
    refine ⟨210063259203365105295515347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280084345604486807060687129 210063259203365105295515347)
    ·
      refine ⟨315094888805047657943273021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210063259203365105295515347 315094888805047657943273021)
      ·
        refine ⟨118160583301892871728727383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315094888805047657943273021 118160583301892871728727383)
        ·
          refine ⟨177240874952839307593091075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118160583301892871728727383 177240874952839307593091075)
          ·
            refine ⟨265861312429258961389636613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177240874952839307593091075 265861312429258961389636613)
            ·
              refine ⟨49848996080486055260556865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265861312429258961389636613 49848996080486055260556865)
              ·
                refine ⟨37386747060364541445417649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49848996080486055260556865 37386747060364541445417649)
                ·
                  refine ⟨28040060295273406084063237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37386747060364541445417649 28040060295273406084063237)
                  ·
                    refine ⟨5257511305363763640761857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28040060295273406084063237 5257511305363763640761857)
                    ·
                      refine ⟨3943133479022822730571393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5257511305363763640761857 3943133479022822730571393)
                      ·
                        rfl

theorem cell23_7679225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 2, 4, 2].length) (baseStart_7679225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679225 prefixEnd_7679225 := by exact prefixLift 7679225
  have htrace : WordTrace (prefixWord ++ tailWord_7679225) baseStart_7679225 baseEnd_7679225 := by
    simpa [prefixWord, tailWord_7679225, baseEnd_7679225] using wordTrace_append hprefix tailTrace_7679225
  have hstable : (prefixWord ++ tailWord_7679225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679225).length < 2 ^ (prefixWord ++ tailWord_7679225).sum := by decide
  have hdescent : baseEnd_7679225 < baseStart_7679225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679269 : List Nat := [1, 3, 1, 2, 4, 2, 2, 3, 1, 4]
def baseStart_7679269 : Nat := 118140960795 + 7679269 * 2 ^ 59
def prefixEnd_7679269 : Nat := 4983230072969 + 3 ^ 40 * 7679269 * 2
def baseEnd_7679269 : Nat := 1314385357390540186140397

theorem tailTrace_7679269 : CollatzResearch.WordTrace tailWord_7679269 prefixEnd_7679269 1314385357390540186140397 := by
  unfold tailWord_7679269
  simp only [CollatzResearch.WordTrace]
  refine ⟨280085950416327402575288861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186723966944218268383525907 280085950416327402575288861)
  ·
    refine ⟨105032231406122775965733323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280085950416327402575288861 105032231406122775965733323)
    ·
      refine ⟨157548347109184163948599985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105032231406122775965733323 157548347109184163948599985)
      ·
        refine ⟨118161260331888122961449989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157548347109184163948599985 118161260331888122961449989)
        ·
          refine ⟨22155236312229023055271873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118161260331888122961449989 22155236312229023055271873)
          ·
            refine ⟨16616427234171767291453905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22155236312229023055271873 16616427234171767291453905)
            ·
              refine ⟨12462320425628825468590429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16616427234171767291453905 12462320425628825468590429)
              ·
                refine ⟨4673370159610809550721411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12462320425628825468590429 4673370159610809550721411)
                ·
                  refine ⟨7010055239416214326082117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4673370159610809550721411 7010055239416214326082117)
                  ·
                    refine ⟨1314385357390540186140397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7010055239416214326082117 1314385357390540186140397)
                    ·
                      rfl

theorem cell23_7679269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 1, 4].length) (baseStart_7679269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679269 prefixEnd_7679269 := by exact prefixLift 7679269
  have htrace : WordTrace (prefixWord ++ tailWord_7679269) baseStart_7679269 baseEnd_7679269 := by
    simpa [prefixWord, tailWord_7679269, baseEnd_7679269] using wordTrace_append hprefix tailTrace_7679269
  have hstable : (prefixWord ++ tailWord_7679269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679269).length < 2 ^ (prefixWord ++ tailWord_7679269).sum := by decide
  have hdescent : baseEnd_7679269 < baseStart_7679269 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679282 : List Nat := [3, 2, 1, 1, 4, 3, 1, 2, 6]
def baseStart_7679282 : Nat := 118140960795 + 7679282 * 2 ^ 59
def prefixEnd_7679282 : Nat := 4983230072969 + 3 ^ 40 * 7679282 * 2
def baseEnd_7679282 : Nat := 438129194157792111950959

theorem tailTrace_7679282 : CollatzResearch.WordTrace tailWord_7679282 prefixEnd_7679282 438129194157792111950959 := by
  unfold tailWord_7679282
  simp only [CollatzResearch.WordTrace]
  refine ⟨70021606141320076448878025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186724283043520203863674733 70021606141320076448878025)
  ·
    refine ⟨52516204605990057336658519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70021606141320076448878025 52516204605990057336658519)
    ·
      refine ⟨78774306908985086004987779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52516204605990057336658519 78774306908985086004987779)
      ·
        refine ⟨118161460363477629007481669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78774306908985086004987779 118161460363477629007481669)
        ·
          refine ⟨22155273818152055438902813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118161460363477629007481669 22155273818152055438902813)
          ·
            refine ⟨8308227681807020789588555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22155273818152055438902813 8308227681807020789588555)
            ·
              refine ⟨12462341522710531184382833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8308227681807020789588555 12462341522710531184382833)
              ·
                refine ⟨9346756142032898388287125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12462341522710531184382833 9346756142032898388287125)
                ·
                  refine ⟨438129194157792111950959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9346756142032898388287125 438129194157792111950959)
                  ·
                    rfl

theorem cell23_7679282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 6].length) (baseStart_7679282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679282 prefixEnd_7679282 := by exact prefixLift 7679282
  have htrace : WordTrace (prefixWord ++ tailWord_7679282) baseStart_7679282 baseEnd_7679282 := by
    simpa [prefixWord, tailWord_7679282, baseEnd_7679282] using wordTrace_append hprefix tailTrace_7679282
  have hstable : (prefixWord ++ tailWord_7679282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679282).length < 2 ^ (prefixWord ++ tailWord_7679282).sum := by decide
  have hdescent : baseEnd_7679282 < baseStart_7679282 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679286 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_7679286 : Nat := 118140960795 + 7679286 * 2 ^ 59
def prefixEnd_7679286 : Nat := 4983230072969 + 3 ^ 40 * 7679286 * 2
def baseEnd_7679286 : Nat := 1314388267114248997302871

theorem tailTrace_7679286 : CollatzResearch.WordTrace tailWord_7679286 prefixEnd_7679286 1314388267114248997302871 := by
  unfold tailWord_7679286
  simp only [CollatzResearch.WordTrace]
  refine ⟨17505410653579113404916107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186724380304843876319105141 17505410653579113404916107)
  ·
    refine ⟨26258115980368670107374161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17505410653579113404916107 26258115980368670107374161)
    ·
      refine ⟨19693586985276502580530621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26258115980368670107374161 19693586985276502580530621)
      ·
        refine ⟨7385095119478688467698983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19693586985276502580530621 7385095119478688467698983)
        ·
          refine ⟨11077642679218032701548475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7385095119478688467698983 11077642679218032701548475)
          ·
            refine ⟨16616464018827049052322713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11077642679218032701548475 16616464018827049052322713)
            ·
              refine ⟨12462348014120286789242035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16616464018827049052322713 12462348014120286789242035)
              ·
                refine ⟨18693522021180430183863053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12462348014120286789242035 18693522021180430183863053)
                ·
                  refine ⟨7010070757942661318948645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18693522021180430183863053 7010070757942661318948645)
                  ·
                    refine ⟨1314388267114248997302871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7010070757942661318948645 1314388267114248997302871)
                    ·
                      rfl

theorem cell23_7679286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_7679286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679286 prefixEnd_7679286 := by exact prefixLift 7679286
  have htrace : WordTrace (prefixWord ++ tailWord_7679286) baseStart_7679286 baseEnd_7679286 := by
    simpa [prefixWord, tailWord_7679286, baseEnd_7679286] using wordTrace_append hprefix tailTrace_7679286
  have hstable : (prefixWord ++ tailWord_7679286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679286).length < 2 ^ (prefixWord ++ tailWord_7679286).sum := by decide
  have hdescent : baseEnd_7679286 < baseStart_7679286 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679292 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 3, 1, 3]
def baseStart_7679292 : Nat := 118140960795 + 7679292 * 2 ^ 59
def prefixEnd_7679292 : Nat := 4983230072969 + 3 ^ 40 * 7679292 * 2
def baseEnd_7679292 : Nat := 3943167882226673968433585

theorem tailTrace_7679292 : CollatzResearch.WordTrace tailWord_7679292 prefixEnd_7679292 3943167882226673968433585 := by
  unfold tailWord_7679292
  simp only [CollatzResearch.WordTrace]
  refine ⟨140043394647622038751688065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186724526196829385002250753 140043394647622038751688065)
  ·
    refine ⟨105032545985716529063766049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140043394647622038751688065 105032545985716529063766049)
    ·
      refine ⟨78774409489287396797824537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105032545985716529063766049 78774409489287396797824537)
      ·
        refine ⟨59080807116965547598368403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78774409489287396797824537 59080807116965547598368403)
        ·
          refine ⟨88621210675448321397552605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59080807116965547598368403 88621210675448321397552605)
          ·
            refine ⟨33232954003293120524082227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88621210675448321397552605 33232954003293120524082227)
            ·
              refine ⟨49849431004939680786123341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33232954003293120524082227 49849431004939680786123341)
              ·
                refine ⟨18693536626852380294796253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49849431004939680786123341 18693536626852380294796253)
                ·
                  refine ⟨7010076235069642610548595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18693536626852380294796253 7010076235069642610548595)
                  ·
                    refine ⟨10515114352604463915822893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7010076235069642610548595 10515114352604463915822893)
                    ·
                      refine ⟨3943167882226673968433585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10515114352604463915822893 3943167882226673968433585)
                      ·
                        rfl

theorem cell23_7679292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 3, 1, 3].length) (baseStart_7679292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679292 prefixEnd_7679292 := by exact prefixLift 7679292
  have htrace : WordTrace (prefixWord ++ tailWord_7679292) baseStart_7679292 baseEnd_7679292 := by
    simpa [prefixWord, tailWord_7679292, baseEnd_7679292] using wordTrace_append hprefix tailTrace_7679292
  have hstable : (prefixWord ++ tailWord_7679292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679292).length < 2 ^ (prefixWord ++ tailWord_7679292).sum := by decide
  have hdescent : baseEnd_7679292 < baseStart_7679292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679315 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 2, 6, 2]
def baseStart_7679315 : Nat := 118140960795 + 7679315 * 2 ^ 59
def prefixEnd_7679315 : Nat := 4983230072969 + 3 ^ 40 * 7679315 * 2
def baseEnd_7679315 : Nat := 3943179692281727378445979

theorem tailTrace_7679315 : CollatzResearch.WordTrace tailWord_7679315 prefixEnd_7679315 3943179692281727378445979 := by
  unfold tailWord_7679315
  simp only [CollatzResearch.WordTrace]
  refine ⟨280087628174160752431463399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186725085449440501620975599 280087628174160752431463399)
  ·
    refine ⟨420131442261241128647195099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280087628174160752431463399 420131442261241128647195099)
    ·
      refine ⟨630197163391861692970792649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420131442261241128647195099 630197163391861692970792649)
      ·
        refine ⟨472647872543896269728094487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630197163391861692970792649 472647872543896269728094487)
        ·
          refine ⟨708971808815844404592141731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472647872543896269728094487 708971808815844404592141731)
          ·
            refine ⟨1063457713223766606888212597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 708971808815844404592141731 1063457713223766606888212597)
            ·
              refine ⟨99699160614728119395769931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1063457713223766606888212597 99699160614728119395769931)
              ·
                refine ⟨149548740922092179093654897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99699160614728119395769931 149548740922092179093654897)
                ·
                  refine ⟨112161555691569134320241173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 149548740922092179093654897 112161555691569134320241173)
                  ·
                    refine ⟨5257572923042303171261305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 112161555691569134320241173 5257572923042303171261305)
                    ·
                      refine ⟨3943179692281727378445979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5257572923042303171261305 3943179692281727378445979)
                      ·
                        rfl

theorem cell23_7679315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 6, 2].length) (baseStart_7679315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679315 prefixEnd_7679315 := by exact prefixLift 7679315
  have htrace : WordTrace (prefixWord ++ tailWord_7679315) baseStart_7679315 baseEnd_7679315 := by
    simpa [prefixWord, tailWord_7679315, baseEnd_7679315] using wordTrace_append hprefix tailTrace_7679315
  have hstable : (prefixWord ++ tailWord_7679315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679315).length < 2 ^ (prefixWord ++ tailWord_7679315).sum := by decide
  have hdescent : baseEnd_7679315 < baseStart_7679315 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679332 : List Nat := [2, 3, 1, 1, 3, 2, 2, 3, 1, 1, 4]
def baseStart_7679332 : Nat := 118140960795 + 7679332 * 2 ^ 59
def prefixEnd_7679332 : Nat := 4983230072969 + 3 ^ 40 * 7679332 * 2
def baseEnd_7679332 : Nat := 3943188421452853811933401

theorem tailTrace_7679332 : CollatzResearch.WordTrace tailWord_7679332 prefixEnd_7679332 3943188421452853811933401 := by
  unfold tailWord_7679332
  simp only [CollatzResearch.WordTrace]
  refine ⟨140044124107549582167416125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186725498810066109556554833 140044124107549582167416125)
  ·
    refine ⟨52516546540331093312781047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140044124107549582167416125 52516546540331093312781047)
    ·
      refine ⟨78774819810496639969171571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52516546540331093312781047 78774819810496639969171571)
      ·
        refine ⟨118162229715744959953757357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78774819810496639969171571 118162229715744959953757357)
        ·
          refine ⟨44310836143404359982659009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118162229715744959953757357 44310836143404359982659009)
          ·
            refine ⟨33233127107553269986994257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44310836143404359982659009 33233127107553269986994257)
            ·
              refine ⟨24924845330664952490245693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33233127107553269986994257 24924845330664952490245693)
              ·
                refine ⟨9346816998999357183842135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24924845330664952490245693 9346816998999357183842135)
                ·
                  refine ⟨14020225498499035775763203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9346816998999357183842135 14020225498499035775763203)
                  ·
                    refine ⟨21030338247748553663644805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14020225498499035775763203 21030338247748553663644805)
                    ·
                      refine ⟨3943188421452853811933401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21030338247748553663644805 3943188421452853811933401)
                      ·
                        rfl

theorem cell23_7679332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 3, 1, 1, 4].length) (baseStart_7679332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679332 prefixEnd_7679332 := by exact prefixLift 7679332
  have htrace : WordTrace (prefixWord ++ tailWord_7679332) baseStart_7679332 baseEnd_7679332 := by
    simpa [prefixWord, tailWord_7679332, baseEnd_7679332] using wordTrace_append hprefix tailTrace_7679332
  have hstable : (prefixWord ++ tailWord_7679332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679332).length < 2 ^ (prefixWord ++ tailWord_7679332).sum := by decide
  have hdescent : baseEnd_7679332 < baseStart_7679332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679400 : List Nat := [2, 1, 6, 1, 2, 1, 1, 4, 1, 2, 2]
def baseStart_7679400 : Nat := 118140960795 + 7679400 * 2 ^ 59
def prefixEnd_7679400 : Nat := 4983230072969 + 3 ^ 40 * 7679400 * 2
def baseEnd_7679400 : Nat := 3943223338137359545883089

theorem tailTrace_7679400 : CollatzResearch.WordTrace tailWord_7679400 prefixEnd_7679400 3943223338137359545883089 := by
  unfold tailWord_7679400
  simp only [CollatzResearch.WordTrace]
  refine ⟨140045364189426405974153827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186727152252568541298871769 140045364189426405974153827)
  ·
    refine ⟨210068046284139608961230741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140045364189426405974153827 210068046284139608961230741)
    ·
      refine ⟨9846939669569044170057691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 210068046284139608961230741 9846939669569044170057691)
      ·
        refine ⟨14770409504353566255086537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9846939669569044170057691 14770409504353566255086537)
        ·
          refine ⟨11077807128265174691314903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14770409504353566255086537 11077807128265174691314903)
          ·
            refine ⟨16616710692397762036972355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11077807128265174691314903 16616710692397762036972355)
            ·
              refine ⟨24925066038596643055458533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16616710692397762036972355 24925066038596643055458533)
              ·
                refine ⟨4673449882236870572898475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24925066038596643055458533 4673449882236870572898475)
                ·
                  refine ⟨7010174823355305859347713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4673449882236870572898475 7010174823355305859347713)
                  ·
                    refine ⟨5257631117516479394510785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7010174823355305859347713 5257631117516479394510785)
                    ·
                      refine ⟨3943223338137359545883089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5257631117516479394510785 3943223338137359545883089)
                      ·
                        rfl

theorem cell23_7679400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_7679400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679400 prefixEnd_7679400 := by exact prefixLift 7679400
  have htrace : WordTrace (prefixWord ++ tailWord_7679400) baseStart_7679400 baseEnd_7679400 := by
    simpa [prefixWord, tailWord_7679400, baseEnd_7679400] using wordTrace_append hprefix tailTrace_7679400
  have hstable : (prefixWord ++ tailWord_7679400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679400).length < 2 ^ (prefixWord ++ tailWord_7679400).sum := by decide
  have hdescent : baseEnd_7679400 < baseStart_7679400 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679415 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 2, 6]
def baseStart_7679415 : Nat := 118140960795 + 7679415 * 2 ^ 59
def prefixEnd_7679415 : Nat := 4983230072969 + 3 ^ 40 * 7679415 * 2
def baseEnd_7679415 : Nat := 1314410346782392329065173

theorem tailTrace_7679415 : CollatzResearch.WordTrace tailWord_7679415 prefixEnd_7679415 1314410346782392329065173 := by
  unfold tailWord_7679415
  simp only [CollatzResearch.WordTrace]
  refine ⟨280091275473798469510103699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186727516982532313006735799 280091275473798469510103699)
  ·
    refine ⟨420136913210697704265155549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280091275473798469510103699 420136913210697704265155549)
    ·
      refine ⟨157551342454011639099433331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420136913210697704265155549 157551342454011639099433331)
      ·
        refine ⟨236327013681017458649149997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157551342454011639099433331 236327013681017458649149997)
        ·
          refine ⟨88622630130381546993431249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236327013681017458649149997 88622630130381546993431249)
          ·
            refine ⟨66466972597786160245073437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88622630130381546993431249 66466972597786160245073437)
            ·
              refine ⟨24925114724169810091902539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66466972597786160245073437 24925114724169810091902539)
              ·
                refine ⟨37387672086254715137853809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24925114724169810091902539 37387672086254715137853809)
                ·
                  refine ⟨28040754064691036353390357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37387672086254715137853809 28040754064691036353390357)
                  ·
                    refine ⟨1314410346782392329065173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28040754064691036353390357 1314410346782392329065173)
                    ·
                      rfl

theorem cell23_7679415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_7679415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679415 prefixEnd_7679415 := by exact prefixLift 7679415
  have htrace : WordTrace (prefixWord ++ tailWord_7679415) baseStart_7679415 baseEnd_7679415 := by
    simpa [prefixWord, tailWord_7679415, baseEnd_7679415] using wordTrace_append hprefix tailTrace_7679415
  have hstable : (prefixWord ++ tailWord_7679415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679415).length < 2 ^ (prefixWord ++ tailWord_7679415).sum := by decide
  have hdescent : baseEnd_7679415 < baseStart_7679415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679445 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 9]
def baseStart_7679445 : Nat := 118140960795 + 7679445 * 2 ^ 59
def prefixEnd_7679445 : Nat := 4983230072969 + 3 ^ 40 * 7679445 * 2
def baseEnd_7679445 : Nat := 438138493862979096646709

theorem tailTrace_7679445 : CollatzResearch.WordTrace tailWord_7679445 prefixEnd_7679445 438138493862979096646709 := by
  unfold tailWord_7679445
  simp only [CollatzResearch.WordTrace]
  refine ⟨280092369663689784633695789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186728246442459856422463859 280092369663689784633695789)
  ·
    refine ⟨105034638623883669237635921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280092369663689784633695789 105034638623883669237635921)
    ·
      refine ⟨78775978967912751928226941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105034638623883669237635921 78775978967912751928226941)
      ·
        refine ⟨29540992112967281973085103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78775978967912751928226941 29540992112967281973085103)
        ·
          refine ⟨44311488169450922959627655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29540992112967281973085103 44311488169450922959627655)
          ·
            refine ⟨66467232254176384439441483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44311488169450922959627655 66467232254176384439441483)
            ·
              refine ⟨99700848381264576659162225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66467232254176384439441483 99700848381264576659162225)
              ·
                refine ⟨74775636285948432494371669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99700848381264576659162225 74775636285948432494371669)
                ·
                  refine ⟨438138493862979096646709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 74775636285948432494371669 438138493862979096646709)
                  ·
                    rfl

theorem cell23_7679445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 9].length) (baseStart_7679445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679445 prefixEnd_7679445 := by exact prefixLift 7679445
  have htrace : WordTrace (prefixWord ++ tailWord_7679445) baseStart_7679445 baseEnd_7679445 := by
    simpa [prefixWord, tailWord_7679445, baseEnd_7679445] using wordTrace_append hprefix tailTrace_7679445
  have hstable : (prefixWord ++ tailWord_7679445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679445).length < 2 ^ (prefixWord ++ tailWord_7679445).sum := by decide
  have hdescent : baseEnd_7679445 < baseStart_7679445 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679472 : List Nat := [2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 3]
def baseStart_7679472 : Nat := 118140960795 + 7679472 * 2 ^ 59
def prefixEnd_7679472 : Nat := 4983230072969 + 3 ^ 40 * 7679472 * 2
def baseEnd_7679472 : Nat := 3943260308744483264182757

theorem tailTrace_7679472 : CollatzResearch.WordTrace tailWord_7679472 prefixEnd_7679472 3943260308744483264182757 := by
  unfold tailWord_7679472
  simp only [CollatzResearch.WordTrace]
  refine ⟨140046677217295984122464335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186728902956394645496619113 140046677217295984122464335)
  ·
    refine ⟨210070015825943976183696503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140046677217295984122464335 210070015825943976183696503)
    ·
      refine ⟨315105023738915964275544755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210070015825943976183696503 315105023738915964275544755)
      ·
        refine ⟨472657535608373946413317133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315105023738915964275544755 472657535608373946413317133)
        ·
          refine ⟨177246575853140229904993925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472657535608373946413317133 177246575853140229904993925)
          ·
            refine ⟨33233732972463793107186361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177246575853140229904993925 33233732972463793107186361)
            ·
              refine ⟨24925299729347844830389771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33233732972463793107186361 24925299729347844830389771)
              ·
                refine ⟨37387949594021767245584657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24925299729347844830389771 37387949594021767245584657)
                ·
                  refine ⟨28040962195516325434188493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37387949594021767245584657 28040962195516325434188493)
                  ·
                    refine ⟨10515360823318622037820685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28040962195516325434188493 10515360823318622037820685)
                    ·
                      refine ⟨3943260308744483264182757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10515360823318622037820685 3943260308744483264182757)
                      ·
                        rfl

theorem cell23_7679472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 3].length) (baseStart_7679472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679472 prefixEnd_7679472 := by exact prefixLift 7679472
  have htrace : WordTrace (prefixWord ++ tailWord_7679472) baseStart_7679472 baseEnd_7679472 := by
    simpa [prefixWord, tailWord_7679472, baseEnd_7679472] using wordTrace_append hprefix tailTrace_7679472
  have hstable : (prefixWord ++ tailWord_7679472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679472).length < 2 ^ (prefixWord ++ tailWord_7679472).sum := by decide
  have hdescent : baseEnd_7679472 < baseStart_7679472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679473 : List Nat := [1, 2, 2, 2, 3, 3, 3, 1, 2, 2, 2]
def baseStart_7679473 : Nat := 118140960795 + 7679473 * 2 ^ 59
def prefixEnd_7679473 : Nat := 4983230072969 + 3 ^ 40 * 7679473 * 2
def baseEnd_7679473 : Nat := 3943260822225137760270253

theorem tailTrace_7679473 : CollatzResearch.WordTrace tailWord_7679473 prefixEnd_7679473 3943260822225137760270253 := by
  unfold tailWord_7679473
  simp only [CollatzResearch.WordTrace]
  refine ⟨280093390907588345415715073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186728927271725563610476715 280093390907588345415715073)
  ·
    refine ⟨210070043180691259061786305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280093390907588345415715073 210070043180691259061786305)
    ·
      refine ⟨157552532385518444296339729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210070043180691259061786305 157552532385518444296339729)
      ·
        refine ⟨118164399289138833222254797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157552532385518444296339729 118164399289138833222254797)
        ·
          refine ⟨44311649733427062458345549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118164399289138833222254797 44311649733427062458345549)
          ·
            refine ⟨16616868650035148421879581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44311649733427062458345549 16616868650035148421879581)
            ·
              refine ⟨6231325743763180658204843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16616868650035148421879581 6231325743763180658204843)
              ·
                refine ⟨9346988615644770987307265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6231325743763180658204843 9346988615644770987307265)
                ·
                  refine ⟨7010241461733578240480449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9346988615644770987307265 7010241461733578240480449)
                  ·
                    refine ⟨5257681096300183680360337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7010241461733578240480449 5257681096300183680360337)
                    ·
                      refine ⟨3943260822225137760270253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5257681096300183680360337 3943260822225137760270253)
                      ·
                        rfl

theorem cell23_7679473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 1, 2, 2, 2].length) (baseStart_7679473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679473 prefixEnd_7679473 := by exact prefixLift 7679473
  have htrace : WordTrace (prefixWord ++ tailWord_7679473) baseStart_7679473 baseEnd_7679473 := by
    simpa [prefixWord, tailWord_7679473, baseEnd_7679473] using wordTrace_append hprefix tailTrace_7679473
  have hstable : (prefixWord ++ tailWord_7679473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679473).length < 2 ^ (prefixWord ++ tailWord_7679473).sum := by decide
  have hdescent : baseEnd_7679473 < baseStart_7679473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679475 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 6, 5]
def baseStart_7679475 : Nat := 118140960795 + 7679475 * 2 ^ 59
def prefixEnd_7679475 : Nat := 4983230072969 + 3 ^ 40 * 7679475 * 2
def baseEnd_7679475 : Nat := 1314420616395482250815081

theorem tailTrace_7679475 : CollatzResearch.WordTrace tailWord_7679475 prefixEnd_7679475 1314420616395482250815081 := by
  unfold tailWord_7679475
  simp only [CollatzResearch.WordTrace]
  refine ⟨280093463853581099757287879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186728975902387399838191919 280093463853581099757287879)
  ·
    refine ⟨420140195780371649635931819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280093463853581099757287879 420140195780371649635931819)
    ·
      refine ⟨630210293670557474453897729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420140195780371649635931819 630210293670557474453897729)
      ·
        refine ⟨472657720252918105840423297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630210293670557474453897729 472657720252918105840423297)
        ·
          refine ⟨354493290189688579380317473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 472657720252918105840423297 354493290189688579380317473)
          ·
            refine ⟨265869967642266434535238105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354493290189688579380317473 265869967642266434535238105)
            ·
              refine ⟨199402475731699825901428579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265869967642266434535238105 199402475731699825901428579)
              ·
                refine ⟨299103713597549738852142869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199402475731699825901428579 299103713597549738852142869)
                ·
                  refine ⟨14020486574885144008694197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 299103713597549738852142869 14020486574885144008694197)
                  ·
                    refine ⟨1314420616395482250815081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14020486574885144008694197 1314420616395482250815081)
                    ·
                      rfl

theorem cell23_7679475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 5].length) (baseStart_7679475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679475 prefixEnd_7679475 := by exact prefixLift 7679475
  have htrace : WordTrace (prefixWord ++ tailWord_7679475) baseStart_7679475 baseEnd_7679475 := by
    simpa [prefixWord, tailWord_7679475, baseEnd_7679475] using wordTrace_append hprefix tailTrace_7679475
  have hstable : (prefixWord ++ tailWord_7679475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679475).length < 2 ^ (prefixWord ++ tailWord_7679475).sum := by decide
  have hdescent : baseEnd_7679475 < baseStart_7679475 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679555 : List Nat := [1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 8]
def baseStart_7679555 : Nat := 118140960795 + 7679555 * 2 ^ 59
def prefixEnd_7679555 : Nat := 4983230072969 + 3 ^ 40 * 7679555 * 2
def baseEnd_7679555 : Nat := 3943302927638806439444875

theorem tailTrace_7679555 : CollatzResearch.WordTrace tailWord_7679555 prefixEnd_7679555 3943302927638806439444875 := by
  unfold tailWord_7679555
  simp only [CollatzResearch.WordTrace]
  refine ⟨280096381693291273420200119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186730921128860848946800079 280096381693291273420200119)
  ·
    refine ⟨420144572539936910130300179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280096381693291273420200119 420144572539936910130300179)
    ·
      refine ⟨630216858809905365195450269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420144572539936910130300179 630216858809905365195450269)
      ·
        refine ⟨236331322053714511948293851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 630216858809905365195450269 236331322053714511948293851)
        ·
          refine ⟨354496983080571767922440777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236331322053714511948293851 354496983080571767922440777)
          ·
            refine ⟨265872737310428825941830583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354496983080571767922440777 265872737310428825941830583)
            ·
              refine ⟨398809105965643238912745875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265872737310428825941830583 398809105965643238912745875)
              ·
                refine ⟨598213658948464858369118813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398809105965643238912745875 598213658948464858369118813)
                ·
                  refine ⟨224330122105674321888419555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 598213658948464858369118813 224330122105674321888419555)
                  ·
                    refine ⟨336495183158511482832629333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 224330122105674321888419555 336495183158511482832629333)
                    ·
                      refine ⟨3943302927638806439444875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 336495183158511482832629333 3943302927638806439444875)
                      ·
                        rfl

theorem cell23_7679555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_7679555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679555 prefixEnd_7679555 := by exact prefixLift 7679555
  have htrace : WordTrace (prefixWord ++ tailWord_7679555) baseStart_7679555 baseEnd_7679555 := by
    simpa [prefixWord, tailWord_7679555, baseEnd_7679555] using wordTrace_append hprefix tailTrace_7679555
  have hstable : (prefixWord ++ tailWord_7679555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679555).length < 2 ^ (prefixWord ++ tailWord_7679555).sum := by decide
  have hdescent : baseEnd_7679555 < baseStart_7679555 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679572 : List Nat := [2, 4, 1, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_7679572 : Nat := 118140960795 + 7679572 * 2 ^ 59
def prefixEnd_7679572 : Nat := 4983230072969 + 3 ^ 40 * 7679572 * 2
def baseEnd_7679572 : Nat := 3943311656809932872932297

theorem tailTrace_7679572 : CollatzResearch.WordTrace tailWord_7679572 prefixEnd_7679572 3943311656809932872932297 := by
  unfold tailWord_7679572
  simp only [CollatzResearch.WordTrace]
  refine ⟨140048500867114842661784485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186731334489486456882379313 140048500867114842661784485)
  ·
    refine ⟨26259093912584032999084591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140048500867114842661784485 26259093912584032999084591)
    ·
      refine ⟨39388640868876049498626887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26259093912584032999084591 39388640868876049498626887)
      ·
        refine ⟨59082961303314074247940331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39388640868876049498626887 59082961303314074247940331)
        ·
          refine ⟨88624441954971111371910497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59082961303314074247940331 88624441954971111371910497)
          ·
            refine ⟨66468331466228333528932873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88624441954971111371910497 66468331466228333528932873)
            ·
              refine ⟨49851248599671250146699655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66468331466228333528932873 49851248599671250146699655)
              ·
                refine ⟨74776872899506875220049483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49851248599671250146699655 74776872899506875220049483)
                ·
                  refine ⟨112165309349260312830074225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74776872899506875220049483 112165309349260312830074225)
                  ·
                    refine ⟨84123982011945234622555669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 112165309349260312830074225 84123982011945234622555669)
                    ·
                      refine ⟨3943311656809932872932297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84123982011945234622555669 3943311656809932872932297)
                      ·
                        rfl

theorem cell23_7679572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_7679572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679572 prefixEnd_7679572 := by exact prefixLift 7679572
  have htrace : WordTrace (prefixWord ++ tailWord_7679572) baseStart_7679572 baseEnd_7679572 := by
    simpa [prefixWord, tailWord_7679572, baseEnd_7679572] using wordTrace_append hprefix tailTrace_7679572
  have hstable : (prefixWord ++ tailWord_7679572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679572).length < 2 ^ (prefixWord ++ tailWord_7679572).sum := by decide
  have hdescent : baseEnd_7679572 < baseStart_7679572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679613 : List Nat := [1, 4, 1, 1, 4, 1, 1, 5, 1, 1, 3]
def baseStart_7679613 : Nat := 118140960795 + 7679613 * 2 ^ 59
def prefixEnd_7679613 : Nat := 4983230072969 + 3 ^ 40 * 7679613 * 2
def baseEnd_7679613 : Nat := 3943332709516767212519609

theorem tailTrace_7679613 : CollatzResearch.WordTrace tailWord_7679613 prefixEnd_7679613 3943332709516767212519609 := by
  unfold tailWord_7679613
  simp only [CollatzResearch.WordTrace]
  refine ⟨280098497127081149325811493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186732331418054099550540995 280098497127081149325811493)
  ·
    refine ⟨52518468211327715498589655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280098497127081149325811493 52518468211327715498589655)
    ·
      refine ⟨78777702316991573247884483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52518468211327715498589655 78777702316991573247884483)
      ·
        refine ⟨118166553475487359871826725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78777702316991573247884483 118166553475487359871826725)
        ·
          refine ⟨22156228776653879975967511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118166553475487359871826725 22156228776653879975967511)
          ·
            refine ⟨33234343164980819963951267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22156228776653879975967511 33234343164980819963951267)
            ·
              refine ⟨49851514747471229945926901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33234343164980819963951267 49851514747471229945926901)
              ·
                refine ⟨4673579507575427807430647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49851514747471229945926901 4673579507575427807430647)
                ·
                  refine ⟨7010369261363141711145971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4673579507575427807430647 7010369261363141711145971)
                  ·
                    refine ⟨10515553892044712566718957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7010369261363141711145971 10515553892044712566718957)
                    ·
                      refine ⟨3943332709516767212519609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10515553892044712566718957 3943332709516767212519609)
                      ·
                        rfl

theorem cell23_7679613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 5, 1, 1, 3].length) (baseStart_7679613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679613 prefixEnd_7679613 := by exact prefixLift 7679613
  have htrace : WordTrace (prefixWord ++ tailWord_7679613) baseStart_7679613 baseEnd_7679613 := by
    simpa [prefixWord, tailWord_7679613, baseEnd_7679613] using wordTrace_append hprefix tailTrace_7679613
  have hstable : (prefixWord ++ tailWord_7679613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679613).length < 2 ^ (prefixWord ++ tailWord_7679613).sum := by decide
  have hdescent : baseEnd_7679613 < baseStart_7679613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679632 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 4]
def baseStart_7679632 : Nat := 118140960795 + 7679632 * 2 ^ 59
def prefixEnd_7679632 : Nat := 4983230072969 + 3 ^ 40 * 7679632 * 2
def baseEnd_7679632 : Nat := 3943342465649202638182021

theorem tailTrace_7679632 : CollatzResearch.WordTrace tailWord_7679632 prefixEnd_7679632 3943342465649202638182021 := by
  unfold tailWord_7679632
  simp only [CollatzResearch.WordTrace]
  refine ⟨140049595057006157785376575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186732793409341543713835433 140049595057006157785376575)
  ·
    refine ⟨210074392585509236678064863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140049595057006157785376575 210074392585509236678064863)
    ·
      refine ⟨315111588878263855017097295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210074392585509236678064863 315111588878263855017097295)
      ·
        refine ⟨472667383317395782525645943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315111588878263855017097295 472667383317395782525645943)
        ·
          refine ⟨709001074976093673788468915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472667383317395782525645943 709001074976093673788468915)
          ·
            refine ⟨1063501612464140510682703373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709001074976093673788468915 1063501612464140510682703373)
            ·
              refine ⟨398813104674052691506013765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1063501612464140510682703373 398813104674052691506013765)
              ·
                refine ⟨74777457126384879657377581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 398813104674052691506013765 74777457126384879657377581)
                ·
                  refine ⟨28041546422394329871516593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74777457126384879657377581 28041546422394329871516593)
                  ·
                    refine ⟨21031159816795747403637445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28041546422394329871516593 21031159816795747403637445)
                    ·
                      refine ⟨3943342465649202638182021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21031159816795747403637445 3943342465649202638182021)
                      ·
                        rfl

theorem cell23_7679632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_7679632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679632 prefixEnd_7679632 := by exact prefixLift 7679632
  have htrace : WordTrace (prefixWord ++ tailWord_7679632) baseStart_7679632 baseEnd_7679632 := by
    simpa [prefixWord, tailWord_7679632, baseEnd_7679632] using wordTrace_append hprefix tailTrace_7679632
  have hstable : (prefixWord ++ tailWord_7679632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679632).length < 2 ^ (prefixWord ++ tailWord_7679632).sum := by decide
  have hdescent : baseEnd_7679632 < baseStart_7679632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679639 : List Nat := [1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 5]
def baseStart_7679639 : Nat := 118140960795 + 7679639 * 2 ^ 59
def prefixEnd_7679639 : Nat := 4983230072969 + 3 ^ 40 * 7679639 * 2
def baseEnd_7679639 : Nat := 3943346060013784110794489

theorem tailTrace_7679639 : CollatzResearch.WordTrace tailWord_7679639 prefixEnd_7679639 3943346060013784110794489 := by
  unfold tailWord_7679639
  simp only [CollatzResearch.WordTrace]
  refine ⟨280099445424986955766257971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186732963616657970510838647 280099445424986955766257971)
  ·
    refine ⟨420149168137480433649386957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280099445424986955766257971 420149168137480433649386957)
    ·
      refine ⟨157555938051555162618520109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420149168137480433649386957 157555938051555162618520109)
      ·
        refine ⟨59083476769333185981945041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157555938051555162618520109 59083476769333185981945041)
        ·
          refine ⟨44312607576999889486458781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59083476769333185981945041 44312607576999889486458781)
          ·
            refine ⟨16617227841374958557422043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44312607576999889486458781 16617227841374958557422043)
            ·
              refine ⟨24925841762062437836133065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16617227841374958557422043 24925841762062437836133065)
              ·
                refine ⟨18694381321546828377099799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24925841762062437836133065 18694381321546828377099799)
                ·
                  refine ⟨28041571982320242565649699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18694381321546828377099799 28041571982320242565649699)
                  ·
                    refine ⟨42062357973480363848474549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28041571982320242565649699 42062357973480363848474549)
                    ·
                      refine ⟨3943346060013784110794489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42062357973480363848474549 3943346060013784110794489)
                      ·
                        rfl

theorem cell23_7679639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_7679639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679639 prefixEnd_7679639 := by exact prefixLift 7679639
  have htrace : WordTrace (prefixWord ++ tailWord_7679639) baseStart_7679639 baseEnd_7679639 := by
    simpa [prefixWord, tailWord_7679639, baseEnd_7679639] using wordTrace_append hprefix tailTrace_7679639
  have hstable : (prefixWord ++ tailWord_7679639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679639).length < 2 ^ (prefixWord ++ tailWord_7679639).sum := by decide
  have hdescent : baseEnd_7679639 < baseStart_7679639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679646 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_7679646 : Nat := 118140960795 + 7679646 * 2 ^ 59
def prefixEnd_7679646 : Nat := 4983230072969 + 3 ^ 40 * 7679646 * 2
def baseEnd_7679646 : Nat := 1314449884792788527802319

theorem tailTrace_7679646 : CollatzResearch.WordTrace tailWord_7679646 prefixEnd_7679646 1314449884792788527802319 := by
  unfold tailWord_7679646
  simp only [CollatzResearch.WordTrace]
  refine ⟨35012462591995199495220349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186733133823974397307841861 35012462591995199495220349)
  ·
    refine ⟨13129673471998199810707631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35012462591995199495220349 13129673471998199810707631)
    ·
      refine ⟨19694510207997299716061447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13129673471998199810707631 19694510207997299716061447)
      ·
        refine ⟨29541765311995949574092171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19694510207997299716061447 29541765311995949574092171)
        ·
          refine ⟨44312647967993924361138257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29541765311995949574092171 44312647967993924361138257)
          ·
            refine ⟨33234485975995443270853693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44312647967993924361138257 33234485975995443270853693)
            ·
              refine ⟨12462932240998291226570135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33234485975995443270853693 12462932240998291226570135)
              ·
                refine ⟨18694398361497436839855203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12462932240998291226570135 18694398361497436839855203)
                ·
                  refine ⟨28041597542246155259782805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18694398361497436839855203 28041597542246155259782805)
                  ·
                    refine ⟨1314449884792788527802319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28041597542246155259782805 1314449884792788527802319)
                    ·
                      rfl

theorem cell23_7679646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_7679646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679646 prefixEnd_7679646 := by exact prefixLift 7679646
  have htrace : WordTrace (prefixWord ++ tailWord_7679646) baseStart_7679646 baseEnd_7679646 := by
    simpa [prefixWord, tailWord_7679646, baseEnd_7679646] using wordTrace_append hprefix tailTrace_7679646
  have hstable : (prefixWord ++ tailWord_7679646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679646).length < 2 ^ (prefixWord ++ tailWord_7679646).sum := by decide
  have hdescent : baseEnd_7679646 < baseStart_7679646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679649 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 1, 1, 6]
def baseStart_7679649 : Nat := 118140960795 + 7679649 * 2 ^ 59
def prefixEnd_7679649 : Nat := 4983230072969 + 3 ^ 40 * 7679649 * 2
def baseEnd_7679649 : Nat := 3943351194820329071669443

theorem tailTrace_7679649 : CollatzResearch.WordTrace tailWord_7679649 prefixEnd_7679649 3943351194820329071669443 := by
  unfold tailWord_7679649
  simp only [CollatzResearch.WordTrace]
  refine ⟨280099810154950727474122001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186733206769967151649414667 280099810154950727474122001)
  ·
    refine ⟨210074857616213045605591501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280099810154950727474122001 210074857616213045605591501)
    ·
      refine ⟨78778071606079892102096813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210074857616213045605591501 78778071606079892102096813)
      ·
        refine ⟨29541776852279959538286305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78778071606079892102096813 29541776852279959538286305)
        ·
          refine ⟨22156332639209969653714729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29541776852279959538286305 22156332639209969653714729)
          ·
            refine ⟨16617249479407477240286047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22156332639209969653714729 16617249479407477240286047)
            ·
              refine ⟨24925874219111215860429071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16617249479407477240286047 24925874219111215860429071)
              ·
                refine ⟨37388811328666823790643607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24925874219111215860429071 37388811328666823790643607)
                ·
                  refine ⟨56083216993000235685965411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37388811328666823790643607 56083216993000235685965411)
                  ·
                    refine ⟨84124825489500353528948117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56083216993000235685965411 84124825489500353528948117)
                    ·
                      refine ⟨3943351194820329071669443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84124825489500353528948117 3943351194820329071669443)
                      ·
                        rfl

theorem cell23_7679649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_7679649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679649 prefixEnd_7679649 := by exact prefixLift 7679649
  have htrace : WordTrace (prefixWord ++ tailWord_7679649) baseStart_7679649 baseEnd_7679649 := by
    simpa [prefixWord, tailWord_7679649, baseEnd_7679649] using wordTrace_append hprefix tailTrace_7679649
  have hstable : (prefixWord ++ tailWord_7679649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679649).length < 2 ^ (prefixWord ++ tailWord_7679649).sum := by decide
  have hdescent : baseEnd_7679649 < baseStart_7679649 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679713 : List Nat := [1, 2, 3, 1, 5, 1, 1, 1, 3, 3, 2]
def baseStart_7679713 : Nat := 118140960795 + 7679713 * 2 ^ 59
def prefixEnd_7679713 : Nat := 4983230072969 + 3 ^ 40 * 7679713 * 2
def baseEnd_7679713 : Nat := 3943384057582216821269149

theorem tailTrace_7679713 : CollatzResearch.WordTrace tailWord_7679713 prefixEnd_7679713 3943384057582216821269149 := by
  unfold tailWord_7679713
  simp only [CollatzResearch.WordTrace]
  refine ⟨280102144426718866404451793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186734762951145910936301195 280102144426718866404451793)
  ·
    refine ⟨210076608320039149803338845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280102144426718866404451793 210076608320039149803338845)
    ·
      refine ⟨78778728120014681176252067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210076608320039149803338845 78778728120014681176252067)
      ·
        refine ⟨118168092180022021764378101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78778728120014681176252067 118168092180022021764378101)
        ·
          refine ⟨11078258641877064540410447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 118168092180022021764378101 11078258641877064540410447)
          ·
            refine ⟨16617387962815596810615671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11078258641877064540410447 16617387962815596810615671)
            ·
              refine ⟨24926081944223395215923507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16617387962815596810615671 24926081944223395215923507)
              ·
                refine ⟨37389122916335092823885261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24926081944223395215923507 37389122916335092823885261)
                ·
                  refine ⟨14020921093625659808956973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37389122916335092823885261 14020921093625659808956973)
                  ·
                    refine ⟨5257845410109622428358865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14020921093625659808956973 5257845410109622428358865)
                    ·
                      refine ⟨3943384057582216821269149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5257845410109622428358865 3943384057582216821269149)
                      ·
                        rfl

theorem cell23_7679713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 1, 3, 3, 2].length) (baseStart_7679713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679713 prefixEnd_7679713 := by exact prefixLift 7679713
  have htrace : WordTrace (prefixWord ++ tailWord_7679713) baseStart_7679713 baseEnd_7679713 := by
    simpa [prefixWord, tailWord_7679713, baseEnd_7679713] using wordTrace_append hprefix tailTrace_7679713
  have hstable : (prefixWord ++ tailWord_7679713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679713).length < 2 ^ (prefixWord ++ tailWord_7679713).sum := by decide
  have hdescent : baseEnd_7679713 < baseStart_7679713 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679729 : List Nat := [1, 2, 2, 2, 2, 3, 2, 1, 2, 1, 5]
def baseStart_7679729 : Nat := 118140960795 + 7679729 * 2 ^ 59
def prefixEnd_7679729 : Nat := 4983230072969 + 3 ^ 40 * 7679729 * 2
def baseEnd_7679729 : Nat := 3943392273272688758669075

theorem tailTrace_7679729 : CollatzResearch.WordTrace tailWord_7679729 prefixEnd_7679729 3943392273272688758669075 := by
  unfold tailWord_7679729
  simp only [CollatzResearch.WordTrace]
  refine ⟨280102727994660901137034241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186735151996440600758022827 280102727994660901137034241)
  ·
    refine ⟨210077045995995675852775681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280102727994660901137034241 210077045995995675852775681)
    ·
      refine ⟨157557784496996756889581761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210077045995995675852775681 157557784496996756889581761)
      ·
        refine ⟨118168338372747567667186321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157557784496996756889581761 118168338372747567667186321)
        ·
          refine ⟨88626253779560675750389741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118168338372747567667186321 88626253779560675750389741)
          ·
            refine ⟨33234845167335253406396153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88626253779560675750389741 33234845167335253406396153)
            ·
              refine ⟨24926133875501440054797115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33234845167335253406396153 24926133875501440054797115)
              ·
                refine ⟨37389200813252160082195673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24926133875501440054797115 37389200813252160082195673)
                ·
                  refine ⟨28041900609939120061646755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37389200813252160082195673 28041900609939120061646755)
                  ·
                    refine ⟨42062850914908680092470133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28041900609939120061646755 42062850914908680092470133)
                    ·
                      refine ⟨3943392273272688758669075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42062850914908680092470133 3943392273272688758669075)
                      ·
                        rfl

theorem cell23_7679729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_7679729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679729 prefixEnd_7679729 := by exact prefixLift 7679729
  have htrace : WordTrace (prefixWord ++ tailWord_7679729) baseStart_7679729 baseEnd_7679729 := by
    simpa [prefixWord, tailWord_7679729, baseEnd_7679729] using wordTrace_append hprefix tailTrace_7679729
  have hstable : (prefixWord ++ tailWord_7679729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679729).length < 2 ^ (prefixWord ++ tailWord_7679729).sum := by decide
  have hdescent : baseEnd_7679729 < baseStart_7679729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679730 : List Nat := [3, 2, 1, 3, 1, 1, 5, 1, 1, 3, 2]
def baseStart_7679730 : Nat := 118140960795 + 7679730 * 2 ^ 59
def prefixEnd_7679730 : Nat := 4983230072969 + 3 ^ 40 * 7679730 * 2
def baseEnd_7679730 : Nat := 3943392786753343254756571

theorem tailTrace_7679730 : CollatzResearch.WordTrace tailWord_7679730 prefixEnd_7679730 3943392786753343254756571 := by
  unfold tailWord_7679730
  simp only [CollatzResearch.WordTrace]
  refine ⟨70025691116914319576955161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186735176311771518871880429 70025691116914319576955161)
  ·
    refine ⟨52519268337685739682716371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70025691116914319576955161 52519268337685739682716371)
    ·
      refine ⟨78778902506528609524074557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52519268337685739682716371 78778902506528609524074557)
      ·
        refine ⟨29542088439948228571527959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78778902506528609524074557 29542088439948228571527959)
        ·
          refine ⟨44313132659922342857291939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29542088439948228571527959 44313132659922342857291939)
          ·
            refine ⟨66469698989883514285937909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44313132659922342857291939 66469698989883514285937909)
            ·
              refine ⟨6231534280301579464306679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66469698989883514285937909 6231534280301579464306679)
              ·
                refine ⟨9347301420452369196460019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6231534280301579464306679 9347301420452369196460019)
                ·
                  refine ⟨14020952130678553794690029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9347301420452369196460019 14020952130678553794690029)
                  ·
                    refine ⟨5257857049004457673008761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14020952130678553794690029 5257857049004457673008761)
                    ·
                      refine ⟨3943392786753343254756571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5257857049004457673008761 3943392786753343254756571)
                      ·
                        rfl

theorem cell23_7679730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_7679730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679730 prefixEnd_7679730 := by exact prefixLift 7679730
  have htrace : WordTrace (prefixWord ++ tailWord_7679730) baseStart_7679730 baseEnd_7679730 := by
    simpa [prefixWord, tailWord_7679730, baseEnd_7679730] using wordTrace_append hprefix tailTrace_7679730
  have hstable : (prefixWord ++ tailWord_7679730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679730).length < 2 ^ (prefixWord ++ tailWord_7679730).sum := by decide
  have hdescent : baseEnd_7679730 < baseStart_7679730 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679743 : List Nat := [1, 1, 2, 2, 1, 3, 3, 4, 2, 2, 2]
def baseStart_7679743 : Nat := 118140960795 + 7679743 * 2 ^ 59
def prefixEnd_7679743 : Nat := 4983230072969 + 3 ^ 40 * 7679743 * 2
def baseEnd_7679743 : Nat := 3943399462001851703894011

theorem tailTrace_7679743 : CollatzResearch.WordTrace tailWord_7679743 prefixEnd_7679743 3943399462001851703894011 := by
  unfold tailWord_7679743
  simp only [CollatzResearch.WordTrace]
  refine ⟨280103238616610181528043883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186735492411073454352029255 280103238616610181528043883)
  ·
    refine ⟨420154857924915272292065825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280103238616610181528043883 420154857924915272292065825)
    ·
      refine ⟨315116143443686454219049369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420154857924915272292065825 315116143443686454219049369)
      ·
        refine ⟨236337107582764840664287027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315116143443686454219049369 236337107582764840664287027)
        ·
          refine ⟨354505661374147260996430541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236337107582764840664287027 354505661374147260996430541)
          ·
            refine ⟨132939623015305222873661453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354505661374147260996430541 132939623015305222873661453)
            ·
              refine ⟨49852358630739458577623045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132939623015305222873661453 49852358630739458577623045)
              ·
                refine ⟨9347317243263648483304321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 49852358630739458577623045 9347317243263648483304321)
                ·
                  refine ⟨7010487932447736362478241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9347317243263648483304321 7010487932447736362478241)
                  ·
                    refine ⟨5257865949335802271858681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7010487932447736362478241 5257865949335802271858681)
                    ·
                      refine ⟨3943399462001851703894011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5257865949335802271858681 3943399462001851703894011)
                      ·
                        rfl

theorem cell23_7679743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 4, 2, 2, 2].length) (baseStart_7679743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679743 prefixEnd_7679743 := by exact prefixLift 7679743
  have htrace : WordTrace (prefixWord ++ tailWord_7679743) baseStart_7679743 baseEnd_7679743 := by
    simpa [prefixWord, tailWord_7679743, baseEnd_7679743] using wordTrace_append hprefix tailTrace_7679743
  have hstable : (prefixWord ++ tailWord_7679743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679743).length < 2 ^ (prefixWord ++ tailWord_7679743).sum := by decide
  have hdescent : baseEnd_7679743 < baseStart_7679743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679746 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_7679746 : Nat := 118140960795 + 7679746 * 2 ^ 59
def prefixEnd_7679746 : Nat := 4983230072969 + 3 ^ 40 * 7679746 * 2
def baseEnd_7679746 : Nat := 3943401002443815192156497

theorem tailTrace_7679746 : CollatzResearch.WordTrace tailWord_7679746 prefixEnd_7679746 3943401002443815192156497 := by
  unfold tailWord_7679746
  simp only [CollatzResearch.WordTrace]
  refine ⟨70025837008899828260100773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186735565357066208693602061 70025837008899828260100773)
  ·
    refine ⟨13129844439168717798768895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 70025837008899828260100773 13129844439168717798768895)
    ·
      refine ⟨19694766658753076698153343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13129844439168717798768895 19694766658753076698153343)
      ·
        refine ⟨29542149988129615047230015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19694766658753076698153343 29542149988129615047230015)
        ·
          refine ⟨44313224982194422570845023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29542149988129615047230015 44313224982194422570845023)
          ·
            refine ⟨66469837473291633856267535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44313224982194422570845023 66469837473291633856267535)
            ·
              refine ⟨99704756209937450784401303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66469837473291633856267535 99704756209937450784401303)
              ·
                refine ⟨149557134314906176176601955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99704756209937450784401303 149557134314906176176601955)
                ·
                  refine ⟨224335701472359264264902933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149557134314906176176601955 224335701472359264264902933)
                  ·
                    refine ⟨10515736006516840512417325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 224335701472359264264902933 10515736006516840512417325)
                    ·
                      refine ⟨3943401002443815192156497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10515736006516840512417325 3943401002443815192156497)
                      ·
                        rfl

theorem cell23_7679746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_7679746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679746 prefixEnd_7679746 := by exact prefixLift 7679746
  have htrace : WordTrace (prefixWord ++ tailWord_7679746) baseStart_7679746 baseEnd_7679746 := by
    simpa [prefixWord, tailWord_7679746, baseEnd_7679746] using wordTrace_append hprefix tailTrace_7679746
  have hstable : (prefixWord ++ tailWord_7679746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679746).length < 2 ^ (prefixWord ++ tailWord_7679746).sum := by decide
  have hdescent : baseEnd_7679746 < baseStart_7679746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679839 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 8]
def baseStart_7679839 : Nat := 118140960795 + 7679839 * 2 ^ 59
def prefixEnd_7679839 : Nat := 4983230072969 + 3 ^ 40 * 7679839 * 2
def baseEnd_7679839 : Nat := 438160972904964814254841

theorem tailTrace_7679839 : CollatzResearch.WordTrace tailWord_7679839 prefixEnd_7679839 438160972904964814254841 := by
  unfold tailWord_7679839
  simp only [CollatzResearch.WordTrace]
  refine ⟨280106740024262389923538571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186737826682841593282359047 280106740024262389923538571)
  ·
    refine ⟨420160110036393584885307857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280106740024262389923538571 420160110036393584885307857)
    ·
      refine ⟨315120082527295188663980893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420160110036393584885307857 315120082527295188663980893)
      ·
        refine ⟨118170030947735695748992835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315120082527295188663980893 118170030947735695748992835)
        ·
          refine ⟨177255046421603543623489253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118170030947735695748992835 177255046421603543623489253)
          ·
            refine ⟨33235321204050664429404235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 177255046421603543623489253 33235321204050664429404235)
            ·
              refine ⟨49852981806075996644106353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33235321204050664429404235 49852981806075996644106353)
              ·
                refine ⟨37389736354556997483079765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49852981806075996644106353 37389736354556997483079765)
                ·
                  refine ⟨438160972904964814254841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37389736354556997483079765 438160972904964814254841)
                  ·
                    rfl

theorem cell23_7679839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 8].length) (baseStart_7679839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679839 prefixEnd_7679839 := by exact prefixLift 7679839
  have htrace : WordTrace (prefixWord ++ tailWord_7679839) baseStart_7679839 baseEnd_7679839 := by
    simpa [prefixWord, tailWord_7679839, baseEnd_7679839] using wordTrace_append hprefix tailTrace_7679839
  have hstable : (prefixWord ++ tailWord_7679839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679839).length < 2 ^ (prefixWord ++ tailWord_7679839).sum := by decide
  have hdescent : baseEnd_7679839 < baseStart_7679839 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679850 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_7679850 : Nat := 118140960795 + 7679850 * 2 ^ 59
def prefixEnd_7679850 : Nat := 4983230072969 + 3 ^ 40 * 7679850 * 2
def baseEnd_7679850 : Nat := 3943454404431882785256019

theorem tailTrace_7679850 : CollatzResearch.WordTrace tailWord_7679850 prefixEnd_7679850 3943454404431882785256019 := by
  unfold tailWord_7679850
  simp only [CollatzResearch.WordTrace]
  refine ⟨70026785306805634700547251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186738094151481692534792669 70026785306805634700547251)
  ·
    refine ⟨105040177960208452050820877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70026785306805634700547251 105040177960208452050820877)
    ·
      refine ⟨39390066735078169519057829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105040177960208452050820877 39390066735078169519057829)
      ·
        refine ⟨7385637512827156784823343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39390066735078169519057829 7385637512827156784823343)
        ·
          refine ⟨11078456269240735177235015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7385637512827156784823343 11078456269240735177235015)
          ·
            refine ⟨16617684403861102765852523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11078456269240735177235015 16617684403861102765852523)
            ·
              refine ⟨24926526605791654148778785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16617684403861102765852523 24926526605791654148778785)
              ·
                refine ⟨18694894954343740611584089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24926526605791654148778785 18694894954343740611584089)
                ·
                  refine ⟨14021171215757805458688067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18694894954343740611584089 14021171215757805458688067)
                  ·
                    refine ⟨21031756823636708188032101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14021171215757805458688067 21031756823636708188032101)
                    ·
                      refine ⟨3943454404431882785256019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21031756823636708188032101 3943454404431882785256019)
                      ·
                        rfl

theorem cell23_7679850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_7679850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679850 prefixEnd_7679850 := by exact prefixLift 7679850
  have htrace : WordTrace (prefixWord ++ tailWord_7679850) baseStart_7679850 baseEnd_7679850 := by
    simpa [prefixWord, tailWord_7679850, baseEnd_7679850] using wordTrace_append hprefix tailTrace_7679850
  have hstable : (prefixWord ++ tailWord_7679850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679850).length < 2 ^ (prefixWord ++ tailWord_7679850).sum := by decide
  have hdescent : baseEnd_7679850 < baseStart_7679850 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679869 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 2, 9]
def baseStart_7679869 : Nat := 118140960795 + 7679869 * 2 ^ 59
def prefixEnd_7679869 : Nat := 4983230072969 + 3 ^ 40 * 7679869 * 2
def baseEnd_7679869 : Nat := 1314488053521439403639477

theorem tailTrace_7679869 : CollatzResearch.WordTrace tailWord_7679869 prefixEnd_7679869 1314488053521439403639477 := by
  unfold tailWord_7679869
  simp only [CollatzResearch.WordTrace]
  refine ⟨280107834214153705047130661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186738556142769136698087107 280107834214153705047130661)
  ·
    refine ⟨52520218915153819696336999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280107834214153705047130661 52520218915153819696336999)
    ·
      refine ⟨78780328372730729544505499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52520218915153819696336999 78780328372730729544505499)
      ·
        refine ⟨118170492559096094316758249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78780328372730729544505499 118170492559096094316758249)
        ·
          refine ⟨88627869419322070737568687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118170492559096094316758249 88627869419322070737568687)
          ·
            refine ⟨132941804128983106106353031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88627869419322070737568687 132941804128983106106353031)
            ·
              refine ⟨199412706193474659159529547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132941804128983106106353031 199412706193474659159529547)
              ·
                refine ⟨299119059290211988739294321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199412706193474659159529547 299119059290211988739294321)
                ·
                  refine ⟨224339294467658991554470741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 299119059290211988739294321 224339294467658991554470741)
                  ·
                    refine ⟨1314488053521439403639477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 224339294467658991554470741 1314488053521439403639477)
                    ·
                      rfl

theorem cell23_7679869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_7679869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679869 prefixEnd_7679869 := by exact prefixLift 7679869
  have htrace : WordTrace (prefixWord ++ tailWord_7679869) baseStart_7679869 baseEnd_7679869 := by
    simpa [prefixWord, tailWord_7679869, baseEnd_7679869] using wordTrace_append hprefix tailTrace_7679869
  have hstable : (prefixWord ++ tailWord_7679869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679869).length < 2 ^ (prefixWord ++ tailWord_7679869).sum := by decide
  have hdescent : baseEnd_7679869 < baseStart_7679869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679933 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 1, 6]
def baseStart_7679933 : Nat := 118140960795 + 7679933 * 2 ^ 59
def prefixEnd_7679933 : Nat := 4983230072969 + 3 ^ 40 * 7679933 * 2
def baseEnd_7679933 : Nat := 1314499007775401986839379

theorem tailTrace_7679933 : CollatzResearch.WordTrace tailWord_7679933 prefixEnd_7679933 1314499007775401986839379 := by
  unfold tailWord_7679933
  simp only [CollatzResearch.WordTrace]
  refine ⟨280110168485921843977460453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186740112323947895984973635 280110168485921843977460453)
  ·
    refine ⟨52520656591110345745773835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280110168485921843977460453 52520656591110345745773835)
    ·
      refine ⟨78780984886665518618660753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52520656591110345745773835 78780984886665518618660753)
      ·
        refine ⟨59085738664999138963995565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78780984886665518618660753 59085738664999138963995565)
        ·
          refine ⟨22157151999374677111498337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 59085738664999138963995565 22157151999374677111498337)
          ·
            refine ⟨16617863999531007833623753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22157151999374677111498337 16617863999531007833623753)
            ·
              refine ⟨12463397999648255875217815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16617863999531007833623753 12463397999648255875217815)
              ·
                refine ⟨18695096999472383812826723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12463397999648255875217815 18695096999472383812826723)
                ·
                  refine ⟨28042645499208575719240085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18695096999472383812826723 28042645499208575719240085)
                  ·
                    refine ⟨1314499007775401986839379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28042645499208575719240085 1314499007775401986839379)
                    ·
                      rfl

theorem cell23_7679933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 6].length) (baseStart_7679933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679933 prefixEnd_7679933 := by exact prefixLift 7679933
  have htrace : WordTrace (prefixWord ++ tailWord_7679933) baseStart_7679933 baseEnd_7679933 := by
    simpa [prefixWord, tailWord_7679933, baseEnd_7679933] using wordTrace_append hprefix tailTrace_7679933
  have hstable : (prefixWord ++ tailWord_7679933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679933).length < 2 ^ (prefixWord ++ tailWord_7679933).sum := by decide
  have hdescent : baseEnd_7679933 < baseStart_7679933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679943 : List Nat := [1, 1, 4, 1, 1, 2, 1, 6, 1, 2, 3]
def baseStart_7679943 : Nat := 118140960795 + 7679943 * 2 ^ 59
def prefixEnd_7679943 : Nat := 4983230072969 + 3 ^ 40 * 7679943 * 2
def baseEnd_7679943 : Nat := 3943502158132750921393091

theorem tailTrace_7679943 : CollatzResearch.WordTrace tailWord_7679943 prefixEnd_7679943 3943502158132750921393091 := by
  unfold tailWord_7679943
  simp only [CollatzResearch.WordTrace]
  refine ⟨280110533215885615685324483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186740355477257077123549655 280110533215885615685324483)
  ·
    refine ⟨420165799823828423527986725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280110533215885615685324483 420165799823828423527986725)
    ·
      refine ⟨78781087466967829411497511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 420165799823828423527986725 78781087466967829411497511)
      ·
        refine ⟨118171631200451744117246267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78781087466967829411497511 118171631200451744117246267)
        ·
          refine ⟨177257446800677616175869401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118171631200451744117246267 177257446800677616175869401)
          ·
            refine ⟨132943085100508212131902051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177257446800677616175869401 132943085100508212131902051)
            ·
              refine ⟨199414627650762318197853077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132943085100508212131902051 199414627650762318197853077)
              ·
                refine ⟨9347560671129483665524363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 199414627650762318197853077 9347560671129483665524363)
                ·
                  refine ⟨14021341006694225498286545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9347560671129483665524363 14021341006694225498286545)
                  ·
                    refine ⟨10516005755020669123714909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14021341006694225498286545 10516005755020669123714909)
                    ·
                      refine ⟨3943502158132750921393091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10516005755020669123714909 3943502158132750921393091)
                      ·
                        rfl

theorem cell23_7679943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 6, 1, 2, 3].length) (baseStart_7679943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679943 prefixEnd_7679943 := by exact prefixLift 7679943
  have htrace : WordTrace (prefixWord ++ tailWord_7679943) baseStart_7679943 baseEnd_7679943 := by
    simpa [prefixWord, tailWord_7679943, baseEnd_7679943] using wordTrace_append hprefix tailTrace_7679943
  have hstable : (prefixWord ++ tailWord_7679943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679943).length < 2 ^ (prefixWord ++ tailWord_7679943).sum := by decide
  have hdescent : baseEnd_7679943 < baseStart_7679943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679954 : List Nat := [3, 2, 2, 3, 3, 1, 2, 1, 1, 5]
def baseStart_7679954 : Nat := 118140960795 + 7679954 * 2 ^ 59
def prefixEnd_7679954 : Nat := 4983230072969 + 3 ^ 40 * 7679954 * 2
def baseEnd_7679954 : Nat := 1314502602139983459451847

theorem tailTrace_7679954 : CollatzResearch.WordTrace tailWord_7679954 prefixEnd_7679954 1314502602139983459451847 := by
  unfold tailWord_7679954
  simp only [CollatzResearch.WordTrace]
  refine ⟨70027733604711441140993729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186740622945897176375983277 70027733604711441140993729)
  ·
    refine ⟨52520800203533580855745297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70027733604711441140993729 52520800203533580855745297)
    ·
      refine ⟨39390600152650185641808973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52520800203533580855745297 39390600152650185641808973)
      ·
        refine ⟨14771475057243819615678365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39390600152650185641808973 14771475057243819615678365)
        ·
          refine ⟨5539303146466432355879387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14771475057243819615678365 5539303146466432355879387)
          ·
            refine ⟨8308954719699648533819081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5539303146466432355879387 8308954719699648533819081)
            ·
              refine ⟨6231716039774736400364311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8308954719699648533819081 6231716039774736400364311)
              ·
                refine ⟨9347574059662104600546467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6231716039774736400364311 9347574059662104600546467)
                ·
                  refine ⟨14021361089493156900819701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9347574059662104600546467 14021361089493156900819701)
                  ·
                    refine ⟨1314502602139983459451847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14021361089493156900819701 1314502602139983459451847)
                    ·
                      rfl

theorem cell23_7679954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_7679954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679954 prefixEnd_7679954 := by exact prefixLift 7679954
  have htrace : WordTrace (prefixWord ++ tailWord_7679954) baseStart_7679954 baseEnd_7679954 := by
    simpa [prefixWord, tailWord_7679954, baseEnd_7679954] using wordTrace_append hprefix tailTrace_7679954
  have hstable : (prefixWord ++ tailWord_7679954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679954).length < 2 ^ (prefixWord ++ tailWord_7679954).sum := by decide
  have hdescent : baseEnd_7679954 < baseStart_7679954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7679957 : List Nat := [1, 3, 2, 3, 2, 3, 2, 1, 1, 1, 4]
def baseStart_7679957 : Nat := 118140960795 + 7679957 * 2 ^ 59
def prefixEnd_7679957 : Nat := 4983230072969 + 3 ^ 40 * 7679957 * 2
def baseEnd_7679957 : Nat := 3943509346861913866618027

theorem tailTrace_7679957 : CollatzResearch.WordTrace tailWord_7679957 prefixEnd_7679957 3943509346861913866618027 := by
  unfold tailWord_7679957
  simp only [CollatzResearch.WordTrace]
  refine ⟨280111043837834896076334125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186740695891889930717556083 280111043837834896076334125)
  ·
    refine ⟨105041641439188086028625297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280111043837834896076334125 105041641439188086028625297)
    ·
      refine ⟨78781231079391064521468973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105041641439188086028625297 78781231079391064521468973)
      ·
        refine ⟨29542961654771649195550865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78781231079391064521468973 29542961654771649195550865)
        ·
          refine ⟨22157221241078736896663149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29542961654771649195550865 22157221241078736896663149)
          ·
            refine ⟨8308957965404526336248681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22157221241078736896663149 8308957965404526336248681)
            ·
              refine ⟨6231718474053394752186511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8308957965404526336248681 6231718474053394752186511)
              ·
                refine ⟨9347577711080092128279767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6231718474053394752186511 9347577711080092128279767)
                ·
                  refine ⟨14021366566620138192419651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9347577711080092128279767 14021366566620138192419651)
                  ·
                    refine ⟨21032049849930207288629477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14021366566620138192419651 21032049849930207288629477)
                    ·
                      refine ⟨3943509346861913866618027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21032049849930207288629477 3943509346861913866618027)
                      ·
                        rfl

theorem cell23_7679957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 3, 2, 1, 1, 1, 4].length) (baseStart_7679957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7679957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7679957 prefixEnd_7679957 := by exact prefixLift 7679957
  have htrace : WordTrace (prefixWord ++ tailWord_7679957) baseStart_7679957 baseEnd_7679957 := by
    simpa [prefixWord, tailWord_7679957, baseEnd_7679957] using wordTrace_append hprefix tailTrace_7679957
  have hstable : (prefixWord ++ tailWord_7679957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7679957).length < 2 ^ (prefixWord ++ tailWord_7679957).sum := by decide
  have hdescent : baseEnd_7679957 < baseStart_7679957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7679957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680016 : List Nat := [2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 5]
def baseStart_7680016 : Nat := 118140960795 + 7680016 * 2 ^ 59
def prefixEnd_7680016 : Nat := 4983230072969 + 3 ^ 40 * 7680016 * 2
def baseEnd_7680016 : Nat := 3943539642220529135780255

theorem tailTrace_7680016 : CollatzResearch.WordTrace tailWord_7680016 prefixEnd_7680016 3943539642220529135780255 := by
  unfold tailWord_7680016
  simp only [CollatzResearch.WordTrace]
  refine ⟨140056597872310574576365951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186742130496414099435154601 140056597872310574576365951)
  ·
    refine ⟨210084896808465861864548927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140056597872310574576365951 210084896808465861864548927)
    ·
      refine ⟨315127345212698792796823391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210084896808465861864548927 315127345212698792796823391)
      ·
        refine ⟨472691017819048189195235087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315127345212698792796823391 472691017819048189195235087)
        ·
          refine ⟨709036526728572283792852631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472691017819048189195235087 709036526728572283792852631)
          ·
            refine ⟨1063554790092858425689278947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709036526728572283792852631 1063554790092858425689278947)
            ·
              refine ⟨1595332185139287638533918421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1063554790092858425689278947 1595332185139287638533918421)
              ·
                refine ⟨37390598089202054028138713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1595332185139287638533918421 37390598089202054028138713)
                ·
                  refine ⟨28042948566901540521104035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37390598089202054028138713 28042948566901540521104035)
                  ·
                    refine ⟨42064422850352310781656053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28042948566901540521104035 42064422850352310781656053)
                    ·
                      refine ⟨3943539642220529135780255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42064422850352310781656053 3943539642220529135780255)
                      ·
                        rfl

theorem cell23_7680016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_7680016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680016 prefixEnd_7680016 := by exact prefixLift 7680016
  have htrace : WordTrace (prefixWord ++ tailWord_7680016) baseStart_7680016 baseEnd_7680016 := by
    simpa [prefixWord, tailWord_7680016, baseEnd_7680016] using wordTrace_append hprefix tailTrace_7680016
  have hstable : (prefixWord ++ tailWord_7680016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680016).length < 2 ^ (prefixWord ++ tailWord_7680016).sum := by decide
  have hdescent : baseEnd_7680016 < baseStart_7680016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680094 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_7680094 : Nat := 118140960795 + 7680094 * 2 ^ 59
def prefixEnd_7680094 : Nat := 4983230072969 + 3 ^ 40 * 7680094 * 2
def baseEnd_7680094 : Nat := 3943579693711579830604897

theorem tailTrace_7680094 : CollatzResearch.WordTrace tailWord_7680094 prefixEnd_7680094 3943579693711579830604897 := by
  unfold tailWord_7680094
  simp only [CollatzResearch.WordTrace]
  refine ⟨35014505079792321059258917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186744027092225712316047557 35014505079792321059258917)
  ·
    refine ⟨6565219702461060198611047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35014505079792321059258917 6565219702461060198611047)
    ·
      refine ⟨9847829553691590297916571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6565219702461060198611047 9847829553691590297916571)
      ·
        refine ⟨14771744330537385446874857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9847829553691590297916571 14771744330537385446874857)
        ·
          refine ⟨11078808247903039085156143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14771744330537385446874857 11078808247903039085156143)
          ·
            refine ⟨16618212371854558627734215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11078808247903039085156143 16618212371854558627734215)
            ·
              refine ⟨24927318557781837941601323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16618212371854558627734215 24927318557781837941601323)
              ·
                refine ⟨37390977836672756912401985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24927318557781837941601323 37390977836672756912401985)
                ·
                  refine ⟨28043233377504567684301489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37390977836672756912401985 28043233377504567684301489)
                  ·
                    refine ⟨21032425033128425763226117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28043233377504567684301489 21032425033128425763226117)
                    ·
                      refine ⟨3943579693711579830604897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21032425033128425763226117 3943579693711579830604897)
                      ·
                        rfl

theorem cell23_7680094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_7680094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680094 prefixEnd_7680094 := by exact prefixLift 7680094
  have htrace : WordTrace (prefixWord ++ tailWord_7680094) baseStart_7680094 baseEnd_7680094 := by
    simpa [prefixWord, tailWord_7680094, baseEnd_7680094] using wordTrace_append hprefix tailTrace_7680094
  have hstable : (prefixWord ++ tailWord_7680094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680094).length < 2 ^ (prefixWord ++ tailWord_7680094).sum := by decide
  have hdescent : baseEnd_7680094 < baseStart_7680094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680103 : List Nat := [1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 4]
def baseStart_7680103 : Nat := 118140960795 + 7680103 * 2 ^ 59
def prefixEnd_7680103 : Nat := 4983230072969 + 3 ^ 40 * 7680103 * 2
def baseEnd_7680103 : Nat := 3943584315037470295392355

theorem tailTrace_7680103 : CollatzResearch.WordTrace tailWord_7680103 prefixEnd_7680103 3943584315037470295392355 := by
  unfold tailWord_7680103
  simp only [CollatzResearch.WordTrace]
  refine ⟨280116368895305963011148963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186744245930203975340765975 280116368895305963011148963)
  ·
    refine ⟨420174553342958944516723445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280116368895305963011148963 420174553342958944516723445)
    ·
      refine ⟨39391364375902401048442823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 420174553342958944516723445 39391364375902401048442823)
      ·
        refine ⟨59087046563853601572664235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39391364375902401048442823 59087046563853601572664235)
        ·
          refine ⟨88630569845780402358996353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59087046563853601572664235 88630569845780402358996353)
          ·
            refine ⟨66472927384335301769247265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88630569845780402358996353 66472927384335301769247265)
            ·
              refine ⟨49854695538251476326935449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66472927384335301769247265 49854695538251476326935449)
              ·
                refine ⟨37391021653688607245201587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49854695538251476326935449 37391021653688607245201587)
                ·
                  refine ⟨56086532480532910867802381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37391021653688607245201587 56086532480532910867802381)
                  ·
                    refine ⟨21032449680199841575425893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 56086532480532910867802381 21032449680199841575425893)
                    ·
                      refine ⟨3943584315037470295392355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21032449680199841575425893 3943584315037470295392355)
                      ·
                        rfl

theorem cell23_7680103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_7680103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680103 prefixEnd_7680103 := by exact prefixLift 7680103
  have htrace : WordTrace (prefixWord ++ tailWord_7680103) baseStart_7680103 baseEnd_7680103 := by
    simpa [prefixWord, tailWord_7680103, baseEnd_7680103] using wordTrace_append hprefix tailTrace_7680103
  have hstable : (prefixWord ++ tailWord_7680103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680103).length < 2 ^ (prefixWord ++ tailWord_7680103).sum := by decide
  have hdescent : baseEnd_7680103 < baseStart_7680103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680133 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 2, 1, 6]
def baseStart_7680133 : Nat := 118140960795 + 7680133 * 2 ^ 59
def prefixEnd_7680133 : Nat := 4983230072969 + 3 ^ 40 * 7680133 * 2
def baseEnd_7680133 : Nat := 3943599719457105178017217

theorem tailTrace_7680133 : CollatzResearch.WordTrace tailWord_7680133 prefixEnd_7680133 3943599719457105178017217 := by
  unfold tailWord_7680133
  simp only [CollatzResearch.WordTrace]
  refine ⟨280117463085197278134741053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186744975390131518756494035 280117463085197278134741053)
  ·
    refine ⟨105044048656948979300527895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280117463085197278134741053 105044048656948979300527895)
    ·
      refine ⟨157566072985423468950791843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105044048656948979300527895 157566072985423468950791843)
      ·
        refine ⟨236349109478135203426187765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157566072985423468950791843 236349109478135203426187765)
        ·
          refine ⟨22157729013575175321205103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 236349109478135203426187765 22157729013575175321205103)
          ·
            refine ⟨33236593520362762981807655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22157729013575175321205103 33236593520362762981807655)
            ·
              refine ⟨49854890280544144472711483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33236593520362762981807655 49854890280544144472711483)
              ·
                refine ⟨74782335420816216709067225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49854890280544144472711483 74782335420816216709067225)
                ·
                  refine ⟨56086751565612162531800419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74782335420816216709067225 56086751565612162531800419)
                  ·
                    refine ⟨84130127348418243797700629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 56086751565612162531800419 84130127348418243797700629)
                    ·
                      refine ⟨3943599719457105178017217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84130127348418243797700629 3943599719457105178017217)
                      ·
                        rfl

theorem cell23_7680133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_7680133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680133 prefixEnd_7680133 := by exact prefixLift 7680133
  have htrace : WordTrace (prefixWord ++ tailWord_7680133) baseStart_7680133 baseEnd_7680133 := by
    simpa [prefixWord, tailWord_7680133, baseEnd_7680133] using wordTrace_append hprefix tailTrace_7680133
  have hstable : (prefixWord ++ tailWord_7680133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680133).length < 2 ^ (prefixWord ++ tailWord_7680133).sum := by decide
  have hdescent : baseEnd_7680133 < baseStart_7680133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680237 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_7680237 : Nat := 118140960795 + 7680237 * 2 ^ 59
def prefixEnd_7680237 : Nat := 4983230072969 + 3 ^ 40 * 7680237 * 2
def baseEnd_7680237 : Nat := 1314551040481724257038913

theorem tailTrace_7680237 : CollatzResearch.WordTrace tailWord_7680237 prefixEnd_7680237 1314551040481724257038913 := by
  unfold tailWord_7680237
  simp only [CollatzResearch.WordTrace]
  refine ⟨280121256276820503896526965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186747504184547002597684643 280121256276820503896526965)
  ·
    refine ⟨26261367775951922240299403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280121256276820503896526965 26261367775951922240299403)
    ·
      refine ⟨39392051663927883360449105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26261367775951922240299403 39392051663927883360449105)
      ·
        refine ⟨29544038747945912520336829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39392051663927883360449105 29544038747945912520336829)
        ·
          refine ⟨11079014530479717195126311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29544038747945912520336829 11079014530479717195126311)
          ·
            refine ⟨16618521795719575792689467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11079014530479717195126311 16618521795719575792689467)
            ·
              refine ⟨24927782693579363689034201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16618521795719575792689467 24927782693579363689034201)
              ·
                refine ⟨18695837020184522766775651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24927782693579363689034201 18695837020184522766775651)
                ·
                  refine ⟨28043755530276784150163477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18695837020184522766775651 28043755530276784150163477)
                  ·
                    refine ⟨1314551040481724257038913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28043755530276784150163477 1314551040481724257038913)
                    ·
                      rfl

theorem cell23_7680237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_7680237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680237 prefixEnd_7680237 := by exact prefixLift 7680237
  have htrace : WordTrace (prefixWord ++ tailWord_7680237) baseStart_7680237 baseEnd_7680237 := by
    simpa [prefixWord, tailWord_7680237, baseEnd_7680237] using wordTrace_append hprefix tailTrace_7680237
  have hstable : (prefixWord ++ tailWord_7680237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680237).length < 2 ^ (prefixWord ++ tailWord_7680237).sum := by decide
  have hdescent : baseEnd_7680237 < baseStart_7680237 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680254 : List Nat := [4, 2, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_7680254 : Nat := 118140960795 + 7680254 * 2 ^ 59
def prefixEnd_7680254 : Nat := 4983230072969 + 3 ^ 40 * 7680254 * 2
def baseEnd_7680254 : Nat := 1314553950205433068201387

theorem tailTrace_7680254 : CollatzResearch.WordTrace tailWord_7680254 prefixEnd_7680254 1314553950205433068201387 := by
  unfold tailWord_7680254
  simp only [CollatzResearch.WordTrace]
  refine ⟨35015234539719864474986977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186747917545172610533263877 35015234539719864474986977)
  ·
    refine ⟨26261425904789898356240233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35015234539719864474986977 26261425904789898356240233)
    ·
      refine ⟨19696069428592423767180175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26261425904789898356240233 19696069428592423767180175)
      ·
        refine ⟨29544104142888635650770263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19696069428592423767180175 29544104142888635650770263)
        ·
          refine ⟨44316156214332953476155395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29544104142888635650770263 44316156214332953476155395)
          ·
            refine ⟨66474234321499430214233093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44316156214332953476155395 66474234321499430214233093)
            ·
              refine ⟨12463918935281143165168705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66474234321499430214233093 12463918935281143165168705)
              ·
                refine ⟨9347939201460857373876529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12463918935281143165168705 9347939201460857373876529)
                ·
                  refine ⟨7010954401095643030407397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9347939201460857373876529 7010954401095643030407397)
                  ·
                    refine ⟨1314553950205433068201387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7010954401095643030407397 1314553950205433068201387)
                    ·
                      rfl

theorem cell23_7680254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_7680254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680254 prefixEnd_7680254 := by exact prefixLift 7680254
  have htrace : WordTrace (prefixWord ++ tailWord_7680254) baseStart_7680254 baseEnd_7680254 := by
    simpa [prefixWord, tailWord_7680254, baseEnd_7680254] using wordTrace_append hprefix tailTrace_7680254
  have hstable : (prefixWord ++ tailWord_7680254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680254).length < 2 ^ (prefixWord ++ tailWord_7680254).sum := by decide
  have hdescent : baseEnd_7680254 < baseStart_7680254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680295 : List Nat := [1, 1, 8, 1, 1, 2, 2, 1, 1, 1, 4]
def baseStart_7680295 : Nat := 118140960795 + 7680295 * 2 ^ 59
def prefixEnd_7680295 : Nat := 4983230072969 + 3 ^ 40 * 7680295 * 2
def baseEnd_7680295 : Nat := 3943682903323133544191473

theorem tailTrace_7680295 : CollatzResearch.WordTrace tailWord_7680295 prefixEnd_7680295 3943682903323133544191473 := by
  unfold tailWord_7680295
  simp only [CollatzResearch.WordTrace]
  refine ⟨280123371710610379802138339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186748914473740253201425559 280123371710610379802138339)
  ·
    refine ⟨420185057565915569703207509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280123371710610379802138339 420185057565915569703207509)
    ·
      refine ⟨4924043643350573082459463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 420185057565915569703207509 4924043643350573082459463)
      ·
        refine ⟨7386065465025859623689195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4924043643350573082459463 7386065465025859623689195)
        ·
          refine ⟨11079098197538789435533793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7386065465025859623689195 11079098197538789435533793)
          ·
            refine ⟨8309323648154092076650345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11079098197538789435533793 8309323648154092076650345)
            ·
              refine ⟨6231992736115569057487759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8309323648154092076650345 6231992736115569057487759)
              ·
                refine ⟨9347989104173353586231639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6231992736115569057487759 9347989104173353586231639)
                ·
                  refine ⟨14021983656260030379347459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9347989104173353586231639 14021983656260030379347459)
                  ·
                    refine ⟨21032975484390045569021189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14021983656260030379347459 21032975484390045569021189)
                    ·
                      refine ⟨3943682903323133544191473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21032975484390045569021189 3943682903323133544191473)
                      ·
                        rfl

theorem cell23_7680295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_7680295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680295 prefixEnd_7680295 := by exact prefixLift 7680295
  have htrace : WordTrace (prefixWord ++ tailWord_7680295) baseStart_7680295 baseEnd_7680295 := by
    simpa [prefixWord, tailWord_7680295, baseEnd_7680295] using wordTrace_append hprefix tailTrace_7680295
  have hstable : (prefixWord ++ tailWord_7680295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680295).length < 2 ^ (prefixWord ++ tailWord_7680295).sum := by decide
  have hdescent : baseEnd_7680295 < baseStart_7680295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680298 : List Nat := [3, 1, 4, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_7680298 : Nat := 118140960795 + 7680298 * 2 ^ 59
def prefixEnd_7680298 : Nat := 4983230072969 + 3 ^ 40 * 7680298 * 2
def baseEnd_7680298 : Nat := 3943684443765097032453959

theorem tailTrace_7680298 : CollatzResearch.WordTrace tailWord_7680298 prefixEnd_7680298 3943684443765097032453959 := by
  unfold tailWord_7680298
  simp only [CollatzResearch.WordTrace]
  refine ⟨70030870282399877828624387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186748987419733007542998365 70030870282399877828624387)
  ·
    refine ⟨105046305423599816742936581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70030870282399877828624387 105046305423599816742936581)
    ·
      refine ⟨19696182266924965639300609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105046305423599816742936581 19696182266924965639300609)
      ·
        refine ⟨14772136700193724229475457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19696182266924965639300609 14772136700193724229475457)
        ·
          refine ⟨11079102525145293172106593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14772136700193724229475457 11079102525145293172106593)
          ·
            refine ⟨8309326893858969879079945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11079102525145293172106593 8309326893858969879079945)
            ·
              refine ⟨6231995170394227409309959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8309326893858969879079945 6231995170394227409309959)
              ·
                refine ⟨9347992755591341113964939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6231995170394227409309959 9347992755591341113964939)
                ·
                  refine ⟨14021989133387011670947409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9347992755591341113964939 14021989133387011670947409)
                  ·
                    refine ⟨10516491850040258753210557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14021989133387011670947409 10516491850040258753210557)
                    ·
                      refine ⟨3943684443765097032453959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10516491850040258753210557 3943684443765097032453959)
                      ·
                        rfl

theorem cell23_7680298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_7680298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680298 prefixEnd_7680298 := by exact prefixLift 7680298
  have htrace : WordTrace (prefixWord ++ tailWord_7680298) baseStart_7680298 baseEnd_7680298 := by
    simpa [prefixWord, tailWord_7680298, baseEnd_7680298] using wordTrace_append hprefix tailTrace_7680298
  have hstable : (prefixWord ++ tailWord_7680298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680298).length < 2 ^ (prefixWord ++ tailWord_7680298).sum := by decide
  have hdescent : baseEnd_7680298 < baseStart_7680298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680320 : List Nat := [2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 3]
def baseStart_7680320 : Nat := 118140960795 + 7680320 * 2 ^ 59
def prefixEnd_7680320 : Nat := 4983230072969 + 3 ^ 40 * 7680320 * 2
def baseEnd_7680320 : Nat := 3943695740339495946378857

theorem tailTrace_7680320 : CollatzResearch.WordTrace tailWord_7680320 prefixEnd_7680320 3943695740339495946378857 := by
  unfold tailWord_7680320
  simp only [CollatzResearch.WordTrace]
  refine ⟨140062141767759904535899207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186749522357013206047865609 140062141767759904535899207)
  ·
    refine ⟨210093212651639856803848811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140062141767759904535899207 210093212651639856803848811)
    ·
      refine ⟨315139818977459785205773217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210093212651639856803848811 315139818977459785205773217)
      ·
        refine ⟨236354864233094838904329913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315139818977459785205773217 236354864233094838904329913)
        ·
          refine ⟨177266148174821129178247435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236354864233094838904329913 177266148174821129178247435)
          ·
            refine ⟨265899222262231693767371153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177266148174821129178247435 265899222262231693767371153)
            ·
              refine ⟨199424416696673770325528365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265899222262231693767371153 199424416696673770325528365)
              ·
                refine ⟨74784156261252663872073137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199424416696673770325528365 74784156261252663872073137)
                ·
                  refine ⟨56088117195939497904054853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74784156261252663872073137 56088117195939497904054853)
                  ·
                    refine ⟨10516521974238655857010285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 56088117195939497904054853 10516521974238655857010285)
                    ·
                      refine ⟨3943695740339495946378857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10516521974238655857010285 3943695740339495946378857)
                      ·
                        rfl

theorem cell23_7680320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_7680320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680320 prefixEnd_7680320 := by exact prefixLift 7680320
  have htrace : WordTrace (prefixWord ++ tailWord_7680320) baseStart_7680320 baseEnd_7680320 := by
    simpa [prefixWord, tailWord_7680320, baseEnd_7680320] using wordTrace_append hprefix tailTrace_7680320
  have hstable : (prefixWord ++ tailWord_7680320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680320).length < 2 ^ (prefixWord ++ tailWord_7680320).sum := by decide
  have hdescent : baseEnd_7680320 < baseStart_7680320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680377 : List Nat := [1, 2, 1, 3, 2, 1, 1, 3, 2, 5, 2]
def baseStart_7680377 : Nat := 118140960795 + 7680377 * 2 ^ 59
def prefixEnd_7680377 : Nat := 4983230072969 + 3 ^ 40 * 7680377 * 2
def baseEnd_7680377 : Nat := 3943725008736802223366095

theorem tailTrace_7680377 : CollatzResearch.WordTrace tailWord_7680377 prefixEnd_7680377 3943725008736802223366095 := by
  unfold tailWord_7680377
  simp only [CollatzResearch.WordTrace]
  refine ⟨280126362496313307806623385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186750908330875538537748923 280126362496313307806623385)
  ·
    refine ⟨210094771872234980854967539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280126362496313307806623385 210094771872234980854967539)
    ·
      refine ⟨315142157808352471282451309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210094771872234980854967539 315142157808352471282451309)
      ·
        refine ⟨118178309178132176730919241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315142157808352471282451309 118178309178132176730919241)
        ·
          refine ⟨88633731883599132548189431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118178309178132176730919241 88633731883599132548189431)
          ·
            refine ⟨132950597825398698822284147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88633731883599132548189431 132950597825398698822284147)
            ·
              refine ⟨199425896738098048233426221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132950597825398698822284147 199425896738098048233426221)
              ·
                refine ⟨74784711276786768087534833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 199425896738098048233426221 74784711276786768087534833)
                ·
                  refine ⟨56088533457590076065651125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 74784711276786768087534833 56088533457590076065651125)
                  ·
                    refine ⟨5258300011649069631154793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56088533457590076065651125 5258300011649069631154793)
                    ·
                      refine ⟨3943725008736802223366095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5258300011649069631154793 3943725008736802223366095)
                      ·
                        rfl

theorem cell23_7680377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 5, 2].length) (baseStart_7680377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680377 prefixEnd_7680377 := by exact prefixLift 7680377
  have htrace : WordTrace (prefixWord ++ tailWord_7680377) baseStart_7680377 baseEnd_7680377 := by
    simpa [prefixWord, tailWord_7680377, baseEnd_7680377] using wordTrace_append hprefix tailTrace_7680377
  have hstable : (prefixWord ++ tailWord_7680377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680377).length < 2 ^ (prefixWord ++ tailWord_7680377).sum := by decide
  have hdescent : baseEnd_7680377 < baseStart_7680377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680385 : List Nat := [1, 2, 4, 3, 1, 3, 2, 1, 2, 2, 2]
def baseStart_7680385 : Nat := 118140960795 + 7680385 * 2 ^ 59
def prefixEnd_7680385 : Nat := 4983230072969 + 3 ^ 40 * 7680385 * 2
def baseEnd_7680385 : Nat := 3943729116582038192066059

theorem tailTrace_7680385 : CollatzResearch.WordTrace tailWord_7680385 prefixEnd_7680385 3943729116582038192066059 := by
  unfold tailWord_7680385
  simp only [CollatzResearch.WordTrace]
  refine ⟨280126654280284325172914609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186751102853522883448609739 280126654280284325172914609)
  ·
    refine ⟨210094990710213243879685957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280126654280284325172914609 210094990710213243879685957)
    ·
      refine ⟨39392810758164983227441117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210094990710213243879685957 39392810758164983227441117)
      ·
        refine ⟨14772304034311868710290419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39392810758164983227441117 14772304034311868710290419)
        ·
          refine ⟨22158456051467803065435629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14772304034311868710290419 22158456051467803065435629)
          ·
            refine ⟨8309421019300426149538361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22158456051467803065435629 8309421019300426149538361)
            ·
              refine ⟨6232065764475319612153771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8309421019300426149538361 6232065764475319612153771)
              ·
                refine ⟨9348098646712979418230657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6232065764475319612153771 9348098646712979418230657)
                ·
                  refine ⟨7011073985034734563672993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9348098646712979418230657 7011073985034734563672993)
                  ·
                    refine ⟨5258305488776050922754745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7011073985034734563672993 5258305488776050922754745)
                    ·
                      refine ⟨3943729116582038192066059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5258305488776050922754745 3943729116582038192066059)
                      ·
                        rfl

theorem cell23_7680385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_7680385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680385 prefixEnd_7680385 := by exact prefixLift 7680385
  have htrace : WordTrace (prefixWord ++ tailWord_7680385) baseStart_7680385 baseEnd_7680385 := by
    simpa [prefixWord, tailWord_7680385, baseEnd_7680385] using wordTrace_append hprefix tailTrace_7680385
  have hstable : (prefixWord ++ tailWord_7680385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680385).length < 2 ^ (prefixWord ++ tailWord_7680385).sum := by decide
  have hdescent : baseEnd_7680385 < baseStart_7680385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680407 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 4]
def baseStart_7680407 : Nat := 118140960795 + 7680407 * 2 ^ 59
def prefixEnd_7680407 : Nat := 4983230072969 + 3 ^ 40 * 7680407 * 2
def baseEnd_7680407 : Nat := 3943740413156437105990957

theorem tailTrace_7680407 : CollatzResearch.WordTrace tailWord_7680407 prefixEnd_7680407 3943740413156437105990957 := by
  unfold tailWord_7680407
  simp only [CollatzResearch.WordTrace]
  refine ⟨280127456686204622930215475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186751637790803081953476983 280127456686204622930215475)
  ·
    refine ⟨420191185029306934395323213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280127456686204622930215475 420191185029306934395323213)
    ·
      refine ⟨157571694385990100398246205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420191185029306934395323213 157571694385990100398246205)
      ·
        refine ⟨59089385394746287649342327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157571694385990100398246205 59089385394746287649342327)
        ·
          refine ⟨88634078092119431474013491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59089385394746287649342327 88634078092119431474013491)
          ·
            refine ⟨132951117138179147211020237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88634078092119431474013491 132951117138179147211020237)
            ·
              refine ⟨49856668926817180204132589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132951117138179147211020237 49856668926817180204132589)
              ·
                refine ⟨18696250847556442576549721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49856668926817180204132589 18696250847556442576549721)
                ·
                  refine ⟨14022188135667331932412291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18696250847556442576549721 14022188135667331932412291)
                  ·
                    refine ⟨21033282203500997898618437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14022188135667331932412291 21033282203500997898618437)
                    ·
                      refine ⟨3943740413156437105990957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21033282203500997898618437 3943740413156437105990957)
                      ·
                        rfl

theorem cell23_7680407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_7680407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680407 prefixEnd_7680407 := by exact prefixLift 7680407
  have htrace : WordTrace (prefixWord ++ tailWord_7680407) baseStart_7680407 baseEnd_7680407 := by
    simpa [prefixWord, tailWord_7680407, baseEnd_7680407] using wordTrace_append hprefix tailTrace_7680407
  have hstable : (prefixWord ++ tailWord_7680407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680407).length < 2 ^ (prefixWord ++ tailWord_7680407).sum := by decide
  have hdescent : baseEnd_7680407 < baseStart_7680407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680414 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_7680414 : Nat := 118140960795 + 7680414 * 2 ^ 59
def prefixEnd_7680414 : Nat := 4983230072969 + 3 ^ 40 * 7680414 * 2
def baseEnd_7680414 : Nat := 3943744007521018578603425

theorem tailTrace_7680414 : CollatzResearch.WordTrace tailWord_7680414 prefixEnd_7680414 3943744007521018578603425 := by
  unfold tailWord_7680414
  simp only [CollatzResearch.WordTrace]
  refine ⟨35015963999647407890715037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186751807998119508750480197 35015963999647407890715037)
  ·
    refine ⟨13130986499867777959018139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35015963999647407890715037 13130986499867777959018139)
    ·
      refine ⟨19696479749801666938527209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13130986499867777959018139 19696479749801666938527209)
      ·
        refine ⟨14772359812351250203895407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19696479749801666938527209 14772359812351250203895407)
        ·
          refine ⟨22158539718526875305843111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14772359812351250203895407 22158539718526875305843111)
          ·
            refine ⟨33237809577790312958764667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22158539718526875305843111 33237809577790312958764667)
            ·
              refine ⟨49856714366685469438147001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33237809577790312958764667 49856714366685469438147001)
              ·
                refine ⟨37392535775014102078610251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49856714366685469438147001 37392535775014102078610251)
                ·
                  refine ⟨56088803662521153117915377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37392535775014102078610251 56088803662521153117915377)
                  ·
                    refine ⟨42066602746890864838436533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56088803662521153117915377 42066602746890864838436533)
                    ·
                      refine ⟨3943744007521018578603425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42066602746890864838436533 3943744007521018578603425)
                      ·
                        rfl

theorem cell23_7680414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_7680414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680414 prefixEnd_7680414 := by exact prefixLift 7680414
  have htrace : WordTrace (prefixWord ++ tailWord_7680414) baseStart_7680414 baseEnd_7680414 := by
    simpa [prefixWord, tailWord_7680414, baseEnd_7680414] using wordTrace_append hprefix tailTrace_7680414
  have hstable : (prefixWord ++ tailWord_7680414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680414).length < 2 ^ (prefixWord ++ tailWord_7680414).sum := by decide
  have hdescent : baseEnd_7680414 < baseStart_7680414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680468 : List Nat := [2, 4, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_7680468 : Nat := 118140960795 + 7680468 * 2 ^ 59
def prefixEnd_7680468 : Nat := 4983230072969 + 3 ^ 40 * 7680468 * 2
def baseEnd_7680468 : Nat := 1314590578492120455776059

theorem tailTrace_7680468 : CollatzResearch.WordTrace tailWord_7680468 prefixEnd_7680468 1314590578492120455776059 := by
  unfold tailWord_7680468
  simp only [CollatzResearch.WordTrace]
  refine ⟨140064840769491815174093029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186753121025989086898790705 140064840769491815174093029)
  ·
    refine ⟨26262157644279715345142443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 140064840769491815174093029 26262157644279715345142443)
    ·
      refine ⟨39393236466419573017713665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26262157644279715345142443 39393236466419573017713665)
      ·
        refine ⟨29544927349814679763285249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39393236466419573017713665 29544927349814679763285249)
        ·
          refine ⟨22158695512361009822463937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29544927349814679763285249 22158695512361009822463937)
          ·
            refine ⟨16619021634270757366847953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22158695512361009822463937 16619021634270757366847953)
            ·
              refine ⟨12464266225703068025135965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16619021634270757366847953 12464266225703068025135965)
              ·
                refine ⟨4674099834638650509425987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12464266225703068025135965 4674099834638650509425987)
                ·
                  refine ⟨7011149751957975764138981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4674099834638650509425987 7011149751957975764138981)
                  ·
                    refine ⟨1314590578492120455776059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7011149751957975764138981 1314590578492120455776059)
                    ·
                      rfl

theorem cell23_7680468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_7680468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680468 prefixEnd_7680468 := by exact prefixLift 7680468
  have htrace : WordTrace (prefixWord ++ tailWord_7680468) baseStart_7680468 baseEnd_7680468 := by
    simpa [prefixWord, tailWord_7680468, baseEnd_7680468] using wordTrace_append hprefix tailTrace_7680468
  have hstable : (prefixWord ++ tailWord_7680468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680468).length < 2 ^ (prefixWord ++ tailWord_7680468).sum := by decide
  have hdescent : baseEnd_7680468 < baseStart_7680468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680474 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3]
def baseStart_7680474 : Nat := 118140960795 + 7680474 * 2 ^ 59
def prefixEnd_7680474 : Nat := 4983230072969 + 3 ^ 40 * 7680474 * 2
def baseEnd_7680474 : Nat := 3943774816360288343853149

theorem tailTrace_7680474 : CollatzResearch.WordTrace tailWord_7680474 prefixEnd_7680474 3943774816360288343853149 := by
  unfold tailWord_7680474
  simp only [CollatzResearch.WordTrace]
  refine ⟨70032475094240473343226119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186753266917974595581936317 70032475094240473343226119)
  ·
    refine ⟨105048712641360710014839179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70032475094240473343226119 105048712641360710014839179)
    ·
      refine ⟨157573068962041065022258769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105048712641360710014839179 157573068962041065022258769)
      ·
        refine ⟨118179801721530798766694077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157573068962041065022258769 118179801721530798766694077)
        ·
          refine ⟨44317425645574049537510279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118179801721530798766694077 44317425645574049537510279)
          ·
            refine ⟨66476138468361074306265419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44317425645574049537510279 66476138468361074306265419)
            ·
              refine ⟨99714207702541611459398129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66476138468361074306265419 99714207702541611459398129)
              ·
                refine ⟨74785655776906208594548597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 99714207702541611459398129 74785655776906208594548597)
                ·
                  refine ⟨7011155229084957055738931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 74785655776906208594548597 7011155229084957055738931)
                  ·
                    refine ⟨10516732843627435583608397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7011155229084957055738931 10516732843627435583608397)
                    ·
                      refine ⟨3943774816360288343853149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10516732843627435583608397 3943774816360288343853149)
                      ·
                        rfl

theorem cell23_7680474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 5, 1, 3].length) (baseStart_7680474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680474 prefixEnd_7680474 := by exact prefixLift 7680474
  have htrace : WordTrace (prefixWord ++ tailWord_7680474) baseStart_7680474 baseEnd_7680474 := by
    simpa [prefixWord, tailWord_7680474, baseEnd_7680474] using wordTrace_append hprefix tailTrace_7680474
  have hstable : (prefixWord ++ tailWord_7680474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680474).length < 2 ^ (prefixWord ++ tailWord_7680474).sum := by decide
  have hdescent : baseEnd_7680474 < baseStart_7680474 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680491 : List Nat := [1, 1, 1, 1, 2, 3, 3, 6, 1, 1, 3]
def baseStart_7680491 : Nat := 118140960795 + 7680491 * 2 ^ 59
def prefixEnd_7680491 : Nat := 4983230072969 + 3 ^ 40 * 7680491 * 2
def baseEnd_7680491 : Nat := 3943783545531414777340571

theorem tailTrace_7680491 : CollatzResearch.WordTrace tailWord_7680491 prefixEnd_7680491 3943783545531414777340571 := by
  unfold tailWord_7680491
  simp only [CollatzResearch.WordTrace]
  refine ⟨280130520417900305276273327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186753680278600203517515551 280130520417900305276273327)
  ·
    refine ⟨420195780626850457914409991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280130520417900305276273327 420195780626850457914409991)
    ·
      refine ⟨630293670940275686871614987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420195780626850457914409991 630293670940275686871614987)
      ·
        refine ⟨945440506410413530307422481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630293670940275686871614987 945440506410413530307422481)
        ·
          refine ⟨709080379807810147730566861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 945440506410413530307422481 709080379807810147730566861)
          ·
            refine ⟨265905142427928805398962573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 709080379807810147730566861 265905142427928805398962573)
            ·
              refine ⟨99714428410473302024610965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 265905142427928805398962573 99714428410473302024610965)
              ·
                refine ⟨4674113831740936032403639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 99714428410473302024610965 4674113831740936032403639)
                ·
                  refine ⟨7011170747611404048605459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4674113831740936032403639 7011170747611404048605459)
                  ·
                    refine ⟨10516756121417106072908189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7011170747611404048605459 10516756121417106072908189)
                    ·
                      refine ⟨3943783545531414777340571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10516756121417106072908189 3943783545531414777340571)
                      ·
                        rfl

theorem cell23_7680491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 6, 1, 1, 3].length) (baseStart_7680491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680491 prefixEnd_7680491 := by exact prefixLift 7680491
  have htrace : WordTrace (prefixWord ++ tailWord_7680491) baseStart_7680491 baseEnd_7680491 := by
    simpa [prefixWord, tailWord_7680491, baseEnd_7680491] using wordTrace_append hprefix tailTrace_7680491
  have hstable : (prefixWord ++ tailWord_7680491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680491).length < 2 ^ (prefixWord ++ tailWord_7680491).sum := by decide
  have hdescent : baseEnd_7680491 < baseStart_7680491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680507 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 8, 4]
def baseStart_7680507 : Nat := 118140960795 + 7680507 * 2 ^ 59
def prefixEnd_7680507 : Nat := 4983230072969 + 3 ^ 40 * 7680507 * 2
def baseEnd_7680507 : Nat := 1314597253740628904913499

theorem tailTrace_7680507 : CollatzResearch.WordTrace tailWord_7680507 prefixEnd_7680507 1314597253740628904913499 := by
  unfold tailWord_7680507
  simp only [CollatzResearch.WordTrace]
  refine ⟨280131103985842340008855775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186754069323894893339237183 280131103985842340008855775)
  ·
    refine ⟨420196655978763510013283663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280131103985842340008855775 420196655978763510013283663)
    ·
      refine ⟨630294983968145265019925495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420196655978763510013283663 630294983968145265019925495)
      ·
        refine ⟨945442475952217897529888243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630294983968145265019925495 945442475952217897529888243)
        ·
          refine ⟨1418163713928326846294832365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945442475952217897529888243 1418163713928326846294832365)
          ·
            refine ⟨531811392723122567360562137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1418163713928326846294832365 531811392723122567360562137)
            ·
              refine ⟨398858544542341925520421603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 531811392723122567360562137 398858544542341925520421603)
              ·
                refine ⟨598287816813512888280632405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 398858544542341925520421603 598287816813512888280632405)
                ·
                  refine ⟨7011185353283354159538661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 598287816813512888280632405 7011185353283354159538661)
                  ·
                    refine ⟨1314597253740628904913499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7011185353283354159538661 1314597253740628904913499)
                    ·
                      rfl

theorem cell23_7680507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 4].length) (baseStart_7680507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680507 prefixEnd_7680507 := by exact prefixLift 7680507
  have htrace : WordTrace (prefixWord ++ tailWord_7680507) baseStart_7680507 baseEnd_7680507 := by
    simpa [prefixWord, tailWord_7680507, baseEnd_7680507] using wordTrace_append hprefix tailTrace_7680507
  have hstable : (prefixWord ++ tailWord_7680507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680507).length < 2 ^ (prefixWord ++ tailWord_7680507).sum := by decide
  have hdescent : baseEnd_7680507 < baseStart_7680507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680524 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 4, 4]
def baseStart_7680524 : Nat := 118140960795 + 7680524 * 2 ^ 59
def prefixEnd_7680524 : Nat := 4983230072969 + 3 ^ 40 * 7680524 * 2
def baseEnd_7680524 : Nat := 1314600163464337716075973

theorem tailTrace_7680524 : CollatzResearch.WordTrace tailWord_7680524 prefixEnd_7680524 1314600163464337716075973 := by
  unfold tailWord_7680524
  simp only [CollatzResearch.WordTrace]
  refine ⟨140065862013390375956112313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186754482684520501274816417 140065862013390375956112313)
  ·
    refine ⟨105049396510042781967084235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140065862013390375956112313 105049396510042781967084235)
    ·
      refine ⟨157574094765064172950626353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105049396510042781967084235 157574094765064172950626353)
      ·
        refine ⟨118180571073798129712969765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157574094765064172950626353 118180571073798129712969765)
        ·
          refine ⟨22158857076337149321181831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118180571073798129712969765 22158857076337149321181831)
          ·
            refine ⟨33238285614505723981772747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22158857076337149321181831 33238285614505723981772747)
            ·
              refine ⟨49857428421758585972659121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33238285614505723981772747 49857428421758585972659121)
              ·
                refine ⟨37393071316318939479494341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49857428421758585972659121 37393071316318939479494341)
                ·
                  refine ⟨7011200871809801152405189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37393071316318939479494341 7011200871809801152405189)
                  ·
                    refine ⟨1314600163464337716075973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7011200871809801152405189 1314600163464337716075973)
                    ·
                      rfl

theorem cell23_7680524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_7680524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680524 prefixEnd_7680524 := by exact prefixLift 7680524
  have htrace : WordTrace (prefixWord ++ tailWord_7680524) baseStart_7680524 baseEnd_7680524 := by
    simpa [prefixWord, tailWord_7680524, baseEnd_7680524] using wordTrace_append hprefix tailTrace_7680524
  have hstable : (prefixWord ++ tailWord_7680524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680524).length < 2 ^ (prefixWord ++ tailWord_7680524).sum := by decide
  have hdescent : baseEnd_7680524 < baseStart_7680524 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680554 : List Nat := [3, 1, 4, 1, 1, 3, 2, 8]
def baseStart_7680554 : Nat := 118140960795 + 7680554 * 2 ^ 59
def prefixEnd_7680554 : Nat := 4983230072969 + 3 ^ 40 * 7680554 * 2
def baseEnd_7680554 : Nat := 146067255363431408550103

theorem tailTrace_7680554 : CollatzResearch.WordTrace tailWord_7680554 prefixEnd_7680554 146067255363431408550103 := by
  unfold tailWord_7680554
  simp only [CollatzResearch.WordTrace]
  refine ⟨70033204554168016758954179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186755212144448044690544477 70033204554168016758954179)
  ·
    refine ⟨105049806831252025138431269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70033204554168016758954179 105049806831252025138431269)
    ·
      refine ⟨19696838780859754713455863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105049806831252025138431269 19696838780859754713455863)
      ·
        refine ⟨29545258171289632070183795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19696838780859754713455863 29545258171289632070183795)
        ·
          refine ⟨44317887256934448105275693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29545258171289632070183795 44317887256934448105275693)
          ·
            refine ⟨16619207721350418039478385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44317887256934448105275693 16619207721350418039478385)
            ·
              refine ⟨12464405791012813529608789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16619207721350418039478385 12464405791012813529608789)
              ·
                refine ⟨146067255363431408550103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12464405791012813529608789 146067255363431408550103)
                ·
                  rfl

theorem cell23_7680554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 8].length) (baseStart_7680554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680554 prefixEnd_7680554 := by exact prefixLift 7680554
  have htrace : WordTrace (prefixWord ++ tailWord_7680554) baseStart_7680554 baseEnd_7680554 := by
    simpa [prefixWord, tailWord_7680554, baseEnd_7680554] using wordTrace_append hprefix tailTrace_7680554
  have hstable : (prefixWord ++ tailWord_7680554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680554).length < 2 ^ (prefixWord ++ tailWord_7680554).sum := by decide
  have hdescent : baseEnd_7680554 < baseStart_7680554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680558 : List Nat := [4, 1, 3, 1, 3, 1, 1, 3, 2, 4]
def baseStart_7680558 : Nat := 118140960795 + 7680558 * 2 ^ 59
def prefixEnd_7680558 : Nat := 4983230072969 + 3 ^ 40 * 7680558 * 2
def baseEnd_7680558 : Nat := 1314605982911755338400921

theorem tailTrace_7680558 : CollatzResearch.WordTrace tailWord_7680558 prefixEnd_7680558 1314605982911755338400921 := by
  unfold tailWord_7680558
  simp only [CollatzResearch.WordTrace]
  refine ⟨35016620513582196964870291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186755309405771717145974885 35016620513582196964870291)
  ·
    refine ⟨52524930770373295447305437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35016620513582196964870291 52524930770373295447305437)
    ·
      refine ⟨19696849038889985792739539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52524930770373295447305437 19696849038889985792739539)
      ·
        refine ⟨29545273558334978689109309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19696849038889985792739539 29545273558334978689109309)
        ·
          refine ⟨11079477584375617008415991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 29545273558334978689109309 11079477584375617008415991)
          ·
            refine ⟨16619216376563425512623987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11079477584375617008415991 16619216376563425512623987)
            ·
              refine ⟨24928824564845138268935981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16619216376563425512623987 24928824564845138268935981)
              ·
                refine ⟨9348309211816926850850993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24928824564845138268935981 9348309211816926850850993)
                ·
                  refine ⟨7011231908862695138138245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9348309211816926850850993 7011231908862695138138245)
                  ·
                    refine ⟨1314605982911755338400921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7011231908862695138138245 1314605982911755338400921)
                    ·
                      rfl

theorem cell23_7680558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_7680558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680558 prefixEnd_7680558 := by exact prefixLift 7680558
  have htrace : WordTrace (prefixWord ++ tailWord_7680558) baseStart_7680558 baseEnd_7680558 := by
    simpa [prefixWord, tailWord_7680558, baseEnd_7680558] using wordTrace_append hprefix tailTrace_7680558
  have hstable : (prefixWord ++ tailWord_7680558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680558).length < 2 ^ (prefixWord ++ tailWord_7680558).sum := by decide
  have hdescent : baseEnd_7680558 < baseStart_7680558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680591 : List Nat := [1, 1, 2, 1, 1, 2, 4, 5, 1, 3, 2]
def baseStart_7680591 : Nat := 118140960795 + 7680591 * 2 ^ 59
def prefixEnd_7680591 : Nat := 4983230072969 + 3 ^ 40 * 7680591 * 2
def baseEnd_7680591 : Nat := 3943834893596864386090111

theorem tailTrace_7680591 : CollatzResearch.WordTrace tailWord_7680591 prefixEnd_7680591 3943834893596864386090111 := by
  unfold tailWord_7680591
  simp only [CollatzResearch.WordTrace]
  refine ⟨280134167717538022354913627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186756111811692014903275751 280134167717538022354913627)
  ·
    refine ⟨420201251576307033532370441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280134167717538022354913627 420201251576307033532370441)
    ·
      refine ⟨315150938682230275149277831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420201251576307033532370441 315150938682230275149277831)
      ·
        refine ⟨472726408023345412723916747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315150938682230275149277831 472726408023345412723916747)
        ·
          refine ⟨709089612035018119085875121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472726408023345412723916747 709089612035018119085875121)
          ·
            refine ⟨531817209026263589314406341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 709089612035018119085875121 531817209026263589314406341)
            ·
              refine ⟨99715726692424422996451189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 531817209026263589314406341 99715726692424422996451189)
              ·
                refine ⟨9348349377414789655917299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99715726692424422996451189 9348349377414789655917299)
                ·
                  refine ⟨14022524066122184483875949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9348349377414789655917299 14022524066122184483875949)
                  ·
                    refine ⟨5258446524795819181453481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14022524066122184483875949 5258446524795819181453481)
                    ·
                      refine ⟨3943834893596864386090111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5258446524795819181453481 3943834893596864386090111)
                      ·
                        rfl

theorem cell23_7680591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 5, 1, 3, 2].length) (baseStart_7680591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680591 prefixEnd_7680591 := by exact prefixLift 7680591
  have htrace : WordTrace (prefixWord ++ tailWord_7680591) baseStart_7680591 baseEnd_7680591 := by
    simpa [prefixWord, tailWord_7680591, baseEnd_7680591] using wordTrace_append hprefix tailTrace_7680591
  have hstable : (prefixWord ++ tailWord_7680591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680591).length < 2 ^ (prefixWord ++ tailWord_7680591).sum := by decide
  have hdescent : baseEnd_7680591 < baseStart_7680591 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680607 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 5]
def baseStart_7680607 : Nat := 118140960795 + 7680607 * 2 ^ 59
def prefixEnd_7680607 : Nat := 4983230072969 + 3 ^ 40 * 7680607 * 2
def baseEnd_7680607 : Nat := 3943843109287336323490037

theorem tailTrace_7680607 : CollatzResearch.WordTrace tailWord_7680607 prefixEnd_7680607 3943843109287336323490037 := by
  unfold tailWord_7680607
  simp only [CollatzResearch.WordTrace]
  refine ⟨280134751285480057087496075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186756500856986704724997383 280134751285480057087496075)
  ·
    refine ⟨420202126928220085631244113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280134751285480057087496075 420202126928220085631244113)
    ·
      refine ⟨315151595196165064223433085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420202126928220085631244113 315151595196165064223433085)
      ·
        refine ⟨118181848198561899083787407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 315151595196165064223433085 118181848198561899083787407)
        ·
          refine ⟨177272772297842848625681111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118181848198561899083787407 177272772297842848625681111)
          ·
            refine ⟨265909158446764272938521667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177272772297842848625681111 265909158446764272938521667)
            ·
              refine ⟨398863737670146409407782501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265909158446764272938521667 398863737670146409407782501)
              ·
                refine ⟨74786950813152451763959219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 398863737670146409407782501 74786950813152451763959219)
                ·
                  refine ⟨112180426219728677645938829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 74786950813152451763959219 112180426219728677645938829)
                  ·
                    refine ⟨42067659832398254117227061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 112180426219728677645938829 42067659832398254117227061)
                    ·
                      refine ⟨3943843109287336323490037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42067659832398254117227061 3943843109287336323490037)
                      ·
                        rfl

theorem cell23_7680607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 3, 5].length) (baseStart_7680607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680607 prefixEnd_7680607 := by exact prefixLift 7680607
  have htrace : WordTrace (prefixWord ++ tailWord_7680607) baseStart_7680607 baseEnd_7680607 := by
    simpa [prefixWord, tailWord_7680607, baseEnd_7680607] using wordTrace_append hprefix tailTrace_7680607
  have hstable : (prefixWord ++ tailWord_7680607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680607).length < 2 ^ (prefixWord ++ tailWord_7680607).sum := by decide
  have hdescent : baseEnd_7680607 < baseStart_7680607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680667 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 7]
def baseStart_7680667 : Nat := 118140960795 + 7680667 * 2 ^ 59
def prefixEnd_7680667 : Nat := 4983230072969 + 3 ^ 40 * 7680667 * 2
def baseEnd_7680667 : Nat := 3943873918126606088739761

theorem tailTrace_7680667 : CollatzResearch.WordTrace tailWord_7680667 prefixEnd_7680667 3943873918126606088739761 := by
  unfold tailWord_7680667
  simp only [CollatzResearch.WordTrace]
  refine ⟨280136939665262687334680255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186757959776841791556453503 280136939665262687334680255)
  ·
    refine ⟨420205409497894031002020383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280136939665262687334680255 420205409497894031002020383)
    ·
      refine ⟨630308114246841046503030575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420205409497894031002020383 630308114246841046503030575)
      ·
        refine ⟨945462171370261569754545863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630308114246841046503030575 945462171370261569754545863)
        ·
          refine ⟨1418193257055392354631818795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945462171370261569754545863 1418193257055392354631818795)
          ·
            refine ⟨2127289885583088531947728193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418193257055392354631818795 2127289885583088531947728193)
            ·
              refine ⟨1595467414187316398960796145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2127289885583088531947728193 1595467414187316398960796145)
              ·
                refine ⟨1196600560640487299220597109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1595467414187316398960796145 1196600560640487299220597109)
                ·
                  refine ⟨112181302560045684301930979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1196600560640487299220597109 112181302560045684301930979)
                  ·
                    refine ⟨168271953840068526452896469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 112181302560045684301930979 168271953840068526452896469)
                    ·
                      refine ⟨3943873918126606088739761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 168271953840068526452896469 3943873918126606088739761)
                      ·
                        rfl

theorem cell23_7680667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 7].length) (baseStart_7680667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680667 prefixEnd_7680667 := by exact prefixLift 7680667
  have htrace : WordTrace (prefixWord ++ tailWord_7680667) baseStart_7680667 baseEnd_7680667 := by
    simpa [prefixWord, tailWord_7680667, baseEnd_7680667] using wordTrace_append hprefix tailTrace_7680667
  have hstable : (prefixWord ++ tailWord_7680667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680667).length < 2 ^ (prefixWord ++ tailWord_7680667).sum := by decide
  have hdescent : baseEnd_7680667 < baseStart_7680667 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680672 : List Nat := [2, 1, 1, 4, 4, 1, 3, 1, 2, 2, 2]
def baseStart_7680672 : Nat := 118140960795 + 7680672 * 2 ^ 59
def prefixEnd_7680672 : Nat := 4983230072969 + 3 ^ 40 * 7680672 * 2
def baseEnd_7680672 : Nat := 3943876485529878569177239

theorem tailTrace_7680672 : CollatzResearch.WordTrace tailWord_7680672 prefixEnd_7680672 3943876485529878569177239 := by
  unfold tailWord_7680672
  simp only [CollatzResearch.WordTrace]
  refine ⟨140068561015122286594306135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186758081353496382125741513 140068561015122286594306135)
  ·
    refine ⟨210102841522683429891459203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140068561015122286594306135 210102841522683429891459203)
    ·
      refine ⟨315154262284025144837188805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210102841522683429891459203 315154262284025144837188805)
      ·
        refine ⟨59091424178254714656972901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 315154262284025144837188805 59091424178254714656972901)
        ·
          refine ⟨11079642033422758998182419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59091424178254714656972901 11079642033422758998182419)
          ·
            refine ⟨16619463050134138497273629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11079642033422758998182419 16619463050134138497273629)
            ·
              refine ⟨6232298643800301936477611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16619463050134138497273629 6232298643800301936477611)
              ·
                refine ⟨9348447965700452904716417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6232298643800301936477611 9348447965700452904716417)
                ·
                  refine ⟨7011335974275339678537313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9348447965700452904716417 7011335974275339678537313)
                  ·
                    refine ⟨5258501980706504758902985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7011335974275339678537313 5258501980706504758902985)
                    ·
                      refine ⟨3943876485529878569177239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5258501980706504758902985 3943876485529878569177239)
                      ·
                        rfl

theorem cell23_7680672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 1, 2, 2, 2].length) (baseStart_7680672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680672 prefixEnd_7680672 := by exact prefixLift 7680672
  have htrace : WordTrace (prefixWord ++ tailWord_7680672) baseStart_7680672 baseEnd_7680672 := by
    simpa [prefixWord, tailWord_7680672, baseEnd_7680672] using wordTrace_append hprefix tailTrace_7680672
  have hstable : (prefixWord ++ tailWord_7680672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680672).length < 2 ^ (prefixWord ++ tailWord_7680672).sum := by decide
  have hdescent : baseEnd_7680672 < baseStart_7680672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680695 : List Nat := [1, 1, 3, 1, 7, 1, 1, 3, 5]
def baseStart_7680695 : Nat := 118140960795 + 7680695 * 2 ^ 59
def prefixEnd_7680695 : Nat := 4983230072969 + 3 ^ 40 * 7680695 * 2
def baseEnd_7680695 : Nat := 438209810620547997687737

theorem tailTrace_7680695 : CollatzResearch.WordTrace tailWord_7680695 prefixEnd_7680695 438209810620547997687737 := by
  unfold tailWord_7680695
  simp only [CollatzResearch.WordTrace]
  refine ⟨280137960909161248116699539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186758640606107498744466359 280137960909161248116699539)
  ·
    refine ⟨420206941363741872175049309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280137960909161248116699539 420206941363741872175049309)
    ·
      refine ⟨157577603011403202065643491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420206941363741872175049309 157577603011403202065643491)
      ·
        refine ⟨236366404517104803098465237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157577603011403202065643491 236366404517104803098465237)
        ·
          refine ⟨5539837605869643822620279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 236366404517104803098465237 5539837605869643822620279)
          ·
            refine ⟨8309756408804465733930419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5539837605869643822620279 8309756408804465733930419)
            ·
              refine ⟨12464634613206698600895629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8309756408804465733930419 12464634613206698600895629)
              ·
                refine ⟨4674237979952511975335861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12464634613206698600895629 4674237979952511975335861)
                ·
                  refine ⟨438209810620547997687737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4674237979952511975335861 438209810620547997687737)
                  ·
                    rfl

theorem cell23_7680695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 5].length) (baseStart_7680695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680695 prefixEnd_7680695 := by exact prefixLift 7680695
  have htrace : WordTrace (prefixWord ++ tailWord_7680695) baseStart_7680695 baseEnd_7680695 := by
    simpa [prefixWord, tailWord_7680695, baseEnd_7680695] using wordTrace_append hprefix tailTrace_7680695
  have hstable : (prefixWord ++ tailWord_7680695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680695).length < 2 ^ (prefixWord ++ tailWord_7680695).sum := by decide
  have hdescent : baseEnd_7680695 < baseStart_7680695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680711 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 2, 4, 2]
def baseStart_7680711 : Nat := 118140960795 + 7680711 * 2 ^ 59
def prefixEnd_7680711 : Nat := 4983230072969 + 3 ^ 40 * 7680711 * 2
def baseEnd_7680711 : Nat := 3943896511275403916589559

theorem tailTrace_7680711 : CollatzResearch.WordTrace tailWord_7680711 prefixEnd_7680711 3943896511275403916589559 := by
  unfold tailWord_7680711
  simp only [CollatzResearch.WordTrace]
  refine ⟨280138544477103282849281987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186759029651402188566187991 280138544477103282849281987)
  ·
    refine ⟨420207816715654924273922981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280138544477103282849281987 420207816715654924273922981)
    ·
      refine ⟨78788965634185298301360559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 420207816715654924273922981 78788965634185298301360559)
      ·
        refine ⟨118183448451277947452040839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78788965634185298301360559 118183448451277947452040839)
        ·
          refine ⟨177275172676916921178061259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118183448451277947452040839 177275172676916921178061259)
          ·
            refine ⟨265912759015375381767091889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177275172676916921178061259 265912759015375381767091889)
            ·
              refine ⟨199434569261531536325318917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 265912759015375381767091889 199434569261531536325318917)
              ·
                refine ⟨37393981736537163060997297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 199434569261531536325318917 37393981736537163060997297)
                ·
                  refine ⟨28045486302402872295747973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37393981736537163060997297 28045486302402872295747973)
                  ·
                    refine ⟨5258528681700538555452745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28045486302402872295747973 5258528681700538555452745)
                    ·
                      refine ⟨3943896511275403916589559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5258528681700538555452745 3943896511275403916589559)
                      ·
                        rfl

theorem cell23_7680711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 4, 2].length) (baseStart_7680711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680711 prefixEnd_7680711 := by exact prefixLift 7680711
  have htrace : WordTrace (prefixWord ++ tailWord_7680711) baseStart_7680711 baseEnd_7680711 := by
    simpa [prefixWord, tailWord_7680711, baseEnd_7680711] using wordTrace_append hprefix tailTrace_7680711
  have hstable : (prefixWord ++ tailWord_7680711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680711).length < 2 ^ (prefixWord ++ tailWord_7680711).sum := by decide
  have hdescent : baseEnd_7680711 < baseStart_7680711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680771 : List Nat := [1, 1, 1, 3, 2, 2, 1, 2, 3, 5, 2]
def baseStart_7680771 : Nat := 118140960795 + 7680771 * 2 ^ 59
def prefixEnd_7680771 : Nat := 4983230072969 + 3 ^ 40 * 7680771 * 2
def baseEnd_7680771 : Nat := 3943927320114673681839283

theorem tailTrace_7680771 : CollatzResearch.WordTrace tailWord_7680771 prefixEnd_7680771 3943927320114673681839283 := by
  unfold tailWord_7680771
  simp only [CollatzResearch.WordTrace]
  refine ⟨280140732856885913096466167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186760488571257275397644111 280140732856885913096466167)
  ·
    refine ⟨420211099285328869644699251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280140732856885913096466167 420211099285328869644699251)
    ·
      refine ⟨630316648927993304467048877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420211099285328869644699251 630316648927993304467048877)
      ·
        refine ⟨236368743347997489175143329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 630316648927993304467048877 236368743347997489175143329)
        ·
          refine ⟨177276557510998116881357497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236368743347997489175143329 177276557510998116881357497)
          ·
            refine ⟨132957418133248587661018123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177276557510998116881357497 132957418133248587661018123)
            ·
              refine ⟨199436127199872881491527185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132957418133248587661018123 199436127199872881491527185)
              ·
                refine ⟨149577095399904661118645389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199436127199872881491527185 149577095399904661118645389)
                ·
                  refine ⟨56091410774964247919492021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 149577095399904661118645389 56091410774964247919492021)
                  ·
                    refine ⟨5258569760152898242452377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56091410774964247919492021 5258569760152898242452377)
                    ·
                      refine ⟨3943927320114673681839283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5258569760152898242452377 3943927320114673681839283)
                      ·
                        rfl

theorem cell23_7680771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 5, 2].length) (baseStart_7680771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680771 prefixEnd_7680771 := by exact prefixLift 7680771
  have htrace : WordTrace (prefixWord ++ tailWord_7680771) baseStart_7680771 baseEnd_7680771 := by
    simpa [prefixWord, tailWord_7680771, baseEnd_7680771] using wordTrace_append hprefix tailTrace_7680771
  have hstable : (prefixWord ++ tailWord_7680771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680771).length < 2 ^ (prefixWord ++ tailWord_7680771).sum := by decide
  have hdescent : baseEnd_7680771 < baseStart_7680771 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680778 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 3, 1, 3]
def baseStart_7680778 : Nat := 118140960795 + 7680778 * 2 ^ 59
def prefixEnd_7680778 : Nat := 4983230072969 + 3 ^ 40 * 7680778 * 2
def baseEnd_7680778 : Nat := 3943930914479255154451751

theorem tailTrace_7680778 : CollatzResearch.WordTrace tailWord_7680778 prefixEnd_7680778 3943930914479255154451751 := by
  unfold tailWord_7680778
  simp only [CollatzResearch.WordTrace]
  refine ⟨70035247041965138322992747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186760658778573702194647325 70035247041965138322992747)
  ·
    refine ⟨105052870562947707484489121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70035247041965138322992747 105052870562947707484489121)
    ·
      refine ⟨78789652922210780613366841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105052870562947707484489121 78789652922210780613366841)
      ·
        refine ⟨59092239691658085460025131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78789652922210780613366841 59092239691658085460025131)
        ·
          refine ⟨88638359537487128190037697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59092239691658085460025131 88638359537487128190037697)
          ·
            refine ⟨66478769653115346142528273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88638359537487128190037697 66478769653115346142528273)
            ·
              refine ⟨49859077239836509606896205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66478769653115346142528273 49859077239836509606896205)
              ·
                refine ⟨18697153964938691102586077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49859077239836509606896205 18697153964938691102586077)
                ·
                  refine ⟨7011432736852009163469779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18697153964938691102586077 7011432736852009163469779)
                  ·
                    refine ⟨10517149105278013745204669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7011432736852009163469779 10517149105278013745204669)
                    ·
                      refine ⟨3943930914479255154451751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10517149105278013745204669 3943930914479255154451751)
                      ·
                        rfl

theorem cell23_7680778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_7680778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680778 prefixEnd_7680778 := by exact prefixLift 7680778
  have htrace : WordTrace (prefixWord ++ tailWord_7680778) baseStart_7680778 baseEnd_7680778 := by
    simpa [prefixWord, tailWord_7680778, baseEnd_7680778] using wordTrace_append hprefix tailTrace_7680778
  have hstable : (prefixWord ++ tailWord_7680778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680778).length < 2 ^ (prefixWord ++ tailWord_7680778).sum := by decide
  have hdescent : baseEnd_7680778 < baseStart_7680778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680801 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 3, 1, 4]
def baseStart_7680801 : Nat := 118140960795 + 7680801 * 2 ^ 59
def prefixEnd_7680801 : Nat := 4983230072969 + 3 ^ 40 * 7680801 * 2
def baseEnd_7680801 : Nat := 3943942724534308564464145

theorem tailTrace_7680801 : CollatzResearch.WordTrace tailWord_7680801 prefixEnd_7680801 3943942724534308564464145 := by
  unfold tailWord_7680801
  simp only [CollatzResearch.WordTrace]
  refine ⟨280141827046777228220058257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186761218031184818813372171 280141827046777228220058257)
  ·
    refine ⟨210106370285082921165043693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280141827046777228220058257 210106370285082921165043693)
    ·
      refine ⟨78789888856906095436891385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210106370285082921165043693 78789888856906095436891385)
      ·
        refine ⟨59092416642679571577668539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78789888856906095436891385 59092416642679571577668539)
        ·
          refine ⟨88638624964019357366502809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59092416642679571577668539 88638624964019357366502809)
          ·
            refine ⟨66478968723014518024877107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88638624964019357366502809 66478968723014518024877107)
            ·
              refine ⟨99718453084521777037315661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66478968723014518024877107 99718453084521777037315661)
              ·
                refine ⟨37394419906695666388993373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99718453084521777037315661 37394419906695666388993373)
                ·
                  refine ⟨14022907465010874895872515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37394419906695666388993373 14022907465010874895872515)
                  ·
                    refine ⟨21034361197516312343808773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14022907465010874895872515 21034361197516312343808773)
                    ·
                      refine ⟨3943942724534308564464145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21034361197516312343808773 3943942724534308564464145)
                      ·
                        rfl

theorem cell23_7680801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_7680801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680801 prefixEnd_7680801 := by exact prefixLift 7680801
  have htrace : WordTrace (prefixWord ++ tailWord_7680801) baseStart_7680801 baseEnd_7680801 := by
    simpa [prefixWord, tailWord_7680801, baseEnd_7680801] using wordTrace_append hprefix tailTrace_7680801
  have hstable : (prefixWord ++ tailWord_7680801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680801).length < 2 ^ (prefixWord ++ tailWord_7680801).sum := by decide
  have hdescent : baseEnd_7680801 < baseStart_7680801 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680818 : List Nat := [3, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4]
def baseStart_7680818 : Nat := 118140960795 + 7680818 * 2 ^ 59
def prefixEnd_7680818 : Nat := 4983230072969 + 3 ^ 40 * 7680818 * 2
def baseEnd_7680818 : Nat := 3943951453705434997951567

theorem tailTrace_7680818 : CollatzResearch.WordTrace tailWord_7680818 prefixEnd_7680818 3943951453705434997951567 := by
  unfold tailWord_7680818
  simp only [CollatzResearch.WordTrace]
  refine ⟨70035611771928910030856777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186761631391810426748951405 70035611771928910030856777)
  ·
    refine ⟨52526708828946682523142583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 70035611771928910030856777 52526708828946682523142583)
    ·
      refine ⟨78790063243420023784713875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52526708828946682523142583 78790063243420023784713875)
      ·
        refine ⟨118185094865130035677070813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78790063243420023784713875 118185094865130035677070813)
        ·
          refine ⟨44319410574423763378901555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118185094865130035677070813 44319410574423763378901555)
          ·
            refine ⟨66479115861635645068352333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44319410574423763378901555 66479115861635645068352333)
            ·
              refine ⟨24929668448113366900632125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66479115861635645068352333 24929668448113366900632125)
              ·
                refine ⟨9348625668042512587737047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24929668448113366900632125 9348625668042512587737047)
                ·
                  refine ⟨14022938502063768881605571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9348625668042512587737047 14022938502063768881605571)
                  ·
                    refine ⟨21034407753095653322408357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14022938502063768881605571 21034407753095653322408357)
                    ·
                      refine ⟨3943951453705434997951567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21034407753095653322408357 3943951453705434997951567)
                      ·
                        rfl

theorem cell23_7680818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_7680818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680818 prefixEnd_7680818 := by exact prefixLift 7680818
  have htrace : WordTrace (prefixWord ++ tailWord_7680818) baseStart_7680818 baseEnd_7680818 := by
    simpa [prefixWord, tailWord_7680818, baseEnd_7680818] using wordTrace_append hprefix tailTrace_7680818
  have hstable : (prefixWord ++ tailWord_7680818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680818).length < 2 ^ (prefixWord ++ tailWord_7680818).sum := by decide
  have hdescent : baseEnd_7680818 < baseStart_7680818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680824 : List Nat := [2, 1, 2, 1, 3, 2, 12]
def baseStart_7680824 : Nat := 118140960795 + 7680824 * 2 ^ 59
def prefixEnd_7680824 : Nat := 4983230072969 + 3 ^ 40 * 7680824 * 2
def baseEnd_7680824 : Nat := 48690796723325456475019

theorem tailTrace_7680824 : CollatzResearch.WordTrace tailWord_7680824 prefixEnd_7680824 48690796723325456475019 := by
  unfold tailWord_7680824
  simp only [CollatzResearch.WordTrace]
  refine ⟨140071332962846951574072763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186761777283795935432097017 140071332962846951574072763)
  ·
    refine ⟨210106999444270427361109145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140071332962846951574072763 210106999444270427361109145)
    ·
      refine ⟨157580249583202820520831859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210106999444270427361109145 157580249583202820520831859)
      ·
        refine ⟨236370374374804230781247789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157580249583202820520831859 236370374374804230781247789)
        ·
          refine ⟨88638890390551586542967921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236370374374804230781247789 88638890390551586542967921)
          ·
            refine ⟨66479167792913689907225941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88638890390551586542967921 66479167792913689907225941)
            ·
              refine ⟨48690796723325456475019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 66479167792913689907225941 48690796723325456475019)
              ·
                rfl

theorem cell23_7680824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 12].length) (baseStart_7680824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680824 prefixEnd_7680824 := by exact prefixLift 7680824
  have htrace : WordTrace (prefixWord ++ tailWord_7680824) baseStart_7680824 baseEnd_7680824 := by
    simpa [prefixWord, tailWord_7680824, baseEnd_7680824] using wordTrace_append hprefix tailTrace_7680824
  have hstable : (prefixWord ++ tailWord_7680824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680824).length < 2 ^ (prefixWord ++ tailWord_7680824).sum := by decide
  have hdescent : baseEnd_7680824 < baseStart_7680824 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680835 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 3, 2, 2]
def baseStart_7680835 : Nat := 118140960795 + 7680835 * 2 ^ 59
def prefixEnd_7680835 : Nat := 4983230072969 + 3 ^ 40 * 7680835 * 2
def baseEnd_7680835 : Nat := 3943960182876561431438989

theorem tailTrace_7680835 : CollatzResearch.WordTrace tailWord_7680835 prefixEnd_7680835 3943960182876561431438989 := by
  unfold tailWord_7680835
  simp only [CollatzResearch.WordTrace]
  refine ⟨280143067128654052026795959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186762044752436034684530639 280143067128654052026795959)
  ·
    refine ⟨420214600692981078040193939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280143067128654052026795959 420214600692981078040193939)
    ·
      refine ⟨630321901039471617060290909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420214600692981078040193939 630321901039471617060290909)
      ·
        refine ⟨236370712889801856397609091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 630321901039471617060290909 236370712889801856397609091)
        ·
          refine ⟨354556069334702784596413637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236370712889801856397609091 354556069334702784596413637)
          ·
            refine ⟨66479263000256772111827557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 354556069334702784596413637 66479263000256772111827557)
            ·
              refine ⟨12464861812548144770967667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66479263000256772111827557 12464861812548144770967667)
              ·
                refine ⟨18697292718822217156451501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12464861812548144770967667 18697292718822217156451501)
                ·
                  refine ⟨7011484769558331433669313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18697292718822217156451501 7011484769558331433669313)
                  ·
                    refine ⟨5258613577168748575251985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7011484769558331433669313 5258613577168748575251985)
                    ·
                      refine ⟨3943960182876561431438989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5258613577168748575251985 3943960182876561431438989)
                      ·
                        rfl

theorem cell23_7680835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 3, 2, 2].length) (baseStart_7680835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680835 prefixEnd_7680835 := by exact prefixLift 7680835
  have htrace : WordTrace (prefixWord ++ tailWord_7680835) baseStart_7680835 baseEnd_7680835 := by
    simpa [prefixWord, tailWord_7680835, baseEnd_7680835] using wordTrace_append hprefix tailTrace_7680835
  have hstable : (prefixWord ++ tailWord_7680835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680835).length < 2 ^ (prefixWord ++ tailWord_7680835).sum := by decide
  have hdescent : baseEnd_7680835 < baseStart_7680835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680855 : List Nat := [1, 1, 3, 2, 4, 2, 2, 2, 1, 2, 3]
def baseStart_7680855 : Nat := 118140960795 + 7680855 * 2 ^ 59
def prefixEnd_7680855 : Nat := 4983230072969 + 3 ^ 40 * 7680855 * 2
def baseEnd_7680855 : Nat := 3943970452489651353188897

theorem tailTrace_7680855 : CollatzResearch.WordTrace tailWord_7680855 prefixEnd_7680855 3943970452489651353188897 := by
  unfold tailWord_7680855
  simp only [CollatzResearch.WordTrace]
  refine ⟨280143796588581595442524019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186762531059054396961682679 280143796588581595442524019)
  ·
    refine ⟨420215694882872393163786029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280143796588581595442524019 420215694882872393163786029)
    ·
      refine ⟨157580885581077147436419761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 420215694882872393163786029 157580885581077147436419761)
      ·
        refine ⟨118185664185807860577314821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157580885581077147436419761 118185664185807860577314821)
        ·
          refine ⟨22159812034838973858246529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 118185664185807860577314821 22159812034838973858246529)
          ·
            refine ⟨16619859026129230393684897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22159812034838973858246529 16619859026129230393684897)
            ·
              refine ⟨12464894269596922795263673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16619859026129230393684897 12464894269596922795263673)
              ·
                refine ⟨9348670702197692096447755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12464894269596922795263673 9348670702197692096447755)
                ·
                  refine ⟨14023006053296538144671633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9348670702197692096447755 14023006053296538144671633)
                  ·
                    refine ⟨10517254539972403608503725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14023006053296538144671633 10517254539972403608503725)
                    ·
                      refine ⟨3943970452489651353188897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10517254539972403608503725 3943970452489651353188897)
                      ·
                        rfl

theorem cell23_7680855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_7680855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680855 prefixEnd_7680855 := by exact prefixLift 7680855
  have htrace : WordTrace (prefixWord ++ tailWord_7680855) baseStart_7680855 baseEnd_7680855 := by
    simpa [prefixWord, tailWord_7680855, baseEnd_7680855] using wordTrace_append hprefix tailTrace_7680855
  have hstable : (prefixWord ++ tailWord_7680855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680855).length < 2 ^ (prefixWord ++ tailWord_7680855).sum := by decide
  have hdescent : baseEnd_7680855 < baseStart_7680855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680858 : List Nat := [3, 1, 1, 2, 1, 6, 2, 7]
def baseStart_7680858 : Nat := 118140960795 + 7680858 * 2 ^ 59
def prefixEnd_7680858 : Nat := 4983230072969 + 3 ^ 40 * 7680858 * 2
def baseEnd_7680858 : Nat := 146073036775244994127829

theorem tailTrace_7680858 : CollatzResearch.WordTrace tailWord_7680858 prefixEnd_7680858 146073036775244994127829 := by
  unfold tailWord_7680858
  simp only [CollatzResearch.WordTrace]
  refine ⟨70035976501892681738720807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186762604005047151303255485 70035976501892681738720807)
  ·
    refine ⟨105053964752839022608081211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70035976501892681738720807 105053964752839022608081211)
    ·
      refine ⟨157580947129258533912121817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105053964752839022608081211 157580947129258533912121817)
      ·
        refine ⟨118185710346943900434091363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 157580947129258533912121817 118185710346943900434091363)
        ·
          refine ⟨177278565520415850651137045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118185710346943900434091363 177278565520415850651137045)
          ·
            refine ⟨8309932758769492999272049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177278565520415850651137045 8309932758769492999272049)
            ·
              refine ⟨6232449569077119749454037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8309932758769492999272049 6232449569077119749454037)
              ·
                refine ⟨146073036775244994127829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6232449569077119749454037 146073036775244994127829)
                ·
                  rfl

theorem cell23_7680858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 7].length) (baseStart_7680858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680858 prefixEnd_7680858 := by exact prefixLift 7680858
  have htrace : WordTrace (prefixWord ++ tailWord_7680858) baseStart_7680858 baseEnd_7680858 := by
    simpa [prefixWord, tailWord_7680858, baseEnd_7680858] using wordTrace_append hprefix tailTrace_7680858
  have hstable : (prefixWord ++ tailWord_7680858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680858).length < 2 ^ (prefixWord ++ tailWord_7680858).sum := by decide
  have hdescent : baseEnd_7680858 < baseStart_7680858 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680885 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_7680885 : Nat := 118140960795 + 7680885 * 2 ^ 59
def prefixEnd_7680885 : Nat := 4983230072969 + 3 ^ 40 * 7680885 * 2
def baseEnd_7680885 : Nat := 3943985856909286235813759

theorem tailTrace_7680885 : CollatzResearch.WordTrace tailWord_7680885 prefixEnd_7680885 3943985856909286235813759 := by
  unfold tailWord_7680885
  simp only [CollatzResearch.WordTrace]
  refine ⟨280144890778472910566116109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186763260518981940377410739 280144890778472910566116109)
  ·
    refine ⟨105054334041927341462293541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280144890778472910566116109 105054334041927341462293541)
    ·
      refine ⟨19697687632861376524180039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 105054334041927341462293541 19697687632861376524180039)
      ·
        refine ⟨29546531449292064786270059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19697687632861376524180039 29546531449292064786270059)
        ·
          refine ⟨44319797173938097179405089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29546531449292064786270059 44319797173938097179405089)
          ·
            refine ⟨33239847880453572884553817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44319797173938097179405089 33239847880453572884553817)
            ·
              refine ⟨24929885910340179663415363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33239847880453572884553817 24929885910340179663415363)
              ·
                refine ⟨37394828865510269495123045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24929885910340179663415363 37394828865510269495123045)
                ·
                  refine ⟨7011530412283175530335571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37394828865510269495123045 7011530412283175530335571)
                  ·
                    refine ⟨10517295618424763295503357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7011530412283175530335571 10517295618424763295503357)
                    ·
                      refine ⟨3943985856909286235813759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10517295618424763295503357 3943985856909286235813759)
                      ·
                        rfl

theorem cell23_7680885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_7680885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680885 prefixEnd_7680885 := by exact prefixLift 7680885
  have htrace : WordTrace (prefixWord ++ tailWord_7680885) baseStart_7680885 baseEnd_7680885 := by
    simpa [prefixWord, tailWord_7680885, baseEnd_7680885] using wordTrace_append hprefix tailTrace_7680885
  have hstable : (prefixWord ++ tailWord_7680885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680885).length < 2 ^ (prefixWord ++ tailWord_7680885).sum := by decide
  have hdescent : baseEnd_7680885 < baseStart_7680885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680921 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 4, 2, 4]
def baseStart_7680921 : Nat := 118140960795 + 7680921 * 2 ^ 59
def prefixEnd_7680921 : Nat := 4983230072969 + 3 ^ 40 * 7680921 * 2
def baseEnd_7680921 : Nat := 3944004342212848094963593

theorem tailTrace_7680921 : CollatzResearch.WordTrace tailWord_7680921 prefixEnd_7680921 3944004342212848094963593 := by
  unfold tailWord_7680921
  simp only [CollatzResearch.WordTrace]
  refine ⟨280146203806342488714426617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186764135870894992476284411 280146203806342488714426617)
  ·
    refine ⟨210109652854756866535819963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280146203806342488714426617 210109652854756866535819963)
    ·
      refine ⟨315164479282135299803729945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210109652854756866535819963 315164479282135299803729945)
      ·
        refine ⟨236373359461601474852797459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315164479282135299803729945 236373359461601474852797459)
        ·
          refine ⟨354560039192402212279196189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236373359461601474852797459 354560039192402212279196189)
          ·
            refine ⟨132960014697150829604698571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 354560039192402212279196189 132960014697150829604698571)
            ·
              refine ⟨199440022045726244407047857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132960014697150829604698571 199440022045726244407047857)
              ·
                refine ⟨149580016534294683305285893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 199440022045726244407047857 149580016534294683305285893)
                ·
                  refine ⟨28046253100180253119741105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 149580016534294683305285893 28046253100180253119741105)
                  ·
                    refine ⟨21034689825135189839805829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28046253100180253119741105 21034689825135189839805829)
                    ·
                      refine ⟨3944004342212848094963593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21034689825135189839805829 3944004342212848094963593)
                      ·
                        rfl

theorem cell23_7680921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 4, 2, 4].length) (baseStart_7680921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680921 prefixEnd_7680921 := by exact prefixLift 7680921
  have htrace : WordTrace (prefixWord ++ tailWord_7680921) baseStart_7680921 baseEnd_7680921 := by
    simpa [prefixWord, tailWord_7680921, baseEnd_7680921] using wordTrace_append hprefix tailTrace_7680921
  have hstable : (prefixWord ++ tailWord_7680921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680921).length < 2 ^ (prefixWord ++ tailWord_7680921).sum := by decide
  have hdescent : baseEnd_7680921 < baseStart_7680921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680925 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 1, 4, 2]
def baseStart_7680925 : Nat := 118140960795 + 7680925 * 2 ^ 59
def prefixEnd_7680925 : Nat := 4983230072969 + 3 ^ 40 * 7680925 * 2
def baseEnd_7680925 : Nat := 3944006396135466079313575

theorem tailTrace_7680925 : CollatzResearch.WordTrace tailWord_7680925 prefixEnd_7680925 3944006396135466079313575 := by
  unfold tailWord_7680925
  simp only [CollatzResearch.WordTrace]
  refine ⟨280146349698327997397572229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186764233132218664931714819 280146349698327997397572229)
  ·
    refine ⟨52527440568436499512044793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280146349698327997397572229 52527440568436499512044793)
    ·
      refine ⟨39395580426327374634033595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52527440568436499512044793 39395580426327374634033595)
      ·
        refine ⟨59093370639491061951050393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39395580426327374634033595 59093370639491061951050393)
        ·
          refine ⟨44320027979618296463287795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59093370639491061951050393 44320027979618296463287795)
          ·
            refine ⟨66480041969427444694931693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44320027979618296463287795 66480041969427444694931693)
            ·
              refine ⟨24930015738535291760599385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66480041969427444694931693 24930015738535291760599385)
              ·
                refine ⟨18697511803901468820449539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24930015738535291760599385 18697511803901468820449539)
                ·
                  refine ⟨28046267705852203230674309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18697511803901468820449539 28046267705852203230674309)
                  ·
                    refine ⟨5258675194847288105751433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28046267705852203230674309 5258675194847288105751433)
                    ·
                      refine ⟨3944006396135466079313575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5258675194847288105751433 3944006396135466079313575)
                      ·
                        rfl

theorem cell23_7680925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_7680925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680925 prefixEnd_7680925 := by exact prefixLift 7680925
  have htrace : WordTrace (prefixWord ++ tailWord_7680925) baseStart_7680925 baseEnd_7680925 := by
    simpa [prefixWord, tailWord_7680925, baseEnd_7680925] using wordTrace_append hprefix tailTrace_7680925
  have hstable : (prefixWord ++ tailWord_7680925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680925).length < 2 ^ (prefixWord ++ tailWord_7680925).sum := by decide
  have hdescent : baseEnd_7680925 < baseStart_7680925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680929 : List Nat := [1, 2, 3, 4, 1, 2, 3, 1, 1, 3, 2]
def baseStart_7680929 : Nat := 118140960795 + 7680929 * 2 ^ 59
def prefixEnd_7680929 : Nat := 4983230072969 + 3 ^ 40 * 7680929 * 2
def baseEnd_7680929 : Nat := 3944008450058084063663557

theorem tailTrace_7680929 : CollatzResearch.WordTrace tailWord_7680929 prefixEnd_7680929 3944008450058084063663557 := by
  unfold tailWord_7680929
  simp only [CollatzResearch.WordTrace]
  refine ⟨280146495590313506080717841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186764330393542337387145227 280146495590313506080717841)
  ·
    refine ⟨210109871692735129560538381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280146495590313506080717841 210109871692735129560538381)
    ·
      refine ⟨78791201884775673585201893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 210109871692735129560538381 78791201884775673585201893)
      ·
        refine ⟨14773350353395438797225355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 78791201884775673585201893 14773350353395438797225355)
        ·
          refine ⟨22160025530093158195838033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14773350353395438797225355 22160025530093158195838033)
          ·
            refine ⟨16620019147569868646878525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22160025530093158195838033 16620019147569868646878525)
            ·
              refine ⟨6232507180338700742579447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16620019147569868646878525 6232507180338700742579447)
              ·
                refine ⟨9348760770508051113869171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6232507180338700742579447 9348760770508051113869171)
                ·
                  refine ⟨14023141155762076670803757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9348760770508051113869171 14023141155762076670803757)
                  ·
                    refine ⟨5258677933410778751551409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14023141155762076670803757 5258677933410778751551409)
                    ·
                      refine ⟨3944008450058084063663557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5258677933410778751551409 3944008450058084063663557)
                      ·
                        rfl

theorem cell23_7680929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_7680929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680929 prefixEnd_7680929 := by exact prefixLift 7680929
  have htrace : WordTrace (prefixWord ++ tailWord_7680929) baseStart_7680929 baseEnd_7680929 := by
    simpa [prefixWord, tailWord_7680929, baseEnd_7680929] using wordTrace_append hprefix tailTrace_7680929
  have hstable : (prefixWord ++ tailWord_7680929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680929).length < 2 ^ (prefixWord ++ tailWord_7680929).sum := by decide
  have hdescent : baseEnd_7680929 < baseStart_7680929 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7680982 : List Nat := [5, 2, 1, 1, 2, 1, 1, 5, 5]
def baseStart_7680982 : Nat := 118140960795 + 7680982 * 2 ^ 59
def prefixEnd_7680982 : Nat := 4983230072969 + 3 ^ 40 * 7680982 * 2
def baseEnd_7680982 : Nat := 438226184948085817366757

theorem tailTrace_7680982 : CollatzResearch.WordTrace tailWord_7680982 prefixEnd_7680982 438226184948085817366757 := by
  unfold tailWord_7680982
  simp only [CollatzResearch.WordTrace]
  refine ⟨17509276791195093508274825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186765619106080997421598133 17509276791195093508274825)
  ·
    refine ⟨13131957593396320131206119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17509276791195093508274825 13131957593396320131206119)
    ·
      refine ⟨19697936390094480196809179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13131957593396320131206119 19697936390094480196809179)
      ·
        refine ⟨29546904585141720295213769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19697936390094480196809179 29546904585141720295213769)
        ·
          refine ⟨22160178438856290221410327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29546904585141720295213769 22160178438856290221410327)
          ·
            refine ⟨33240267658284435332115491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22160178438856290221410327 33240267658284435332115491)
            ·
              refine ⟨49860401487426652998173237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33240267658284435332115491 49860401487426652998173237)
              ·
                refine ⟨4674412639446248718578741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49860401487426652998173237 4674412639446248718578741)
                ·
                  refine ⟨438226184948085817366757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4674412639446248718578741 438226184948085817366757)
                  ·
                    rfl

theorem cell23_7680982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_7680982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7680982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7680982 prefixEnd_7680982 := by exact prefixLift 7680982
  have htrace : WordTrace (prefixWord ++ tailWord_7680982) baseStart_7680982 baseEnd_7680982 := by
    simpa [prefixWord, tailWord_7680982, baseEnd_7680982] using wordTrace_append hprefix tailTrace_7680982
  have hstable : (prefixWord ++ tailWord_7680982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7680982).length < 2 ^ (prefixWord ++ tailWord_7680982).sum := by decide
  have hdescent : baseEnd_7680982 < baseStart_7680982 := by decide
  rcases family_descends (prefixWord ++ tailWord_7680982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681025 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 3, 4]
def baseStart_7681025 : Nat := 118140960795 + 7681025 * 2 ^ 59
def prefixEnd_7681025 : Nat := 4983230072969 + 3 ^ 40 * 7681025 * 2
def baseEnd_7681025 : Nat := 1314685914733638562687705

theorem tailTrace_7681025 : CollatzResearch.WordTrace tailWord_7681025 prefixEnd_7681025 1314685914733638562687705 := by
  unfold tailWord_7681025
  simp only [CollatzResearch.WordTrace]
  refine ⟨280149996997965714476212529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186766664665310476317475019 280149996997965714476212529)
  ·
    refine ⟨210112497748474285857159397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280149996997965714476212529 210112497748474285857159397)
    ·
      refine ⟨39396093327838928598217387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 210112497748474285857159397 39396093327838928598217387)
      ·
        refine ⟨59094139991758392897326081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39396093327838928598217387 59094139991758392897326081)
        ·
          refine ⟨44320604993818794672994561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59094139991758392897326081 44320604993818794672994561)
          ·
            refine ⟨33240453745364096004745921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44320604993818794672994561 33240453745364096004745921)
            ·
              refine ⟨24930340309023072003559441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33240453745364096004745921 24930340309023072003559441)
              ·
                refine ⟨18697755231767304002669581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24930340309023072003559441 18697755231767304002669581)
                ·
                  refine ⟨7011658211912739001001093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18697755231767304002669581 7011658211912739001001093)
                  ·
                    refine ⟨1314685914733638562687705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7011658211912739001001093 1314685914733638562687705)
                    ·
                      rfl

theorem cell23_7681025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_7681025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681025 prefixEnd_7681025 := by exact prefixLift 7681025
  have htrace : WordTrace (prefixWord ++ tailWord_7681025) baseStart_7681025 baseEnd_7681025 := by
    simpa [prefixWord, tailWord_7681025, baseEnd_7681025] using wordTrace_append hprefix tailTrace_7681025
  have hstable : (prefixWord ++ tailWord_7681025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681025).length < 2 ^ (prefixWord ++ tailWord_7681025).sum := by decide
  have hdescent : baseEnd_7681025 < baseStart_7681025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681038 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 8]
def baseStart_7681038 : Nat := 118140960795 + 7681038 * 2 ^ 59
def prefixEnd_7681038 : Nat := 4983230072969 + 3 ^ 40 * 7681038 * 2
def baseEnd_7681038 : Nat := 438229379938824904133395

theorem tailTrace_7681038 : CollatzResearch.WordTrace tailWord_7681038 prefixEnd_7681038 438229379938824904133395 := by
  unfold tailWord_7681038
  simp only [CollatzResearch.WordTrace]
  refine ⟨35018808893364827212054471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186766980764612411797623845 35018808893364827212054471)
  ·
    refine ⟨52528213340047240818081707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35018808893364827212054471 52528213340047240818081707)
    ·
      refine ⟨78792320010070861227122561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52528213340047240818081707 78792320010070861227122561)
      ·
        refine ⟨59094240007553145920341921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 78792320010070861227122561 59094240007553145920341921)
        ·
          refine ⟨44320680005664859440256441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59094240007553145920341921 44320680005664859440256441)
          ·
            refine ⟨33240510004248644580192331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44320680005664859440256441 33240510004248644580192331)
            ·
              refine ⟨49860765006372966870288497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33240510004248644580192331 49860765006372966870288497)
              ·
                refine ⟨37395573754779725152716373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49860765006372966870288497 37395573754779725152716373)
                ·
                  refine ⟨438229379938824904133395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37395573754779725152716373 438229379938824904133395)
                  ·
                    rfl

theorem cell23_7681038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_7681038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681038 prefixEnd_7681038 := by exact prefixLift 7681038
  have htrace : WordTrace (prefixWord ++ tailWord_7681038) baseStart_7681038 baseEnd_7681038 := by
    simpa [prefixWord, tailWord_7681038, baseEnd_7681038] using wordTrace_append hprefix tailTrace_7681038
  have hstable : (prefixWord ++ tailWord_7681038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681038).length < 2 ^ (prefixWord ++ tailWord_7681038).sum := by decide
  have hdescent : baseEnd_7681038 < baseStart_7681038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681051 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 1, 11]
def baseStart_7681051 : Nat := 118140960795 + 7681051 * 2 ^ 59
def prefixEnd_7681051 : Nat := 4983230072969 + 3 ^ 40 * 7681051 * 2
def baseEnd_7681051 : Nat := 1314690364899310862112665

theorem tailTrace_7681051 : CollatzResearch.WordTrace tailWord_7681051 prefixEnd_7681051 1314690364899310862112665 := by
  unfold tailWord_7681051
  simp only [CollatzResearch.WordTrace]
  refine ⟨280150945295871520916659007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186767296863914347277772671 280150945295871520916659007)
  ·
    refine ⟨420226417943807281374988511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280150945295871520916659007 420226417943807281374988511)
    ·
      refine ⟨630339626915710922062482767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420226417943807281374988511 630339626915710922062482767)
      ·
        refine ⟨945509440373566383093724151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630339626915710922062482767 945509440373566383093724151)
        ·
          refine ⟨1418264160560349574640586227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945509440373566383093724151 1418264160560349574640586227)
          ·
            refine ⟨2127396240840524361960879341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1418264160560349574640586227 2127396240840524361960879341)
            ·
              refine ⟨797773590315196635735329753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2127396240840524361960879341 797773590315196635735329753)
              ·
                refine ⟨598330192736397476801497315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 797773590315196635735329753 598330192736397476801497315)
                ·
                  refine ⟨897495289104596215202245973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 598330192736397476801497315 897495289104596215202245973)
                  ·
                    refine ⟨1314690364899310862112665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 897495289104596215202245973 1314690364899310862112665)
                    ·
                      rfl

theorem cell23_7681051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 11].length) (baseStart_7681051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681051 prefixEnd_7681051 := by exact prefixLift 7681051
  have htrace : WordTrace (prefixWord ++ tailWord_7681051) baseStart_7681051 baseEnd_7681051 := by
    simpa [prefixWord, tailWord_7681051, baseEnd_7681051] using wordTrace_append hprefix tailTrace_7681051
  have hstable : (prefixWord ++ tailWord_7681051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681051).length < 2 ^ (prefixWord ++ tailWord_7681051).sum := by decide
  have hdescent : baseEnd_7681051 < baseStart_7681051 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681052 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 2, 2, 3]
def baseStart_7681052 : Nat := 118140960795 + 7681052 * 2 ^ 59
def prefixEnd_7681052 : Nat := 4983230072969 + 3 ^ 40 * 7681052 * 2
def baseEnd_7681052 : Nat := 3944071608178587082425491

theorem tailTrace_7681052 : CollatzResearch.WordTrace tailWord_7681052 prefixEnd_7681052 3944071608178587082425491 := by
  unfold tailWord_7681052
  simp only [CollatzResearch.WordTrace]
  refine ⟨140075490884433949043722705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186767321179245265391630273 140075490884433949043722705)
  ·
    refine ⟨105056618163325461782792029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140075490884433949043722705 105056618163325461782792029)
    ·
      refine ⟨39396231811247048168547011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105056618163325461782792029 39396231811247048168547011)
      ·
        refine ⟨59094347716870572252820517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39396231811247048168547011 59094347716870572252820517)
        ·
          refine ⟨11080190196913232297403847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 59094347716870572252820517 11080190196913232297403847)
          ·
            refine ⟨16620285295369848446105771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11080190196913232297403847 16620285295369848446105771)
            ·
              refine ⟨24930427943054772669158657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16620285295369848446105771 24930427943054772669158657)
              ·
                refine ⟨18697820957291079501868993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24930427943054772669158657 18697820957291079501868993)
                ·
                  refine ⟨14023365717968309626401745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18697820957291079501868993 14023365717968309626401745)
                  ·
                    refine ⟨10517524288476232219801309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14023365717968309626401745 10517524288476232219801309)
                    ·
                      refine ⟨3944071608178587082425491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10517524288476232219801309 3944071608178587082425491)
                      ·
                        rfl

theorem cell23_7681052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 2, 2, 3].length) (baseStart_7681052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681052 prefixEnd_7681052 := by exact prefixLift 7681052
  have htrace : WordTrace (prefixWord ++ tailWord_7681052) baseStart_7681052 baseEnd_7681052 := by
    simpa [prefixWord, tailWord_7681052, baseEnd_7681052] using wordTrace_append hprefix tailTrace_7681052
  have hstable : (prefixWord ++ tailWord_7681052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681052).length < 2 ^ (prefixWord ++ tailWord_7681052).sum := by decide
  have hdescent : baseEnd_7681052 < baseStart_7681052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681059 : List Nat := [1, 1, 1, 4, 3, 3, 3, 2, 1, 4]
def baseStart_7681059 : Nat := 118140960795 + 7681059 * 2 ^ 59
def prefixEnd_7681059 : Nat := 4983230072969 + 3 ^ 40 * 7681059 * 2
def baseEnd_7681059 : Nat := 1314691734181056185012653

theorem tailTrace_7681059 : CollatzResearch.WordTrace tailWord_7681059 prefixEnd_7681059 1314691734181056185012653 := by
  unfold tailWord_7681059
  simp only [CollatzResearch.WordTrace]
  refine ⟨280151237079842538282950231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186767491386561692188633487 280151237079842538282950231)
  ·
    refine ⟨420226855619763807424425347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280151237079842538282950231 420226855619763807424425347)
    ·
      refine ⟨630340283429645711136638021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420226855619763807424425347 630340283429645711136638021)
      ·
        refine ⟨118188803143058570838119629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 630340283429645711136638021 118188803143058570838119629)
        ·
          refine ⟨44320801178646964064294861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 118188803143058570838119629 44320801178646964064294861)
          ·
            refine ⟨16620300441992611524110573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44320801178646964064294861 16620300441992611524110573)
            ·
              refine ⟨6232612665747229321541465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16620300441992611524110573 6232612665747229321541465)
              ·
                refine ⟨4674459499310421991156099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6232612665747229321541465 4674459499310421991156099)
                ·
                  refine ⟨7011689248965632986734149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4674459499310421991156099 7011689248965632986734149)
                  ·
                    refine ⟨1314691734181056185012653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7011689248965632986734149 1314691734181056185012653)
                    ·
                      rfl

theorem cell23_7681059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 1, 4].length) (baseStart_7681059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681059 prefixEnd_7681059 := by exact prefixLift 7681059
  have htrace : WordTrace (prefixWord ++ tailWord_7681059) baseStart_7681059 baseEnd_7681059 := by
    simpa [prefixWord, tailWord_7681059, baseEnd_7681059] using wordTrace_append hprefix tailTrace_7681059
  have hstable : (prefixWord ++ tailWord_7681059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681059).length < 2 ^ (prefixWord ++ tailWord_7681059).sum := by decide
  have hdescent : baseEnd_7681059 < baseStart_7681059 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681068 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 3, 5]
def baseStart_7681068 : Nat := 118140960795 + 7681068 * 2 ^ 59
def prefixEnd_7681068 : Nat := 4983230072969 + 3 ^ 40 * 7681068 * 2
def baseEnd_7681068 : Nat := 1314693274623019673275139

theorem tailTrace_7681068 : CollatzResearch.WordTrace tailWord_7681068 prefixEnd_7681068 1314693274623019673275139 := by
  unfold tailWord_7681068
  simp only [CollatzResearch.WordTrace]
  refine ⟨140075782668404966410013929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186767710224539955213351905 140075782668404966410013929)
  ·
    refine ⟨105056837001303724807510447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140075782668404966410013929 105056837001303724807510447)
    ·
      refine ⟨157585255501955587211265671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105056837001303724807510447 157585255501955587211265671)
      ·
        refine ⟨236377883252933380816898507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157585255501955587211265671 236377883252933380816898507)
        ·
          refine ⟨354566824879400071225347761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 236377883252933380816898507 354566824879400071225347761)
          ·
            refine ⟨265925118659550053419010821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 354566824879400071225347761 265925118659550053419010821)
            ·
              refine ⟨49860959748665635016064529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 265925118659550053419010821 49860959748665635016064529)
              ·
                refine ⟨37395719811499226262048397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49860959748665635016064529 37395719811499226262048397)
                ·
                  refine ⟨14023394929312209848268149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37395719811499226262048397 14023394929312209848268149)
                  ·
                    refine ⟨1314693274623019673275139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14023394929312209848268149 1314693274623019673275139)
                    ·
                      rfl

theorem cell23_7681068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 5].length) (baseStart_7681068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681068 prefixEnd_7681068 := by exact prefixLift 7681068
  have htrace : WordTrace (prefixWord ++ tailWord_7681068) baseStart_7681068 baseEnd_7681068 := by
    simpa [prefixWord, tailWord_7681068, baseEnd_7681068] using wordTrace_append hprefix tailTrace_7681068
  have hstable : (prefixWord ++ tailWord_7681068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681068).length < 2 ^ (prefixWord ++ tailWord_7681068).sum := by decide
  have hdescent : baseEnd_7681068 < baseStart_7681068 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681075 : List Nat := [1, 1, 1, 2, 4, 1, 1, 1, 6, 3, 2]
def baseStart_7681075 : Nat := 118140960795 + 7681075 * 2 ^ 59
def prefixEnd_7681075 : Nat := 4983230072969 + 3 ^ 40 * 7681075 * 2
def baseEnd_7681075 : Nat := 3944083418233640492437885

theorem tailTrace_7681075 : CollatzResearch.WordTrace tailWord_7681075 prefixEnd_7681075 3944083418233640492437885 := by
  unfold tailWord_7681075
  simp only [CollatzResearch.WordTrace]
  refine ⟨280151820647784573015532679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186767880431856382010355119 280151820647784573015532679)
  ·
    refine ⟨420227730971676859523299019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280151820647784573015532679 420227730971676859523299019)
    ·
      refine ⟨630341596457515289284948529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420227730971676859523299019 630341596457515289284948529)
      ·
        refine ⟨472756197343136466963711397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630341596457515289284948529 472756197343136466963711397)
        ·
          refine ⟨88641787001838087555695887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 472756197343136466963711397 88641787001838087555695887)
          ·
            refine ⟨132962680502757131333543831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88641787001838087555695887 132962680502757131333543831)
            ·
              refine ⟨199444020754135697000315747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 132962680502757131333543831 199444020754135697000315747)
              ·
                refine ⟨299166031131203545500473621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199444020754135697000315747 299166031131203545500473621)
                ·
                  refine ⟨14023407709275166195334701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 299166031131203545500473621 14023407709275166195334701)
                  ·
                    refine ⟨5258777890978187323250513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14023407709275166195334701 5258777890978187323250513)
                    ·
                      refine ⟨3944083418233640492437885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5258777890978187323250513 3944083418233640492437885)
                      ·
                        rfl

theorem cell23_7681075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 1, 6, 3, 2].length) (baseStart_7681075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681075 prefixEnd_7681075 := by exact prefixLift 7681075
  have htrace : WordTrace (prefixWord ++ tailWord_7681075) baseStart_7681075 baseEnd_7681075 := by
    simpa [prefixWord, tailWord_7681075, baseEnd_7681075] using wordTrace_append hprefix tailTrace_7681075
  have hstable : (prefixWord ++ tailWord_7681075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681075).length < 2 ^ (prefixWord ++ tailWord_7681075).sum := by decide
  have hdescent : baseEnd_7681075 < baseStart_7681075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681085 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 3, 5]
def baseStart_7681085 : Nat := 118140960795 + 7681085 * 2 ^ 59
def prefixEnd_7681085 : Nat := 4983230072969 + 3 ^ 40 * 7681085 * 2
def baseEnd_7681085 : Nat := 1314696184346728484437613

theorem tailTrace_7681085 : CollatzResearch.WordTrace tailWord_7681085 prefixEnd_7681085 1314696184346728484437613 := by
  unfold tailWord_7681085
  simp only [CollatzResearch.WordTrace]
  refine ⟨280152185377748344723396709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186768123585165563148931139 280152185377748344723396709)
  ·
    refine ⟨52528534758327814635636883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280152185377748344723396709 52528534758327814635636883)
    ·
      refine ⟨78792802137491721953455325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52528534758327814635636883 78792802137491721953455325)
      ·
        refine ⟨29547300801559395732545747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 78792802137491721953455325 29547300801559395732545747)
        ·
          refine ⟨44320951202339093598818621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29547300801559395732545747 44320951202339093598818621)
          ·
            refine ⟨16620356700877160099556983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44320951202339093598818621 16620356700877160099556983)
            ·
              refine ⟨24930535051315740149335475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16620356700877160099556983 24930535051315740149335475)
              ·
                refine ⟨37395802576973610224003213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24930535051315740149335475 37395802576973610224003213)
                ·
                  refine ⟨14023425966365103834001205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37395802576973610224003213 14023425966365103834001205)
                  ·
                    refine ⟨1314696184346728484437613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14023425966365103834001205 1314696184346728484437613)
                    ·
                      rfl

theorem cell23_7681085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 5].length) (baseStart_7681085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681085 prefixEnd_7681085 := by exact prefixLift 7681085
  have htrace : WordTrace (prefixWord ++ tailWord_7681085) baseStart_7681085 baseEnd_7681085 := by
    simpa [prefixWord, tailWord_7681085, baseEnd_7681085] using wordTrace_append hprefix tailTrace_7681085
  have hstable : (prefixWord ++ tailWord_7681085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681085).length < 2 ^ (prefixWord ++ tailWord_7681085).sum := by decide
  have hdescent : baseEnd_7681085 < baseStart_7681085 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681098 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 3, 6]
def baseStart_7681098 : Nat := 118140960795 + 7681098 * 2 ^ 59
def prefixEnd_7681098 : Nat := 4983230072969 + 3 ^ 40 * 7681098 * 2
def baseEnd_7681098 : Nat := 1314698409429564634150093

theorem tailTrace_7681098 : CollatzResearch.WordTrace tailWord_7681098 prefixEnd_7681098 1314698409429564634150093 := by
  unfold tailWord_7681098
  simp only [CollatzResearch.WordTrace]
  refine ⟨70038164881675311985904987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186768439684467498629079965 70038164881675311985904987)
  ·
    refine ⟨105057247322512967978857481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 70038164881675311985904987 105057247322512967978857481)
    ·
      refine ⟨78792935491884725984143111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 105057247322512967978857481 78792935491884725984143111)
      ·
        refine ⟨118189403237827088976214667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78792935491884725984143111 118189403237827088976214667)
        ·
          refine ⟨177284104856740633464322001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118189403237827088976214667 177284104856740633464322001)
          ·
            refine ⟨132963078642555475098241501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177284104856740633464322001 132963078642555475098241501)
            ·
              refine ⟨49861154490958303161840563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 132963078642555475098241501 49861154490958303161840563)
              ·
                refine ⟨74791731736437454742760845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 49861154490958303161840563 74791731736437454742760845)
                ·
                  refine ⟨28046899401164045528535317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 74791731736437454742760845 28046899401164045528535317)
                  ·
                    refine ⟨1314698409429564634150093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28046899401164045528535317 1314698409429564634150093)
                    ·
                      rfl

theorem cell23_7681098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 3, 6].length) (baseStart_7681098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681098 prefixEnd_7681098 := by exact prefixLift 7681098
  have htrace : WordTrace (prefixWord ++ tailWord_7681098) baseStart_7681098 baseEnd_7681098 := by
    simpa [prefixWord, tailWord_7681098, baseEnd_7681098] using wordTrace_append hprefix tailTrace_7681098
  have hstable : (prefixWord ++ tailWord_7681098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681098).length < 2 ^ (prefixWord ++ tailWord_7681098).sum := by decide
  have hdescent : baseEnd_7681098 < baseStart_7681098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681102 : List Nat := [4, 1, 1, 1, 1, 3, 5, 1, 1, 5]
def baseStart_7681102 : Nat := 118140960795 + 7681102 * 2 ^ 59
def prefixEnd_7681102 : Nat := 4983230072969 + 3 ^ 40 * 7681102 * 2
def baseEnd_7681102 : Nat := 1314699094070437295600087

theorem tailTrace_7681102 : CollatzResearch.WordTrace tailWord_7681102 prefixEnd_7681102 1314699094070437295600087 := by
  unfold tailWord_7681102
  simp only [CollatzResearch.WordTrace]
  refine ⟨35019100677335844578345695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186768536945791171084510373 35019100677335844578345695)
  ·
    refine ⟨52528651016003766867518543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35019100677335844578345695 52528651016003766867518543)
    ·
      refine ⟨78792976524005650301277815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52528651016003766867518543 78792976524005650301277815)
      ·
        refine ⟨118189464786008475451916723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78792976524005650301277815 118189464786008475451916723)
        ·
          refine ⟨177284197179012713177875085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118189464786008475451916723 177284197179012713177875085)
          ·
            refine ⟨66481573942129767441703157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177284197179012713177875085 66481573942129767441703157)
            ·
              refine ⟨6232647557074665697659671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66481573942129767441703157 6232647557074665697659671)
              ·
                refine ⟨9348971335611998546489507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6232647557074665697659671 9348971335611998546489507)
                ·
                  refine ⟨14023457003417997819734261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9348971335611998546489507 14023457003417997819734261)
                  ·
                    refine ⟨1314699094070437295600087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14023457003417997819734261 1314699094070437295600087)
                    ·
                      rfl

theorem cell23_7681102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_7681102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681102 prefixEnd_7681102 := by exact prefixLift 7681102
  have htrace : WordTrace (prefixWord ++ tailWord_7681102) baseStart_7681102 baseEnd_7681102 := by
    simpa [prefixWord, tailWord_7681102, baseEnd_7681102] using wordTrace_append hprefix tailTrace_7681102
  have hstable : (prefixWord ++ tailWord_7681102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681102).length < 2 ^ (prefixWord ++ tailWord_7681102).sum := by decide
  have hdescent : baseEnd_7681102 < baseStart_7681102 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681105 : List Nat := [1, 2, 2, 1, 3, 1, 2, 5, 1, 1, 4]
def baseStart_7681105 : Nat := 118140960795 + 7681105 * 2 ^ 59
def prefixEnd_7681105 : Nat := 4983230072969 + 3 ^ 40 * 7681105 * 2
def baseEnd_7681105 : Nat := 3944098822653275375062747

theorem tailTrace_7681105 : CollatzResearch.WordTrace tailWord_7681105 prefixEnd_7681105 3944098822653275375062747 := by
  unfold tailWord_7681105
  simp only [CollatzResearch.WordTrace]
  refine ⟨280152914837675888139124769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186768609891783925426083179 280152914837675888139124769)
  ·
    refine ⟨210114686128256916104343577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280152914837675888139124769 210114686128256916104343577)
    ·
      refine ⟨157586014596192687078257683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 210114686128256916104343577 157586014596192687078257683)
      ·
        refine ⟨236379021894289030617386525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 157586014596192687078257683 236379021894289030617386525)
        ·
          refine ⟨88642133210358386481519947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236379021894289030617386525 88642133210358386481519947)
          ·
            refine ⟨132963199815537579722279921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88642133210358386481519947 132963199815537579722279921)
            ·
              refine ⟨99722399861653184791709941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 132963199815537579722279921 99722399861653184791709941)
              ·
                refine ⟨9348974987029986074222807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 99722399861653184791709941 9348974987029986074222807)
                ·
                  refine ⟨14023462480544979111334211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9348974987029986074222807 14023462480544979111334211)
                  ·
                    refine ⟨21035193720817468667001317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14023462480544979111334211 21035193720817468667001317)
                    ·
                      refine ⟨3944098822653275375062747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21035193720817468667001317 3944098822653275375062747)
                      ·
                        rfl

theorem cell23_7681105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 5, 1, 1, 4].length) (baseStart_7681105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681105 prefixEnd_7681105 := by exact prefixLift 7681105
  have htrace : WordTrace (prefixWord ++ tailWord_7681105) baseStart_7681105 baseEnd_7681105 := by
    simpa [prefixWord, tailWord_7681105, baseEnd_7681105] using wordTrace_append hprefix tailTrace_7681105
  have hstable : (prefixWord ++ tailWord_7681105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681105).length < 2 ^ (prefixWord ++ tailWord_7681105).sum := by decide
  have hdescent : baseEnd_7681105 < baseStart_7681105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681110 : List Nat := [5, 2, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_7681110 : Nat := 118140960795 + 7681110 * 2 ^ 59
def prefixEnd_7681110 : Nat := 4983230072969 + 3 ^ 40 * 7681110 * 2
def baseEnd_7681110 : Nat := 1314700463352182618500075

theorem tailTrace_7681110 : CollatzResearch.WordTrace tailWord_7681110 prefixEnd_7681110 1314700463352182618500075 := by
  unfold tailWord_7681110
  simp only [CollatzResearch.WordTrace]
  refine ⟨17509568575166110874566049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186768731468438515995371189 17509568575166110874566049)
  ·
    refine ⟨13132176431374583155924537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17509568575166110874566049 13132176431374583155924537)
    ·
      refine ⟨9849132323530937366943403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13132176431374583155924537 9849132323530937366943403)
      ·
        refine ⟨14773698485296406050415105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9849132323530937366943403 14773698485296406050415105)
        ·
          refine ⟨11080273863972304537811329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14773698485296406050415105 11080273863972304537811329)
          ·
            refine ⟨8310205397979228403358497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11080273863972304537811329 8310205397979228403358497)
            ·
              refine ⟨6232654048484421302518873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8310205397979228403358497 6232654048484421302518873)
              ·
                refine ⟨4674490536363315976889155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6232654048484421302518873 4674490536363315976889155)
                ·
                  refine ⟨7011735804544973965333733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4674490536363315976889155 7011735804544973965333733)
                  ·
                    refine ⟨1314700463352182618500075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7011735804544973965333733 1314700463352182618500075)
                    ·
                      rfl

theorem cell23_7681110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_7681110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681110 prefixEnd_7681110 := by exact prefixLift 7681110
  have htrace : WordTrace (prefixWord ++ tailWord_7681110) baseStart_7681110 baseEnd_7681110 := by
    simpa [prefixWord, tailWord_7681110, baseEnd_7681110] using wordTrace_append hprefix tailTrace_7681110
  have hstable : (prefixWord ++ tailWord_7681110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681110).length < 2 ^ (prefixWord ++ tailWord_7681110).sum := by decide
  have hdescent : baseEnd_7681110 < baseStart_7681110 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681122 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_7681122 : Nat := 118140960795 + 7681122 * 2 ^ 59
def prefixEnd_7681122 : Nat := 4983230072969 + 3 ^ 40 * 7681122 * 2
def baseEnd_7681122 : Nat := 3944107551824401808550169

theorem tailTrace_7681122 : CollatzResearch.WordTrace tailWord_7681122 prefixEnd_7681122 3944107551824401808550169 := by
  unfold tailWord_7681122
  simp only [CollatzResearch.WordTrace]
  refine ⟨70038383719653575010623405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186769023252409533361662413 70038383719653575010623405)
  ·
    refine ⟨26264393894870090628983777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70038383719653575010623405 26264393894870090628983777)
    ·
      refine ⟨19698295421152567971737833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26264393894870090628983777 19698295421152567971737833)
      ·
        refine ⟨14773721565864425978803375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19698295421152567971737833 14773721565864425978803375)
        ·
          refine ⟨22160582348796638968205063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14773721565864425978803375 22160582348796638968205063)
          ·
            refine ⟨33240873523194958452307595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22160582348796638968205063 33240873523194958452307595)
            ·
              refine ⟨49861310284792437678461393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33240873523194958452307595 49861310284792437678461393)
              ·
                refine ⟨37395982713594328258846045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49861310284792437678461393 37395982713594328258846045)
                ·
                  refine ⟨14023493517597873097067267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37395982713594328258846045 14023493517597873097067267)
                  ·
                    refine ⟨21035240276396809645600901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14023493517597873097067267 21035240276396809645600901)
                    ·
                      refine ⟨3944107551824401808550169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21035240276396809645600901 3944107551824401808550169)
                      ·
                        rfl

theorem cell23_7681122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_7681122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681122 prefixEnd_7681122 := by exact prefixLift 7681122
  have htrace : WordTrace (prefixWord ++ tailWord_7681122) baseStart_7681122 baseEnd_7681122 := by
    simpa [prefixWord, tailWord_7681122, baseEnd_7681122] using wordTrace_append hprefix tailTrace_7681122
  have hstable : (prefixWord ++ tailWord_7681122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681122).length < 2 ^ (prefixWord ++ tailWord_7681122).sum := by decide
  have hdescent : baseEnd_7681122 < baseStart_7681122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681125 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 5, 2, 3]
def baseStart_7681125 : Nat := 118140960795 + 7681125 * 2 ^ 59
def prefixEnd_7681125 : Nat := 4983230072969 + 3 ^ 40 * 7681125 * 2
def baseEnd_7681125 : Nat := 3944109092266365296812655

theorem tailTrace_7681125 : CollatzResearch.WordTrace tailWord_7681125 prefixEnd_7681125 3944109092266365296812655 := by
  unfold tailWord_7681125
  simp only [CollatzResearch.WordTrace]
  refine ⟨280153644297603431554852829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186769096198402287703235219 280153644297603431554852829)
  ·
    refine ⟨105057616611601286833069811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280153644297603431554852829 105057616611601286833069811)
    ·
      refine ⟨157586424917401930249604717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105057616611601286833069811 157586424917401930249604717)
      ·
        refine ⟨59094909344025723843601769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 157586424917401930249604717 59094909344025723843601769)
        ·
          refine ⟨44321182008019292882701327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59094909344025723843601769 44321182008019292882701327)
          ·
            refine ⟨66481773012028939324051991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44321182008019292882701327 66481773012028939324051991)
            ·
              refine ⟨99722659518043408986077987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66481773012028939324051991 99722659518043408986077987)
              ·
                refine ⟨149583989277065113479116981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99722659518043408986077987 149583989277065113479116981)
                ·
                  refine ⟨14023498994724854388667217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 149583989277065113479116981 14023498994724854388667217)
                  ·
                    refine ⟨10517624246043640791500413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14023498994724854388667217 10517624246043640791500413)
                    ·
                      refine ⟨3944109092266365296812655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10517624246043640791500413 3944109092266365296812655)
                      ·
                        rfl

theorem cell23_7681125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_7681125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681125 prefixEnd_7681125 := by exact prefixLift 7681125
  have htrace : WordTrace (prefixWord ++ tailWord_7681125) baseStart_7681125 baseEnd_7681125 := by
    simpa [prefixWord, tailWord_7681125, baseEnd_7681125] using wordTrace_append hprefix tailTrace_7681125
  have hstable : (prefixWord ++ tailWord_7681125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681125).length < 2 ^ (prefixWord ++ tailWord_7681125).sum := by decide
  have hdescent : baseEnd_7681125 < baseStart_7681125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681135 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 4]
def baseStart_7681135 : Nat := 118140960795 + 7681135 * 2 ^ 59
def prefixEnd_7681135 : Nat := 4983230072969 + 3 ^ 40 * 7681135 * 2
def baseEnd_7681135 : Nat := 3944114227072910257687609

theorem tailTrace_7681135 : CollatzResearch.WordTrace tailWord_7681135 prefixEnd_7681135 3944114227072910257687609 := by
  unfold tailWord_7681135
  simp only [CollatzResearch.WordTrace]
  refine ⟨280154009027567203262716859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186769339351711468841811239 280154009027567203262716859)
  ·
    refine ⟨420231013541350804894075289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280154009027567203262716859 420231013541350804894075289)
    ·
      refine ⟨315173260156013103670556467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420231013541350804894075289 315173260156013103670556467)
      ·
        refine ⟨472759890234019655505834701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315173260156013103670556467 472759890234019655505834701)
        ·
          refine ⟨177284958837757370814688013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472759890234019655505834701 177284958837757370814688013)
          ·
            refine ⟨66481859564159014055508005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177284958837757370814688013 66481859564159014055508005)
            ·
              refine ⟨12465348668279815135407751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 66481859564159014055508005 12465348668279815135407751)
              ·
                refine ⟨18698023002419722703111627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12465348668279815135407751 18698023002419722703111627)
                ·
                  refine ⟨28047034503629584054667441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18698023002419722703111627 28047034503629584054667441)
                  ·
                    refine ⟨21035275877722188041000581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28047034503629584054667441 21035275877722188041000581)
                    ·
                      refine ⟨3944114227072910257687609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21035275877722188041000581 3944114227072910257687609)
                      ·
                        rfl

theorem cell23_7681135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 4].length) (baseStart_7681135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681135 prefixEnd_7681135 := by exact prefixLift 7681135
  have htrace : WordTrace (prefixWord ++ tailWord_7681135) baseStart_7681135 baseEnd_7681135 := by
    simpa [prefixWord, tailWord_7681135, baseEnd_7681135] using wordTrace_append hprefix tailTrace_7681135
  have hstable : (prefixWord ++ tailWord_7681135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681135).length < 2 ^ (prefixWord ++ tailWord_7681135).sum := by decide
  have hdescent : baseEnd_7681135 < baseStart_7681135 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681142 : List Nat := [5, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_7681142 : Nat := 118140960795 + 7681142 * 2 ^ 59
def prefixEnd_7681142 : Nat := 4983230072969 + 3 ^ 40 * 7681142 * 2
def baseEnd_7681142 : Nat := 3944117821437491730300077

theorem tailTrace_7681142 : CollatzResearch.WordTrace tailWord_7681142 prefixEnd_7681142 3944117821437491730300077 := by
  unfold tailWord_7681142
  simp only [CollatzResearch.WordTrace]
  refine ⟨17509641521158865216138855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 186769509559027895638814453 17509641521158865216138855)
  ·
    refine ⟨26264462281738297824208283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17509641521158865216138855 26264462281738297824208283)
    ·
      refine ⟨39396693422607446736312425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26264462281738297824208283 39396693422607446736312425)
      ·
        refine ⟨29547520066955585052234319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39396693422607446736312425 29547520066955585052234319)
        ·
          refine ⟨44321280100433377578351479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29547520066955585052234319 44321280100433377578351479)
          ·
            refine ⟨66481920150650066367527219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44321280100433377578351479 66481920150650066367527219)
            ·
              refine ⟨99722880225975099551290829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66481920150650066367527219 99722880225975099551290829)
              ·
                refine ⟨37396080084740662331734061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 99722880225975099551290829 37396080084740662331734061)
                ·
                  refine ⟨14023530031777748374400273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37396080084740662331734061 14023530031777748374400273)
                  ·
                    refine ⟨10517647523833311280800205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14023530031777748374400273 10517647523833311280800205)
                    ·
                      refine ⟨3944117821437491730300077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10517647523833311280800205 3944117821437491730300077)
                      ·
                        rfl

theorem cell23_7681142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_7681142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681142 prefixEnd_7681142 := by exact prefixLift 7681142
  have htrace : WordTrace (prefixWord ++ tailWord_7681142) baseStart_7681142 baseEnd_7681142 := by
    simpa [prefixWord, tailWord_7681142, baseEnd_7681142] using wordTrace_append hprefix tailTrace_7681142
  have hstable : (prefixWord ++ tailWord_7681142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681142).length < 2 ^ (prefixWord ++ tailWord_7681142).sum := by decide
  have hdescent : baseEnd_7681142 < baseStart_7681142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681155 : List Nat := [1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 3]
def baseStart_7681155 : Nat := 118140960795 + 7681155 * 2 ^ 59
def prefixEnd_7681155 : Nat := 4983230072969 + 3 ^ 40 * 7681155 * 2
def baseEnd_7681155 : Nat := 3944124496686000179437517

theorem tailTrace_7681155 : CollatzResearch.WordTrace tailWord_7681155 prefixEnd_7681155 3944124496686000179437517 := by
  unfold tailWord_7681155
  simp only [CollatzResearch.WordTrace]
  refine ⟨280154738487494746678444919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186769825658329831118963279 280154738487494746678444919)
  ·
    refine ⟨420232107731242120017667379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280154738487494746678444919 420232107731242120017667379)
    ·
      refine ⟨630348161596863180026501069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420232107731242120017667379 630348161596863180026501069)
      ·
        refine ⟨236380560598823692509937901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 630348161596863180026501069 236380560598823692509937901)
        ·
          refine ⟨88642710224558884691226713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 236380560598823692509937901 88642710224558884691226713)
          ·
            refine ⟨66482032668419163518420035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 88642710224558884691226713 66482032668419163518420035)
            ·
              refine ⟨99723049002628745277630053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66482032668419163518420035 99723049002628745277630053)
              ·
                refine ⟨18698071687992889739555635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 99723049002628745277630053 18698071687992889739555635)
                ·
                  refine ⟨28047107531989334609333453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18698071687992889739555635 28047107531989334609333453)
                  ·
                    refine ⟨10517665324496000478500045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28047107531989334609333453 10517665324496000478500045)
                    ·
                      refine ⟨3944124496686000179437517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10517665324496000478500045 3944124496686000179437517)
                      ·
                        rfl

theorem cell23_7681155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 4, 1, 3, 3].length) (baseStart_7681155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681155 prefixEnd_7681155 := by exact prefixLift 7681155
  have htrace : WordTrace (prefixWord ++ tailWord_7681155) baseStart_7681155 baseEnd_7681155 := by
    simpa [prefixWord, tailWord_7681155, baseEnd_7681155] using wordTrace_append hprefix tailTrace_7681155
  have hstable : (prefixWord ++ tailWord_7681155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681155).length < 2 ^ (prefixWord ++ tailWord_7681155).sum := by decide
  have hdescent : baseEnd_7681155 < baseStart_7681155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681156 : List Nat := [2, 3, 2, 1, 2, 2, 1, 5, 1, 2, 2]
def baseStart_7681156 : Nat := 118140960795 + 7681156 * 2 ^ 59
def prefixEnd_7681156 : Nat := 4983230072969 + 3 ^ 40 * 7681156 * 2
def baseEnd_7681156 : Nat := 3944125010166654675525013

theorem tailTrace_7681156 : CollatzResearch.WordTrace tailWord_7681156 prefixEnd_7681156 3944125010166654675525013 := by
  unfold tailWord_7681156
  simp only [CollatzResearch.WordTrace]
  refine ⟨140077387480245561924615661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186769849973660749232820881 140077387480245561924615661)
  ·
    refine ⟨52529020305092085721730873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140077387480245561924615661 52529020305092085721730873)
    ·
      refine ⟨39396765228819064291298155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 52529020305092085721730873 39396765228819064291298155)
      ·
        refine ⟨59095147843228596436947233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39396765228819064291298155 59095147843228596436947233)
        ·
          refine ⟨44321360882421447327710425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59095147843228596436947233 44321360882421447327710425)
          ·
            refine ⟨33241020661816085495782819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44321360882421447327710425 33241020661816085495782819)
            ·
              refine ⟨49861530992724128243674229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33241020661816085495782819 49861530992724128243674229)
              ·
                refine ⟨4674518530567887022844459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49861530992724128243674229 4674518530567887022844459)
                ·
                  refine ⟨7011777795851830534266689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4674518530567887022844459 7011777795851830534266689)
                  ·
                    refine ⟨5258833346888872900700017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7011777795851830534266689 5258833346888872900700017)
                    ·
                      refine ⟨3944125010166654675525013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5258833346888872900700017 3944125010166654675525013)
                      ·
                        rfl

theorem cell23_7681156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_7681156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681156 prefixEnd_7681156 := by exact prefixLift 7681156
  have htrace : WordTrace (prefixWord ++ tailWord_7681156) baseStart_7681156 baseEnd_7681156 := by
    simpa [prefixWord, tailWord_7681156, baseEnd_7681156] using wordTrace_append hprefix tailTrace_7681156
  have hstable : (prefixWord ++ tailWord_7681156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681156).length < 2 ^ (prefixWord ++ tailWord_7681156).sum := by decide
  have hdescent : baseEnd_7681156 < baseStart_7681156 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681168 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 5]
def baseStart_7681168 : Nat := 118140960795 + 7681168 * 2 ^ 59
def prefixEnd_7681168 : Nat := 4983230072969 + 3 ^ 40 * 7681168 * 2
def baseEnd_7681168 : Nat := 3944131171934508628574957

theorem tailTrace_7681168 : CollatzResearch.WordTrace tailWord_7681168 prefixEnd_7681168 3944131171934508628574957 := by
  unfold tailWord_7681168
  simp only [CollatzResearch.WordTrace]
  refine ⟨140077606318223824949334079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186770141757631766599112105 140077606318223824949334079)
  ·
    refine ⟨210116409477335737424001119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 140077606318223824949334079 210116409477335737424001119)
    ·
      refine ⟨315174614216003606136001679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210116409477335737424001119 315174614216003606136001679)
      ·
        refine ⟨472761921324005409204002519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 315174614216003606136001679 472761921324005409204002519)
        ·
          refine ⟨709142881986008113806003779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 472761921324005409204002519 709142881986008113806003779)
          ·
            refine ⟨1063714322979012170709005669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 709142881986008113806003779 1063714322979012170709005669)
            ·
              refine ⟨199446435558564782007938563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1063714322979012170709005669 199446435558564782007938563)
              ·
                refine ⟨299169653337847173011907845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 199446435558564782007938563 299169653337847173011907845)
                ·
                  refine ⟨56094310000846344939732721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 299169653337847173011907845 56094310000846344939732721)
                  ·
                    refine ⟨42070732500634758704799541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 56094310000846344939732721 42070732500634758704799541)
                    ·
                      refine ⟨3944131171934508628574957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42070732500634758704799541 3944131171934508628574957)
                      ·
                        rfl

theorem cell23_7681168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_7681168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681168 prefixEnd_7681168 := by exact prefixLift 7681168
  have htrace : WordTrace (prefixWord ++ tailWord_7681168) baseStart_7681168 baseEnd_7681168 := by
    simpa [prefixWord, tailWord_7681168, baseEnd_7681168] using wordTrace_append hprefix tailTrace_7681168
  have hstable : (prefixWord ++ tailWord_7681168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681168).length < 2 ^ (prefixWord ++ tailWord_7681168).sum := by decide
  have hdescent : baseEnd_7681168 < baseStart_7681168 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681186 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 1, 2, 4]
def baseStart_7681186 : Nat := 118140960795 + 7681186 * 2 ^ 59
def prefixEnd_7681186 : Nat := 4983230072969 + 3 ^ 40 * 7681186 * 2
def baseEnd_7681186 : Nat := 3944140414586289558149875

theorem tailTrace_7681186 : CollatzResearch.WordTrace tailWord_7681186 prefixEnd_7681186 3944140414586289558149875 := by
  unfold tailWord_7681186
  simp only [CollatzResearch.WordTrace]
  refine ⟨70038967287595609743205853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 186770579433588292648548941 70038967287595609743205853)
  ·
    refine ⟨26264612732848353653702195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 70038967287595609743205853 26264612732848353653702195)
    ·
      refine ⟨39396919099272530480553293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26264612732848353653702195 39396919099272530480553293)
      ·
        refine ⟨14773844662227198930207485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 39396919099272530480553293 14773844662227198930207485)
        ·
          refine ⟨5540191748335199598827807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14773844662227198930207485 5540191748335199598827807)
          ·
            refine ⟨8310287622502799398241711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5540191748335199598827807 8310287622502799398241711)
            ·
              refine ⟨12465431433754199097362567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8310287622502799398241711 12465431433754199097362567)
              ·
                refine ⟨18698147150631298646043851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12465431433754199097362567 18698147150631298646043851)
                ·
                  refine ⟨28047220725946947969065777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18698147150631298646043851 28047220725946947969065777)
                  ·
                    refine ⟨21035415544460210976799333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28047220725946947969065777 21035415544460210976799333)
                    ·
                      refine ⟨3944140414586289558149875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21035415544460210976799333 3944140414586289558149875)
                      ·
                        rfl

theorem cell23_7681186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_7681186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681186 prefixEnd_7681186 := by exact prefixLift 7681186
  have htrace : WordTrace (prefixWord ++ tailWord_7681186) baseStart_7681186 baseEnd_7681186 := by
    simpa [prefixWord, tailWord_7681186, baseEnd_7681186] using wordTrace_append hprefix tailTrace_7681186
  have hstable : (prefixWord ++ tailWord_7681186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681186).length < 2 ^ (prefixWord ++ tailWord_7681186).sum := by decide
  have hdescent : baseEnd_7681186 < baseStart_7681186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681332 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_7681332 : Nat := 118140960795 + 7681332 * 2 ^ 59
def prefixEnd_7681332 : Nat := 4983230072969 + 3 ^ 40 * 7681332 * 2
def baseEnd_7681332 : Nat := 3944215382761845986924203

theorem tailTrace_7681332 : CollatzResearch.WordTrace tailWord_7681332 prefixEnd_7681332 3944215382761845986924203 := by
  unfold tailWord_7681332
  simp only [CollatzResearch.WordTrace]
  refine ⟨140080597103926752953819125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186774129471902337271758833 140080597103926752953819125)
  ·
    refine ⟨13132555978493133089420543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 140080597103926752953819125 13132555978493133089420543)
    ·
      refine ⟨19698833967739699634130815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13132555978493133089420543 19698833967739699634130815)
      ·
        refine ⟨29548250951609549451196223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19698833967739699634130815 29548250951609549451196223)
        ·
          refine ⟨44322376427414324176794335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29548250951609549451196223 44322376427414324176794335)
          ·
            refine ⟨66483564641121486265191503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44322376427414324176794335 66483564641121486265191503)
            ·
              refine ⟨99725346961682229397787255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 66483564641121486265191503 99725346961682229397787255)
              ·
                refine ⟨149588020442523344096680883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 99725346961682229397787255 149588020442523344096680883)
                ·
                  refine ⟨224382030663785016145021325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 149588020442523344096680883 224382030663785016145021325)
                  ·
                    refine ⟨84143261498919381054382997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 224382030663785016145021325 84143261498919381054382997)
                    ·
                      refine ⟨3944215382761845986924203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 84143261498919381054382997 3944215382761845986924203)
                      ·
                        rfl

theorem cell23_7681332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_7681332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681332 prefixEnd_7681332 := by exact prefixLift 7681332
  have htrace : WordTrace (prefixWord ++ tailWord_7681332) baseStart_7681332 baseEnd_7681332 := by
    simpa [prefixWord, tailWord_7681332, baseEnd_7681332] using wordTrace_append hprefix tailTrace_7681332
  have hstable : (prefixWord ++ tailWord_7681332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681332).length < 2 ^ (prefixWord ++ tailWord_7681332).sum := by decide
  have hdescent : baseEnd_7681332 < baseStart_7681332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681342 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 8]
def baseStart_7681342 : Nat := 118140960795 + 7681342 * 2 ^ 59
def prefixEnd_7681342 : Nat := 4983230072969 + 3 ^ 40 * 7681342 * 2
def baseEnd_7681342 : Nat := 438246724174265660866573

theorem tailTrace_7681342 : CollatzResearch.WordTrace tailWord_7681342 prefixEnd_7681342 438246724174265660866573 := by
  unfold tailWord_7681342
  simp only [CollatzResearch.WordTrace]
  refine ⟨35020194867227159701937785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186774372625211518410334853 35020194867227159701937785)
  ·
    refine ⟨26265146150420369776453339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35020194867227159701937785 26265146150420369776453339)
    ·
      refine ⟨39397719225630554664680009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26265146150420369776453339 39397719225630554664680009)
      ·
        refine ⟨29548289419222915998510007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 39397719225630554664680009 29548289419222915998510007)
        ·
          refine ⟨44322434128834373997765011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29548289419222915998510007 44322434128834373997765011)
          ·
            refine ⟨66483651193251560996647517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 44322434128834373997765011 66483651193251560996647517)
            ·
              refine ⟨24931369197469335373742819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66483651193251560996647517 24931369197469335373742819)
              ·
                refine ⟨37397053796204003060614229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24931369197469335373742819 37397053796204003060614229)
                ·
                  refine ⟨438246724174265660866573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 37397053796204003060614229 438246724174265660866573)
                  ·
                    rfl

theorem cell23_7681342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_7681342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681342 prefixEnd_7681342 := by exact prefixLift 7681342
  have htrace : WordTrace (prefixWord ++ tailWord_7681342) baseStart_7681342 baseEnd_7681342 := by
    simpa [prefixWord, tailWord_7681342, baseEnd_7681342] using wordTrace_append hprefix tailTrace_7681342
  have hstable : (prefixWord ++ tailWord_7681342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681342).length < 2 ^ (prefixWord ++ tailWord_7681342).sum := by decide
  have hdescent : baseEnd_7681342 < baseStart_7681342 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681369 : List Nat := [1, 2, 1, 2, 2, 2, 4, 2, 3, 1, 3]
def baseStart_7681369 : Nat := 118140960795 + 7681369 * 2 ^ 59
def prefixEnd_7681369 : Nat := 4983230072969 + 3 ^ 40 * 7681369 * 2
def baseEnd_7681369 : Nat := 3944234381546062342161533

theorem tailTrace_7681369 : CollatzResearch.WordTrace tailWord_7681369 prefixEnd_7681369 3944234381546062342161533 := by
  unfold tailWord_7681369
  simp only [CollatzResearch.WordTrace]
  refine ⟨280162543708719461226735161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186775029139146307484490107 280162543708719461226735161)
  ·
    refine ⟨210121907781539595920051371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 280162543708719461226735161 210121907781539595920051371)
    ·
      refine ⟨315182861672309393880077057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 210121907781539595920051371 315182861672309393880077057)
      ·
        refine ⟨236387146254232045410057793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 315182861672309393880077057 236387146254232045410057793)
        ·
          refine ⟨177290359690674034057543345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 236387146254232045410057793 177290359690674034057543345)
          ·
            refine ⟨132967769768005525543157509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 177290359690674034057543345 132967769768005525543157509)
            ·
              refine ⟨24931456831501036039342033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132967769768005525543157509 24931456831501036039342033)
              ·
                refine ⟨18698592623625777029506525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24931456831501036039342033 18698592623625777029506525)
                ·
                  refine ⟨7011972233859666386064947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18698592623625777029506525 7011972233859666386064947)
                  ·
                    refine ⟨10517958350789499579097421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7011972233859666386064947 10517958350789499579097421)
                    ·
                      refine ⟨3944234381546062342161533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10517958350789499579097421 3944234381546062342161533)
                      ·
                        rfl

theorem cell23_7681369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 2, 3, 1, 3].length) (baseStart_7681369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681369 prefixEnd_7681369 := by exact prefixLift 7681369
  have htrace : WordTrace (prefixWord ++ tailWord_7681369) baseStart_7681369 baseEnd_7681369 := by
    simpa [prefixWord, tailWord_7681369, baseEnd_7681369] using wordTrace_append hprefix tailTrace_7681369
  have hstable : (prefixWord ++ tailWord_7681369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681369).length < 2 ^ (prefixWord ++ tailWord_7681369).sum := by decide
  have hdescent : baseEnd_7681369 < baseStart_7681369 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681379 : List Nat := [1, 1, 1, 5, 2, 2, 2, 1, 1, 5, 2]
def baseStart_7681379 : Nat := 118140960795 + 7681379 * 2 ^ 59
def prefixEnd_7681379 : Nat := 4983230072969 + 3 ^ 40 * 7681379 * 2
def baseEnd_7681379 : Nat := 3944239516352607303036487

theorem tailTrace_7681379 : CollatzResearch.WordTrace tailWord_7681379 prefixEnd_7681379 3944239516352607303036487 := by
  unfold tailWord_7681379
  simp only [CollatzResearch.WordTrace]
  refine ⟨280162908438683232934599191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186775272292455488623066127 280162908438683232934599191)
  ·
    refine ⟨420244362658024849401898787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280162908438683232934599191 420244362658024849401898787)
    ·
      refine ⟨630366543987037274102848181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420244362658024849401898787 630366543987037274102848181)
      ·
        refine ⟨59096863498784744447142017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 630366543987037274102848181 59096863498784744447142017)
        ·
          refine ⟨44322647624088558335356513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 59096863498784744447142017 44322647624088558335356513)
          ·
            refine ⟨33241985718066418751517385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 44322647624088558335356513 33241985718066418751517385)
            ·
              refine ⟨24931489288549814063638039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33241985718066418751517385 24931489288549814063638039)
              ·
                refine ⟨37397233932824721095457059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24931489288549814063638039 37397233932824721095457059)
                ·
                  refine ⟨56095850899237081643185589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 37397233932824721095457059 56095850899237081643185589)
                  ·
                    refine ⟨5258986021803476404048649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 56095850899237081643185589 5258986021803476404048649)
                    ·
                      refine ⟨3944239516352607303036487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5258986021803476404048649 3944239516352607303036487)
                      ·
                        rfl

theorem cell23_7681379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 5, 2].length) (baseStart_7681379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681379 prefixEnd_7681379 := by exact prefixLift 7681379
  have htrace : WordTrace (prefixWord ++ tailWord_7681379) baseStart_7681379 baseEnd_7681379 := by
    simpa [prefixWord, tailWord_7681379, baseEnd_7681379] using wordTrace_append hprefix tailTrace_7681379
  have hstable : (prefixWord ++ tailWord_7681379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681379).length < 2 ^ (prefixWord ++ tailWord_7681379).sum := by decide
  have hdescent : baseEnd_7681379 < baseStart_7681379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681389 : List Nat := [1, 5, 1, 1, 1, 3, 2, 3, 1, 5]
def baseStart_7681389 : Nat := 118140960795 + 7681389 * 2 ^ 59
def prefixEnd_7681389 : Nat := 4983230072969 + 3 ^ 40 * 7681389 * 2
def baseEnd_7681389 : Nat := 1314748217053050754637147

theorem tailTrace_7681389 : CollatzResearch.WordTrace tailWord_7681389 prefixEnd_7681389 1314748217053050754637147 := by
  unfold tailWord_7681389
  simp only [CollatzResearch.WordTrace]
  refine ⟨280163273168647004642463221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186775515445764669761642147 280163273168647004642463221)
  ·
    refine ⟨26265306859560656685230927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280163273168647004642463221 26265306859560656685230927)
    ·
      refine ⟨39397960289340985027846391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26265306859560656685230927 39397960289340985027846391)
      ·
        refine ⟨59096940434011477541769587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 39397960289340985027846391 59096940434011477541769587)
        ·
          refine ⟨88645410651017216312654381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 59096940434011477541769587 88645410651017216312654381)
          ·
            refine ⟨33242028994131456117245393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 88645410651017216312654381 33242028994131456117245393)
            ·
              refine ⟨24931521745598592087934045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33242028994131456117245393 24931521745598592087934045)
              ·
                refine ⟨9349320654599472032975267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24931521745598592087934045 9349320654599472032975267)
                ·
                  refine ⟨14023980981899208049462901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9349320654599472032975267 14023980981899208049462901)
                  ·
                    refine ⟨1314748217053050754637147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14023980981899208049462901 1314748217053050754637147)
                    ·
                      rfl

theorem cell23_7681389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 5].length) (baseStart_7681389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681389 prefixEnd_7681389 := by exact prefixLift 7681389
  have htrace : WordTrace (prefixWord ++ tailWord_7681389) baseStart_7681389 baseEnd_7681389 := by
    simpa [prefixWord, tailWord_7681389, baseEnd_7681389] using wordTrace_append hprefix tailTrace_7681389
  have hstable : (prefixWord ++ tailWord_7681389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681389).length < 2 ^ (prefixWord ++ tailWord_7681389).sum := by decide
  have hdescent : baseEnd_7681389 < baseStart_7681389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681403 : List Nat := [1, 1, 1, 1, 1, 6, 5, 2, 1, 1, 3]
def baseStart_7681403 : Nat := 118140960795 + 7681403 * 2 ^ 59
def prefixEnd_7681403 : Nat := 4983230072969 + 3 ^ 40 * 7681403 * 2
def baseEnd_7681403 : Nat := 3944251839888315209136377

theorem tailTrace_7681403 : CollatzResearch.WordTrace tailWord_7681403 prefixEnd_7681403 3944251839888315209136377 := by
  unfold tailWord_7681403
  simp only [CollatzResearch.WordTrace]
  refine ⟨280163783790596285033472863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186775855860397523355648575 280163783790596285033472863)
  ·
    refine ⟨420245675685894427550209295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280163783790596285033472863 420245675685894427550209295)
    ·
      refine ⟨630368513528841641325313943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420245675685894427550209295 630368513528841641325313943)
      ·
        refine ⟨945552770293262461987970915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630368513528841641325313943 945552770293262461987970915)
        ·
          refine ⟨1418329155439893692981956373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 945552770293262461987970915 1418329155439893692981956373)
          ·
            refine ⟨66484179161245016858529205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1418329155439893692981956373 66484179161245016858529205)
            ·
              refine ⟨6232891796366720330487113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 66484179161245016858529205 6232891796366720330487113)
              ·
                refine ⟨4674668847275040247865335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6232891796366720330487113 4674668847275040247865335)
                ·
                  refine ⟨7012003270912560371798003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4674668847275040247865335 7012003270912560371798003)
                  ·
                    refine ⟨10518004906368840557697005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7012003270912560371798003 10518004906368840557697005)
                    ·
                      refine ⟨3944251839888315209136377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10518004906368840557697005 3944251839888315209136377)
                      ·
                        rfl

theorem cell23_7681403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 2, 1, 1, 3].length) (baseStart_7681403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681403 prefixEnd_7681403 := by exact prefixLift 7681403
  have htrace : WordTrace (prefixWord ++ tailWord_7681403) baseStart_7681403 baseEnd_7681403 := by
    simpa [prefixWord, tailWord_7681403, baseEnd_7681403] using wordTrace_append hprefix tailTrace_7681403
  have hstable : (prefixWord ++ tailWord_7681403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681403).length < 2 ^ (prefixWord ++ tailWord_7681403).sum := by decide
  have hdescent : baseEnd_7681403 < baseStart_7681403 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681419 : List Nat := [1, 1, 1, 1, 4, 3, 3, 3, 2, 4]
def baseStart_7681419 : Nat := 118140960795 + 7681419 * 2 ^ 59
def prefixEnd_7681419 : Nat := 4983230072969 + 3 ^ 40 * 7681419 * 2
def baseEnd_7681419 : Nat := 1314753351859595715512101

theorem tailTrace_7681419 : CollatzResearch.WordTrace tailWord_7681419 prefixEnd_7681419 1314753351859595715512101 := by
  unfold tailWord_7681419
  simp only [CollatzResearch.WordTrace]
  refine ⟨280164367358538319766055311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186776244905692213177370207 280164367358538319766055311)
  ·
    refine ⟨420246551037807479649082967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280164367358538319766055311 420246551037807479649082967)
    ·
      refine ⟨630369826556711219473624451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420246551037807479649082967 630369826556711219473624451)
      ·
        refine ⟨945554739835066829210436677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 630369826556711219473624451 945554739835066829210436677)
        ·
          refine ⟨177291513719075030476956877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 945554739835066829210436677 177291513719075030476956877)
          ·
            refine ⟨66484317644653136428858829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177291513719075030476956877 66484317644653136428858829)
            ·
              refine ⟨24931619116744926160822061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 66484317644653136428858829 24931619116744926160822061)
              ·
                refine ⟨9349357168779347310308273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24931619116744926160822061 9349357168779347310308273)
                ·
                  refine ⟨7012017876584510482731205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9349357168779347310308273 7012017876584510482731205)
                  ·
                    refine ⟨1314753351859595715512101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7012017876584510482731205 1314753351859595715512101)
                    ·
                      rfl

theorem cell23_7681419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 4].length) (baseStart_7681419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681419 prefixEnd_7681419 := by exact prefixLift 7681419
  have htrace : WordTrace (prefixWord ++ tailWord_7681419) baseStart_7681419 baseEnd_7681419 := by
    simpa [prefixWord, tailWord_7681419, baseEnd_7681419] using wordTrace_append hprefix tailTrace_7681419
  have hstable : (prefixWord ++ tailWord_7681419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681419).length < 2 ^ (prefixWord ++ tailWord_7681419).sum := by decide
  have hdescent : baseEnd_7681419 < baseStart_7681419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681436 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 1, 6]
def baseStart_7681436 : Nat := 118140960795 + 7681436 * 2 ^ 59
def prefixEnd_7681436 : Nat := 4983230072969 + 3 ^ 40 * 7681436 * 2
def baseEnd_7681436 : Nat := 1314756261583304526674575

theorem tailTrace_7681436 : CollatzResearch.WordTrace tailWord_7681436 prefixEnd_7681436 1314756261583304526674575 := by
  unfold tailWord_7681436
  simp only [CollatzResearch.WordTrace]
  refine ⟨140082493699738365834712081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186776658266317821112949441 140082493699738365834712081)
  ·
    refine ⟨105061870274803774376034061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 140082493699738365834712081 105061870274803774376034061)
    ·
      refine ⟨39398201353051415391012773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 105061870274803774376034061 39398201353051415391012773)
      ·
        refine ⟨7387162753697140385814895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 39398201353051415391012773 7387162753697140385814895)
        ·
          refine ⟨11080744130545710578722343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7387162753697140385814895 11080744130545710578722343)
          ·
            refine ⟨16621116195818565868083515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11080744130545710578722343 16621116195818565868083515)
            ·
              refine ⟨24931674293727848802125273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16621116195818565868083515 24931674293727848802125273)
              ·
                refine ⟨18698755720295886601593955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24931674293727848802125273 18698755720295886601593955)
                ·
                  refine ⟨28048133580443829902390933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18698755720295886601593955 28048133580443829902390933)
                  ·
                    refine ⟨1314756261583304526674575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28048133580443829902390933 1314756261583304526674575)
                    ·
                      rfl

theorem cell23_7681436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_7681436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681436 prefixEnd_7681436 := by exact prefixLift 7681436
  have htrace : WordTrace (prefixWord ++ tailWord_7681436) baseStart_7681436 baseEnd_7681436 := by
    simpa [prefixWord, tailWord_7681436, baseEnd_7681436] using wordTrace_append hprefix tailTrace_7681436
  have hstable : (prefixWord ++ tailWord_7681436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681436).length < 2 ^ (prefixWord ++ tailWord_7681436).sum := by decide
  have hdescent : baseEnd_7681436 < baseStart_7681436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681439 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 4]
def baseStart_7681439 : Nat := 118140960795 + 7681439 * 2 ^ 59
def prefixEnd_7681439 : Nat := 4983230072969 + 3 ^ 40 * 7681439 * 2
def baseEnd_7681439 : Nat := 3944270325191877068286211

theorem tailTrace_7681439 : CollatzResearch.WordTrace tailWord_7681439 prefixEnd_7681439 3944270325191877068286211 := by
  unfold tailWord_7681439
  simp only [CollatzResearch.WordTrace]
  refine ⟨280165096818465863181783371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186776731212310575454522247 280165096818465863181783371)
  ·
    refine ⟨420247645227698794772675057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280165096818465863181783371 420247645227698794772675057)
    ·
      refine ⟨315185733920774096079506293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 420247645227698794772675057 315185733920774096079506293)
      ·
        refine ⟨29548662555072571507453715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 315185733920774096079506293 29548662555072571507453715)
        ·
          refine ⟨44322993832608857261180573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29548662555072571507453715 44322993832608857261180573)
          ·
            refine ⟨16621122687228321472942715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 44322993832608857261180573 16621122687228321472942715)
            ·
              refine ⟨24931684030842482209414073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16621122687228321472942715 24931684030842482209414073)
              ·
                refine ⟨18698763023131861657060555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24931684030842482209414073 18698763023131861657060555)
                ·
                  refine ⟨28048144534697792485590833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18698763023131861657060555 28048144534697792485590833)
                  ·
                    refine ⟨21036108401023344364193125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28048144534697792485590833 21036108401023344364193125)
                    ·
                      refine ⟨3944270325191877068286211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21036108401023344364193125 3944270325191877068286211)
                      ·
                        rfl

theorem cell23_7681439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_7681439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681439 prefixEnd_7681439 := by exact prefixLift 7681439
  have htrace : WordTrace (prefixWord ++ tailWord_7681439) baseStart_7681439 baseEnd_7681439 := by
    simpa [prefixWord, tailWord_7681439, baseEnd_7681439] using wordTrace_append hprefix tailTrace_7681439
  have hstable : (prefixWord ++ tailWord_7681439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681439).length < 2 ^ (prefixWord ++ tailWord_7681439).sum := by decide
  have hdescent : baseEnd_7681439 < baseStart_7681439 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681443 : List Nat := [1, 1, 1, 4, 1, 3, 2, 5, 1, 2, 2]
def baseStart_7681443 : Nat := 118140960795 + 7681443 * 2 ^ 59
def prefixEnd_7681443 : Nat := 4983230072969 + 3 ^ 40 * 7681443 * 2
def baseEnd_7681443 : Nat := 3944272379114495052636193

theorem tailTrace_7681443 : CollatzResearch.WordTrace tailWord_7681443 prefixEnd_7681443 3944272379114495052636193 := by
  unfold tailWord_7681443
  simp only [CollatzResearch.WordTrace]
  refine ⟨280165242710451371864928983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186776828473634247909952655 280165242710451371864928983)
  ·
    refine ⟨420247864065677057797393475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280165242710451371864928983 420247864065677057797393475)
    ·
      refine ⟨630371796098515586696090213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420247864065677057797393475 630371796098515586696090213)
      ·
        refine ⟨118194711768471672505516915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 630371796098515586696090213 118194711768471672505516915)
        ·
          refine ⟨177292067652707508758275373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118194711768471672505516915 177292067652707508758275373)
          ·
            refine ⟨66484525369765315784353265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 177292067652707508758275373 66484525369765315784353265)
            ·
              refine ⟨49863394027323986838264949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 66484525369765315784353265 49863394027323986838264949)
              ·
                refine ⟨4674693190061623766087339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 49863394027323986838264949 4674693190061623766087339)
                ·
                  refine ⟨7012039785092435649131009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4674693190061623766087339 7012039785092435649131009)
                  ·
                    refine ⟨5259029838819326736848257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7012039785092435649131009 5259029838819326736848257)
                    ·
                      refine ⟨3944272379114495052636193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5259029838819326736848257 3944272379114495052636193)
                      ·
                        rfl

theorem cell23_7681443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 1, 2, 2].length) (baseStart_7681443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681443 prefixEnd_7681443 := by exact prefixLift 7681443
  have htrace : WordTrace (prefixWord ++ tailWord_7681443) baseStart_7681443 baseEnd_7681443 := by
    simpa [prefixWord, tailWord_7681443, baseEnd_7681443] using wordTrace_append hprefix tailTrace_7681443
  have hstable : (prefixWord ++ tailWord_7681443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681443).length < 2 ^ (prefixWord ++ tailWord_7681443).sum := by decide
  have hdescent : baseEnd_7681443 < baseStart_7681443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681453 : List Nat := [1, 5, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_7681453 : Nat := 118140960795 + 7681453 * 2 ^ 59
def prefixEnd_7681453 : Nat := 4983230072969 + 3 ^ 40 * 7681453 * 2
def baseEnd_7681453 : Nat := 1314759171307013337837049

theorem tailTrace_7681453 : CollatzResearch.WordTrace tailWord_7681453 prefixEnd_7681453 1314759171307013337837049 := by
  unfold tailWord_7681453
  simp only [CollatzResearch.WordTrace]
  refine ⟨280165607440415143572793013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186777071626943429048528675 280165607440415143572793013)
  ·
    refine ⟨26265525697538919709949345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 280165607440415143572793013 26265525697538919709949345)
    ·
      refine ⟨19699144273154189782462009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26265525697538919709949345 19699144273154189782462009)
      ·
        refine ⟨14774358204865642336846507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19699144273154189782462009 14774358204865642336846507)
        ·
          refine ⟨22161537307298463505269761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14774358204865642336846507 22161537307298463505269761)
          ·
            refine ⟨16621152980473847628952321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22161537307298463505269761 16621152980473847628952321)
            ·
              refine ⟨12465864735355385721714241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16621152980473847628952321 12465864735355385721714241)
              ·
                refine ⟨9349398551516539291285681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12465864735355385721714241 9349398551516539291285681)
                ·
                  refine ⟨7012048913637404468464261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9349398551516539291285681 7012048913637404468464261)
                  ·
                    refine ⟨1314759171307013337837049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7012048913637404468464261 1314759171307013337837049)
                    ·
                      rfl

theorem cell23_7681453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_7681453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681453 prefixEnd_7681453 := by exact prefixLift 7681453
  have htrace : WordTrace (prefixWord ++ tailWord_7681453) baseStart_7681453 baseEnd_7681453 := by
    simpa [prefixWord, tailWord_7681453, baseEnd_7681453] using wordTrace_append hprefix tailTrace_7681453
  have hstable : (prefixWord ++ tailWord_7681453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681453).length < 2 ^ (prefixWord ++ tailWord_7681453).sum := by decide
  have hdescent : baseEnd_7681453 < baseStart_7681453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681459 : List Nat := [1, 1, 1, 2, 3, 1, 1, 5, 4, 1, 3]
def baseStart_7681459 : Nat := 118140960795 + 7681459 * 2 ^ 59
def prefixEnd_7681459 : Nat := 4983230072969 + 3 ^ 40 * 7681459 * 2
def baseEnd_7681459 : Nat := 3944280594804966990036119

theorem tailTrace_7681459 : CollatzResearch.WordTrace tailWord_7681459 prefixEnd_7681459 3944280594804966990036119 := by
  unfold tailWord_7681459
  simp only [CollatzResearch.WordTrace]
  refine ⟨280165826278393406597511431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186777217518928937731674287 280165826278393406597511431)
  ·
    refine ⟨420248739417590109896267147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 280165826278393406597511431 420248739417590109896267147)
    ·
      refine ⟨630373109126385164844400721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 420248739417590109896267147 630373109126385164844400721)
      ·
        refine ⟨472779831844788873633300541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 630373109126385164844400721 472779831844788873633300541)
        ·
          refine ⟨177292436941795827612487703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 472779831844788873633300541 177292436941795827612487703)
          ·
            refine ⟨265938655412693741418731555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 177292436941795827612487703 265938655412693741418731555)
            ·
              refine ⟨398907983119040612128097333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 265938655412693741418731555 398907983119040612128097333)
              ·
                refine ⟨37397623417410057387009125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 398907983119040612128097333 37397623417410057387009125)
                ·
                  refine ⟨7012054390764385760064211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 37397623417410057387009125 7012054390764385760064211)
                  ·
                    refine ⟨10518081586146578640096317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7012054390764385760064211 10518081586146578640096317)
                    ·
                      refine ⟨3944280594804966990036119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10518081586146578640096317 3944280594804966990036119)
                      ·
                        rfl

theorem cell23_7681459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 5, 4, 1, 3].length) (baseStart_7681459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681459 prefixEnd_7681459 := by exact prefixLift 7681459
  have htrace : WordTrace (prefixWord ++ tailWord_7681459) baseStart_7681459 baseEnd_7681459 := by
    simpa [prefixWord, tailWord_7681459, baseEnd_7681459] using wordTrace_append hprefix tailTrace_7681459
  have hstable : (prefixWord ++ tailWord_7681459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681459).length < 2 ^ (prefixWord ++ tailWord_7681459).sum := by decide
  have hdescent : baseEnd_7681459 < baseStart_7681459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681476 : List Nat := [2, 3, 3, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_7681476 : Nat := 118140960795 + 7681476 * 2 ^ 59
def prefixEnd_7681476 : Nat := 4983230072969 + 3 ^ 40 * 7681476 * 2
def baseEnd_7681476 : Nat := 3944289323976093423523541

theorem tailTrace_7681476 : CollatzResearch.WordTrace tailWord_7681476 prefixEnd_7681476 3944289323976093423523541 := by
  unfold tailWord_7681476
  simp only [CollatzResearch.WordTrace]
  refine ⟨140083223159665909250440141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 186777630879554545667253521 140083223159665909250440141)
  ·
    refine ⟨52531208684874715968915053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 140083223159665909250440141 52531208684874715968915053)
    ·
      refine ⟨19699203256828018488343145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 52531208684874715968915053 19699203256828018488343145)
      ·
        refine ⟨14774402442621013866257359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19699203256828018488343145 14774402442621013866257359)
        ·
          refine ⟨22161603663931520799386039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14774402442621013866257359 22161603663931520799386039)
          ·
            refine ⟨33242405495897281199079059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22161603663931520799386039 33242405495897281199079059)
            ·
              refine ⟨49863608243845921798618589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33242405495897281199079059 49863608243845921798618589)
              ·
                refine ⟨18698853091442220674481971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 49863608243845921798618589 18698853091442220674481971)
                ·
                  refine ⟨28048279637163331011722957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18698853091442220674481971 28048279637163331011722957)
                  ·
                    refine ⟨10518104863936249129396109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28048279637163331011722957 10518104863936249129396109)
                    ·
                      refine ⟨3944289323976093423523541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10518104863936249129396109 3944289323976093423523541)
                      ·
                        rfl

theorem cell23_7681476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_7681476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681476 prefixEnd_7681476 := by exact prefixLift 7681476
  have htrace : WordTrace (prefixWord ++ tailWord_7681476) baseStart_7681476 baseEnd_7681476 := by
    simpa [prefixWord, tailWord_7681476, baseEnd_7681476] using wordTrace_append hprefix tailTrace_7681476
  have hstable : (prefixWord ++ tailWord_7681476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681476).length < 2 ^ (prefixWord ++ tailWord_7681476).sum := by decide
  have hdescent : baseEnd_7681476 < baseStart_7681476 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681486 : List Nat := [4, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2]
def baseStart_7681486 : Nat := 118140960795 + 7681486 * 2 ^ 59
def prefixEnd_7681486 : Nat := 4983230072969 + 3 ^ 40 * 7681486 * 2
def baseEnd_7681486 : Nat := 3944294458782638384398495

theorem tailTrace_7681486 : CollatzResearch.WordTrace tailWord_7681486 prefixEnd_7681486 3944294458782638384398495 := by
  unfold tailWord_7681486
  simp only [CollatzResearch.WordTrace]
  refine ⟨35020851381161948776093039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 186777874032863726805829541 35020851381161948776093039)
  ·
    refine ⟨52531277071742923164139559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35020851381161948776093039 52531277071742923164139559)
    ·
      refine ⟨78796915607614384746209339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52531277071742923164139559 78796915607614384746209339)
      ·
        refine ⟨118195373411421577119314009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78796915607614384746209339 118195373411421577119314009)
        ·
          refine ⟨88646530058566182839485507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 118195373411421577119314009 88646530058566182839485507)
          ·
            refine ⟨132969795087849274259228261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 88646530058566182839485507 132969795087849274259228261)
            ·
              refine ⟨24931836578971738923605299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 132969795087849274259228261 24931836578971738923605299)
              ·
                refine ⟨37397754868457608385407949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24931836578971738923605299 37397754868457608385407949)
                ·
                  refine ⟨14024158075671603144527981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 37397754868457608385407949 14024158075671603144527981)
                  ·
                    refine ⟨5259059278376851179197993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14024158075671603144527981 5259059278376851179197993)
                    ·
                      refine ⟨3944294458782638384398495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5259059278376851179197993 3944294458782638384398495)
                      ·
                        rfl

theorem cell23_7681486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_7681486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681486 prefixEnd_7681486 := by exact prefixLift 7681486
  have htrace : WordTrace (prefixWord ++ tailWord_7681486) baseStart_7681486 baseEnd_7681486 := by
    simpa [prefixWord, tailWord_7681486, baseEnd_7681486] using wordTrace_append hprefix tailTrace_7681486
  have hstable : (prefixWord ++ tailWord_7681486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681486).length < 2 ^ (prefixWord ++ tailWord_7681486).sum := by decide
  have hdescent : baseEnd_7681486 < baseStart_7681486 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681509 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 2, 6]
def baseStart_7681509 : Nat := 118140960795 + 7681509 * 2 ^ 59
def prefixEnd_7681509 : Nat := 4983230072969 + 3 ^ 40 * 7681509 * 2
def baseEnd_7681509 : Nat := 1314768756279230598136963

theorem tailTrace_7681509 : CollatzResearch.WordTrace tailWord_7681509 prefixEnd_7681509 1314768756279230598136963 := by
  unfold tailWord_7681509
  simp only [CollatzResearch.WordTrace]
  refine ⟨280167649928212265136831581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186778433285474843424554387 280167649928212265136831581)
  ·
    refine ⟨105062868723079599426311843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 280167649928212265136831581 105062868723079599426311843)
    ·
      refine ⟨157594303084619399139467765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 105062868723079599426311843 157594303084619399139467765)
      ·
        refine ⟨14774465914183068669325103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 157594303084619399139467765 14774465914183068669325103)
        ·
          refine ⟨22161698871274603003987655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14774465914183068669325103 22161698871274603003987655)
          ·
            refine ⟨33242548306911904505981483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22161698871274603003987655 33242548306911904505981483)
            ·
              refine ⟨49863822460367856758972225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33242548306911904505981483 49863822460367856758972225)
              ·
                refine ⟨37397866845275892569229169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 49863822460367856758972225 37397866845275892569229169)
                ·
                  refine ⟨28048400133956919426921877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 37397866845275892569229169 28048400133956919426921877)
                  ·
                    refine ⟨1314768756279230598136963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28048400133956919426921877 1314768756279230598136963)
                    ·
                      rfl

theorem cell23_7681509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 6].length) (baseStart_7681509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681509 prefixEnd_7681509 := by exact prefixLift 7681509
  have htrace : WordTrace (prefixWord ++ tailWord_7681509) baseStart_7681509 baseEnd_7681509 := by
    simpa [prefixWord, tailWord_7681509, baseEnd_7681509] using wordTrace_append hprefix tailTrace_7681509
  have hstable : (prefixWord ++ tailWord_7681509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681509).length < 2 ^ (prefixWord ++ tailWord_7681509).sum := by decide
  have hdescent : baseEnd_7681509 < baseStart_7681509 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7681533 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 1, 4, 2]
def baseStart_7681533 : Nat := 118140960795 + 7681533 * 2 ^ 59
def prefixEnd_7681533 : Nat := 4983230072969 + 3 ^ 40 * 7681533 * 2
def baseEnd_7681533 : Nat := 3944318592373399700510779

theorem tailTrace_7681533 : CollatzResearch.WordTrace tailWord_7681533 prefixEnd_7681533 3944318592373399700510779 := by
  unfold tailWord_7681533
  simp only [CollatzResearch.WordTrace]
  refine ⟨280168525280125317235705253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 186779016853416878157136835 280168525280125317235705253)
  ·
    refine ⟨52531598490023496981694735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 280168525280125317235705253 52531598490023496981694735)
    ·
      refine ⟨78797397735035245472542103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 52531598490023496981694735 78797397735035245472542103)
      ·
        refine ⟨118196096602552868208813155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 78797397735035245472542103 118196096602552868208813155)
        ·
          refine ⟨177294144903829302313219733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 118196096602552868208813155 177294144903829302313219733)
          ·
            refine ⟨8310663042366998545932175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 177294144903829302313219733 8310663042366998545932175)
            ·
              refine ⟨12465994563550497818898263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8310663042366998545932175 12465994563550497818898263)
              ·
                refine ⟨18698991845325746728347395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12465994563550497818898263 18698991845325746728347395)
                ·
                  refine ⟨28048487767988620092521093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18698991845325746728347395 28048487767988620092521093)
                  ·
                    refine ⟨5259091456497866267347705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28048487767988620092521093 5259091456497866267347705)
                    ·
                      refine ⟨3944318592373399700510779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5259091456497866267347705 3944318592373399700510779)
                      ·
                        rfl

theorem cell23_7681533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 4, 2].length) (baseStart_7681533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7681533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7681533 prefixEnd_7681533 := by exact prefixLift 7681533
  have htrace : WordTrace (prefixWord ++ tailWord_7681533) baseStart_7681533 baseEnd_7681533 := by
    simpa [prefixWord, tailWord_7681533, baseEnd_7681533] using wordTrace_append hprefix tailTrace_7681533
  have hstable : (prefixWord ++ tailWord_7681533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7681533).length < 2 ^ (prefixWord ++ tailWord_7681533).sum := by decide
  have hdescent : baseEnd_7681533 < baseStart_7681533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7681533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
