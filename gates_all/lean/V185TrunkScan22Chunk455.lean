import V185TrunkScan22Chunk454

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_4056444 : List Nat := [2, 2, 2, 1, 1, 1, 3, 4, 3, 3]
def baseStart_4056444 : Nat := 118140960795 + 4056444 * 2 ^ 59
def prefixEnd_4056444 : Nat := 4983230072969 + 3 ^ 40 * 4056444 * 2
def baseEnd_4056444 : Nat := 1388603680031221585263173

theorem tailTrace_4056444 : CollatzResearch.WordTrace tailWord_4056444 prefixEnd_4056444 1388603680031221585263173 := by
  unfold tailWord_4056444
  simp only [CollatzResearch.WordTrace]
  refine ⟨73975333658101824162420193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98633778210802432216560257 73975333658101824162420193)
  ·
    refine ⟨55481500243576368121815145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73975333658101824162420193 55481500243576368121815145)
    ·
      refine ⟨41611125182682276091361359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55481500243576368121815145 41611125182682276091361359)
      ·
        refine ⟨62416687774023414137042039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41611125182682276091361359 62416687774023414137042039)
        ·
          refine ⟨93625031661035121205563059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62416687774023414137042039 93625031661035121205563059)
          ·
            refine ⟨140437547491552681808344589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93625031661035121205563059 140437547491552681808344589)
            ·
              refine ⟨52664080309332255678129221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 140437547491552681808344589 52664080309332255678129221)
              ·
                refine ⟨9874515057999797939649229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52664080309332255678129221 9874515057999797939649229)
                ·
                  refine ⟨3702943146749924227368461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9874515057999797939649229 3702943146749924227368461)
                  ·
                    refine ⟨1388603680031221585263173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3702943146749924227368461 1388603680031221585263173)
                    ·
                      rfl

theorem cell22_4056444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 4, 3, 3].length) (baseStart_4056444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056444 prefixEnd_4056444 := by exact prefixLift 4056444
  have htrace : WordTrace (prefixWord ++ tailWord_4056444) baseStart_4056444 baseEnd_4056444 := by
    simpa [prefixWord, tailWord_4056444, baseEnd_4056444] using wordTrace_append hprefix tailTrace_4056444
  have hstable : (prefixWord ++ tailWord_4056444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056444).length < 2 ^ (prefixWord ++ tailWord_4056444).sum := by decide
  have hdescent : baseEnd_4056444 < baseStart_4056444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056474 : List Nat := [3, 1, 1, 4, 1, 1, 2, 4, 5]
def baseStart_4056474 : Nat := 118140960795 + 4056474 * 2 ^ 59
def prefixEnd_4056474 : Nat := 4983230072969 + 3 ^ 40 * 4056474 * 2
def baseEnd_4056474 : Nat := 462871316548103835671027

theorem tailTrace_4056474 : CollatzResearch.WordTrace tailWord_4056474 prefixEnd_4056474 462871316548103835671027 := by
  unfold tailWord_4056474
  simp only [CollatzResearch.WordTrace]
  refine ⟨36987940376523740862108119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98634507670729975632288317 36987940376523740862108119)
  ·
    refine ⟨55481910564785611293162179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36987940376523740862108119 55481910564785611293162179)
    ·
      refine ⟨83222865847178416939743269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55481910564785611293162179 83222865847178416939743269)
      ·
        refine ⟨15604287346345953176201863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83222865847178416939743269 15604287346345953176201863)
        ·
          refine ⟨23406431019518929764302795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15604287346345953176201863 23406431019518929764302795)
          ·
            refine ⟨35109646529278394646454193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23406431019518929764302795 35109646529278394646454193)
            ·
              refine ⟨26332234896958795984840645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35109646529278394646454193 26332234896958795984840645)
              ·
                refine ⟨4937294043179774247157621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26332234896958795984840645 4937294043179774247157621)
                ·
                  refine ⟨462871316548103835671027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4937294043179774247157621 462871316548103835671027)
                  ·
                    rfl

theorem cell22_4056474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_4056474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056474 prefixEnd_4056474 := by exact prefixLift 4056474
  have htrace : WordTrace (prefixWord ++ tailWord_4056474) baseStart_4056474 baseEnd_4056474 := by
    simpa [prefixWord, tailWord_4056474, baseEnd_4056474] using wordTrace_append hprefix tailTrace_4056474
  have hstable : (prefixWord ++ tailWord_4056474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056474).length < 2 ^ (prefixWord ++ tailWord_4056474).sum := by decide
  have hdescent : baseEnd_4056474 < baseStart_4056474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056551 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 1, 5]
def baseStart_4056551 : Nat := 118140960795 + 4056551 * 2 ^ 59
def prefixEnd_4056551 : Nat := 4983230072969 + 3 ^ 40 * 4056551 * 2
def baseEnd_4056551 : Nat := 1388640308317908972837845

theorem tailTrace_4056551 : CollatzResearch.WordTrace tailWord_4056551 prefixEnd_4056551 1388640308317908972837845 := by
  unfold tailWord_4056551
  simp only [CollatzResearch.WordTrace]
  refine ⟨147954569926816005598985507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98636379951210670399323671 147954569926816005598985507)
  ·
    refine ⟨221931854890224008398478261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147954569926816005598985507 221931854890224008398478261)
    ·
      refine ⟨20806111395958500787357337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 221931854890224008398478261 20806111395958500787357337)
      ·
        refine ⟨15604583546968875590518003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20806111395958500787357337 15604583546968875590518003)
        ·
          refine ⟨23406875320453313385777005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15604583546968875590518003 23406875320453313385777005)
          ·
            refine ⟨8777578245169992519666377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23406875320453313385777005 8777578245169992519666377)
            ·
              refine ⟨6583183683877494389749783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8777578245169992519666377 6583183683877494389749783)
              ·
                refine ⟨9874775525816241584624675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6583183683877494389749783 9874775525816241584624675)
                ·
                  refine ⟨14812163288724362376937013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9874775525816241584624675 14812163288724362376937013)
                  ·
                    refine ⟨1388640308317908972837845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14812163288724362376937013 1388640308317908972837845)
                    ·
                      rfl

theorem cell22_4056551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_4056551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056551 prefixEnd_4056551 := by exact prefixLift 4056551
  have htrace : WordTrace (prefixWord ++ tailWord_4056551) baseStart_4056551 baseEnd_4056551 := by
    simpa [prefixWord, tailWord_4056551, baseEnd_4056551] using wordTrace_append hprefix tailTrace_4056551
  have hstable : (prefixWord ++ tailWord_4056551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056551).length < 2 ^ (prefixWord ++ tailWord_4056551).sum := by decide
  have hdescent : baseEnd_4056551 < baseStart_4056551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056566 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 1, 6]
def baseStart_4056566 : Nat := 118140960795 + 4056566 * 2 ^ 59
def prefixEnd_4056566 : Nat := 4983230072969 + 3 ^ 40 * 4056566 * 2
def baseEnd_4056566 : Nat := 1388645443124453933712799

theorem tailTrace_4056566 : CollatzResearch.WordTrace tailWord_4056566 prefixEnd_4056566 1388645443124453933712799 := by
  unfold tailWord_4056566
  simp only [CollatzResearch.WordTrace]
  refine ⟨9247194813860103947548847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98636744681174442107187701 9247194813860103947548847)
  ·
    refine ⟨13870792220790155921323271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9247194813860103947548847 13870792220790155921323271)
    ·
      refine ⟨20806188331185233881984907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13870792220790155921323271 20806188331185233881984907)
      ·
        refine ⟨31209282496777850822977361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20806188331185233881984907 31209282496777850822977361)
        ·
          refine ⟨23406961872583388117233021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31209282496777850822977361 23406961872583388117233021)
          ·
            refine ⟨8777610702218770543962383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23406961872583388117233021 8777610702218770543962383)
            ·
              refine ⟨13166416053328155815943575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8777610702218770543962383 13166416053328155815943575)
              ·
                refine ⟨19749624079992233723915363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13166416053328155815943575 19749624079992233723915363)
                ·
                  refine ⟨29624436119988350585873045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19749624079992233723915363 29624436119988350585873045)
                  ·
                    refine ⟨1388645443124453933712799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29624436119988350585873045 1388645443124453933712799)
                    ·
                      rfl

theorem cell22_4056566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_4056566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056566 prefixEnd_4056566 := by exact prefixLift 4056566
  have htrace : WordTrace (prefixWord ++ tailWord_4056566) baseStart_4056566 baseEnd_4056566 := by
    simpa [prefixWord, tailWord_4056566, baseEnd_4056566] using wordTrace_append hprefix tailTrace_4056566
  have hstable : (prefixWord ++ tailWord_4056566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056566).length < 2 ^ (prefixWord ++ tailWord_4056566).sum := by decide
  have hdescent : baseEnd_4056566 < baseStart_4056566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056647 : List Nat := [1, 1, 4, 1, 5, 1, 3, 2, 1, 3]
def baseStart_4056647 : Nat := 118140960795 + 4056647 * 2 ^ 59
def prefixEnd_4056647 : Nat := 4983230072969 + 3 ^ 40 * 4056647 * 2
def baseEnd_4056647 : Nat := 1388673171079796722437551

theorem tailTrace_4056647 : CollatzResearch.WordTrace tailWord_4056647 prefixEnd_4056647 1388673171079796722437551 := by
  unfold tailWord_4056647
  simp only [CollatzResearch.WordTrace]
  refine ⟨147958071334468213994480195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98638714222978809329653463 147958071334468213994480195)
  ·
    refine ⟨221937107001702320991720293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147958071334468213994480195 221937107001702320991720293)
    ·
      refine ⟨41613207562819185185947555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 221937107001702320991720293 41613207562819185185947555)
      ·
        refine ⟨62419811344228777778921333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41613207562819185185947555 62419811344228777778921333)
        ·
          refine ⟨5851857313521447916773875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62419811344228777778921333 5851857313521447916773875)
          ·
            refine ⟨8777785970282171875160813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5851857313521447916773875 8777785970282171875160813)
            ·
              refine ⟨3291669738855814453185305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8777785970282171875160813 3291669738855814453185305)
              ·
                refine ⟨2468752304141860839888979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3291669738855814453185305 2468752304141860839888979)
                ·
                  refine ⟨3703128456212791259833469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468752304141860839888979 3703128456212791259833469)
                  ·
                    refine ⟨1388673171079796722437551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3703128456212791259833469 1388673171079796722437551)
                    ·
                      rfl

theorem cell22_4056647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_4056647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056647 prefixEnd_4056647 := by exact prefixLift 4056647
  have htrace : WordTrace (prefixWord ++ tailWord_4056647) baseStart_4056647 baseEnd_4056647 := by
    simpa [prefixWord, tailWord_4056647, baseEnd_4056647] using wordTrace_append hprefix tailTrace_4056647
  have hstable : (prefixWord ++ tailWord_4056647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056647).length < 2 ^ (prefixWord ++ tailWord_4056647).sum := by decide
  have hdescent : baseEnd_4056647 < baseStart_4056647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056690 : List Nat := [3, 2, 1, 2, 3, 2, 3, 1, 1, 4]
def baseStart_4056690 : Nat := 118140960795 + 4056690 * 2 ^ 59
def prefixEnd_4056690 : Nat := 4983230072969 + 3 ^ 40 * 4056690 * 2
def baseEnd_4056690 : Nat := 1388687890858558943612419

theorem tailTrace_4056690 : CollatzResearch.WordTrace tailWord_4056690 prefixEnd_4056690 1388687890858558943612419 := by
  unfold tailWord_4056690
  simp only [CollatzResearch.WordTrace]
  refine ⟨36989909918328108084573881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98639759782208288225530349 36989909918328108084573881)
  ·
    refine ⟨27742432438746081063430411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36989909918328108084573881 27742432438746081063430411)
    ·
      refine ⟨41613648658119121595145617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27742432438746081063430411 41613648658119121595145617)
      ·
        refine ⟨31210236493589341196359213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41613648658119121595145617 31210236493589341196359213)
        ·
          refine ⟨11703838685096002948634705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31210236493589341196359213 11703838685096002948634705)
          ·
            refine ⟨8777879013822002211476029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11703838685096002948634705 8777879013822002211476029)
            ·
              refine ⟨3291704630183250829303511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8777879013822002211476029 3291704630183250829303511)
              ·
                refine ⟨4937556945274876243955267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3291704630183250829303511 4937556945274876243955267)
                ·
                  refine ⟨7406335417912314365932901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4937556945274876243955267 7406335417912314365932901)
                  ·
                    refine ⟨1388687890858558943612419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7406335417912314365932901 1388687890858558943612419)
                    ·
                      rfl

theorem cell22_4056690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_4056690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056690 prefixEnd_4056690 := by exact prefixLift 4056690
  have htrace : WordTrace (prefixWord ++ tailWord_4056690) baseStart_4056690 baseEnd_4056690 := by
    simpa [prefixWord, tailWord_4056690, baseEnd_4056690] using wordTrace_append hprefix tailTrace_4056690
  have hstable : (prefixWord ++ tailWord_4056690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056690).length < 2 ^ (prefixWord ++ tailWord_4056690).sum := by decide
  have hdescent : baseEnd_4056690 < baseStart_4056690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056705 : List Nat := [1, 2, 4, 2, 1, 2, 4, 2, 4]
def baseStart_4056705 : Nat := 118140960795 + 4056705 * 2 ^ 59
def prefixEnd_4056705 : Nat := 4983230072969 + 3 ^ 40 * 4056705 * 2
def baseEnd_4056705 : Nat := 462897675221701301495791

theorem tailTrace_4056705 : CollatzResearch.WordTrace tailWord_4056705 prefixEnd_4056705 462897675221701301495791 := by
  unfold tailWord_4056705
  simp only [CollatzResearch.WordTrace]
  refine ⟨147960186768258089900091569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98640124512172059933394379 147960186768258089900091569)
  ·
    refine ⟨110970140076193567425068677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147960186768258089900091569 110970140076193567425068677)
    ·
      refine ⟨20806901264286293892200377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110970140076193567425068677 20806901264286293892200377)
      ·
        refine ⟨15605175948214720419150283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20806901264286293892200377 15605175948214720419150283)
        ·
          refine ⟨23407763922322080628725425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15605175948214720419150283 23407763922322080628725425)
          ·
            refine ⟨17555822941741560471544069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23407763922322080628725425 17555822941741560471544069)
            ·
              refine ⟨3291716801576542588414513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17555822941741560471544069 3291716801576542588414513)
              ·
                refine ⟨2468787601182406941310885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3291716801576542588414513 2468787601182406941310885)
                ·
                  refine ⟨462897675221701301495791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2468787601182406941310885 462897675221701301495791)
                  ·
                    rfl

theorem cell22_4056705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 2, 4].length) (baseStart_4056705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056705 prefixEnd_4056705 := by exact prefixLift 4056705
  have htrace : WordTrace (prefixWord ++ tailWord_4056705) baseStart_4056705 baseEnd_4056705 := by
    simpa [prefixWord, tailWord_4056705, baseEnd_4056705] using wordTrace_append hprefix tailTrace_4056705
  have hstable : (prefixWord ++ tailWord_4056705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056705).length < 2 ^ (prefixWord ++ tailWord_4056705).sum := by decide
  have hdescent : baseEnd_4056705 < baseStart_4056705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056765 : List Nat := [1, 4, 1, 2, 1, 2, 1, 6, 1, 3]
def baseStart_4056765 : Nat := 118140960795 + 4056765 * 2 ^ 59
def prefixEnd_4056765 : Nat := 4983230072969 + 3 ^ 40 * 4056765 * 2
def baseEnd_4056765 : Nat := 1388713564891283747987189

theorem tailTrace_4056765 : CollatzResearch.WordTrace tailWord_4056765 prefixEnd_4056765 1388713564891283747987189 := by
  unfold tailWord_4056765
  simp only [CollatzResearch.WordTrace]
  refine ⟨147962375148040720147275749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98641583432027146764850499 147962375148040720147275749)
  ·
    refine ⟨27742945340257635027614203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147962375148040720147275749 27742945340257635027614203)
    ·
      refine ⟨41614418010386452541421305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27742945340257635027614203 41614418010386452541421305)
      ·
        refine ⟨31210813507789839406065979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41614418010386452541421305 31210813507789839406065979)
        ·
          refine ⟨46816220261684759109098969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31210813507789839406065979 46816220261684759109098969)
          ·
            refine ⟨35112165196263569331824227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46816220261684759109098969 35112165196263569331824227)
            ·
              refine ⟨52668247794395353997736341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35112165196263569331824227 52668247794395353997736341)
              ·
                refine ⟨2468824115362282218643891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52668247794395353997736341 2468824115362282218643891)
                ·
                  refine ⟨3703236173043423327965837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468824115362282218643891 3703236173043423327965837)
                  ·
                    refine ⟨1388713564891283747987189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3703236173043423327965837 1388713564891283747987189)
                    ·
                      rfl

theorem cell22_4056765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_4056765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056765 prefixEnd_4056765 := by exact prefixLift 4056765
  have htrace : WordTrace (prefixWord ++ tailWord_4056765) baseStart_4056765 baseEnd_4056765 := by
    simpa [prefixWord, tailWord_4056765, baseEnd_4056765] using wordTrace_append hprefix tailTrace_4056765
  have hstable : (prefixWord ++ tailWord_4056765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056765).length < 2 ^ (prefixWord ++ tailWord_4056765).sum := by decide
  have hdescent : baseEnd_4056765 < baseStart_4056765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056776 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 2, 5]
def baseStart_4056776 : Nat := 118140960795 + 4056776 * 2 ^ 59
def prefixEnd_4056776 : Nat := 4983230072969 + 3 ^ 40 * 4056776 * 2
def baseEnd_4056776 : Nat := 1388717330416083385962155

theorem tailTrace_4056776 : CollatzResearch.WordTrace tailWord_4056776 prefixEnd_4056776 1388717330416083385962155 := by
  unfold tailWord_4056776
  simp only [CollatzResearch.WordTrace]
  refine ⟨73981388175500434512963091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98641850900667246017284121 73981388175500434512963091)
  ·
    refine ⟨110972082263250651769444637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73981388175500434512963091 110972082263250651769444637)
    ·
      refine ⟨41614530848718994413541739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110972082263250651769444637 41614530848718994413541739)
      ·
        refine ⟨62421796273078491620312609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41614530848718994413541739 62421796273078491620312609)
        ·
          refine ⟨46816347204808868715234457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62421796273078491620312609 46816347204808868715234457)
          ·
            refine ⟨35112260403606651536425843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46816347204808868715234457 35112260403606651536425843)
            ·
              refine ⟨52668390605409977304638765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35112260403606651536425843 52668390605409977304638765)
              ·
                refine ⟨19750646477028741489239537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52668390605409977304638765 19750646477028741489239537)
                ·
                  refine ⟨14812984857771556116929653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19750646477028741489239537 14812984857771556116929653)
                  ·
                    refine ⟨1388717330416083385962155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14812984857771556116929653 1388717330416083385962155)
                    ·
                      rfl

theorem cell22_4056776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 2, 5].length) (baseStart_4056776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056776 prefixEnd_4056776 := by exact prefixLift 4056776
  have htrace : WordTrace (prefixWord ++ tailWord_4056776) baseStart_4056776 baseEnd_4056776 := by
    simpa [prefixWord, tailWord_4056776, baseEnd_4056776] using wordTrace_append hprefix tailTrace_4056776
  have hstable : (prefixWord ++ tailWord_4056776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056776).length < 2 ^ (prefixWord ++ tailWord_4056776).sum := by decide
  have hdescent : baseEnd_4056776 < baseStart_4056776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056823 : List Nat := [1, 1, 3, 1, 1, 1, 4, 6, 4]
def baseStart_4056823 : Nat := 118140960795 + 4056823 * 2 ^ 59
def prefixEnd_4056823 : Nat := 4983230072969 + 3 ^ 40 * 4056823 * 2
def baseEnd_4056823 : Nat := 462911139825530310012337

theorem tailTrace_4056823 : CollatzResearch.WordTrace tailWord_4056823 prefixEnd_4056823 462911139825530310012337 := by
  unfold tailWord_4056823
  simp only [CollatzResearch.WordTrace]
  refine ⟨147964490581830596052887123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98642993721220397368591415 147964490581830596052887123)
  ·
    refine ⟨221946735872745894079330685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147964490581830596052887123 221946735872745894079330685)
    ·
      refine ⟨83230025952279710279749007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221946735872745894079330685 83230025952279710279749007)
      ·
        refine ⟨124845038928419565419623511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83230025952279710279749007 124845038928419565419623511)
        ·
          refine ⟨187267558392629348129435267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124845038928419565419623511 187267558392629348129435267)
          ·
            refine ⟨280901337588944022194152901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187267558392629348129435267 280901337588944022194152901)
            ·
              refine ⟨52669000797927004161403669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 280901337588944022194152901 52669000797927004161403669)
              ·
                refine ⟨2468859412402828320065797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52669000797927004161403669 2468859412402828320065797)
                ·
                  refine ⟨462911139825530310012337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2468859412402828320065797 462911139825530310012337)
                  ·
                    rfl

theorem cell22_4056823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 4].length) (baseStart_4056823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056823 prefixEnd_4056823 := by exact prefixLift 4056823
  have htrace : WordTrace (prefixWord ++ tailWord_4056823) baseStart_4056823 baseEnd_4056823 := by
    simpa [prefixWord, tailWord_4056823, baseEnd_4056823] using wordTrace_append hprefix tailTrace_4056823
  have hstable : (prefixWord ++ tailWord_4056823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056823).length < 2 ^ (prefixWord ++ tailWord_4056823).sum := by decide
  have hdescent : baseEnd_4056823 < baseStart_4056823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056853 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 2, 4]
def baseStart_4056853 : Nat := 118140960795 + 4056853 * 2 ^ 59
def prefixEnd_4056853 : Nat := 4983230072969 + 3 ^ 40 * 4056853 * 2
def baseEnd_4056853 : Nat := 1388743689089680851786919

theorem tailTrace_4056853 : CollatzResearch.WordTrace tailWord_4056853 prefixEnd_4056853 1388743689089680851786919 := by
  unfold tailWord_4056853
  simp only [CollatzResearch.WordTrace]
  refine ⟨147965584771721911176479213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98643723181147940784319475 147965584771721911176479213)
  ·
    refine ⟨55487094289395716691179705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147965584771721911176479213 55487094289395716691179705)
    ·
      refine ⟨41615320717046787518384779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55487094289395716691179705 41615320717046787518384779)
      ·
        refine ⟨62422981075570181277577169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41615320717046787518384779 62422981075570181277577169)
        ·
          refine ⟨46817235806677635958182877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62422981075570181277577169 46817235806677635958182877)
          ·
            refine ⟨17556463427504113484318579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46817235806677635958182877 17556463427504113484318579)
            ·
              refine ⟨26334695141256170226477869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17556463427504113484318579 26334695141256170226477869)
              ·
                refine ⟨9875510677971063834929201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26334695141256170226477869 9875510677971063834929201)
                ·
                  refine ⟨7406633008478297876196901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9875510677971063834929201 7406633008478297876196901)
                  ·
                    refine ⟨1388743689089680851786919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7406633008478297876196901 1388743689089680851786919)
                    ·
                      rfl

theorem cell22_4056853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_4056853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056853 prefixEnd_4056853 := by exact prefixLift 4056853
  have htrace : WordTrace (prefixWord ++ tailWord_4056853) baseStart_4056853 baseEnd_4056853 := by
    simpa [prefixWord, tailWord_4056853, baseEnd_4056853] using wordTrace_append hprefix tailTrace_4056853
  have hstable : (prefixWord ++ tailWord_4056853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056853).length < 2 ^ (prefixWord ++ tailWord_4056853).sum := by decide
  have hdescent : baseEnd_4056853 < baseStart_4056853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056872 : List Nat := [2, 1, 5, 1, 1, 3, 2, 2, 2, 3]
def baseStart_4056872 : Nat := 118140960795 + 4056872 * 2 ^ 59
def prefixEnd_4056872 : Nat := 4983230072969 + 3 ^ 40 * 4056872 * 2
def baseEnd_4056872 : Nat := 1388750193177971135561861

theorem tailTrace_4056872 : CollatzResearch.WordTrace tailWord_4056872 prefixEnd_4056872 1388750193177971135561861 := by
  unfold tailWord_4056872
  simp only [CollatzResearch.WordTrace]
  refine ⟨73983138879326538710710435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98644185172435384947613913 73983138879326538710710435)
  ·
    refine ⟨110974708318989808066065653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73983138879326538710710435 110974708318989808066065653)
    ·
      refine ⟨10403878904905294506193655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 110974708318989808066065653 10403878904905294506193655)
      ·
        refine ⟨15605818357357941759290483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10403878904905294506193655 15605818357357941759290483)
        ·
          refine ⟨23408727536036912638935725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15605818357357941759290483 23408727536036912638935725)
          ·
            refine ⟨8778272826013842239600897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23408727536036912638935725 8778272826013842239600897)
            ·
              refine ⟨6583704619510381679700673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8778272826013842239600897 6583704619510381679700673)
              ·
                refine ⟨4937778464632786259775505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6583704619510381679700673 4937778464632786259775505)
                ·
                  refine ⟨3703333848474589694831629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4937778464632786259775505 3703333848474589694831629)
                  ·
                    refine ⟨1388750193177971135561861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3703333848474589694831629 1388750193177971135561861)
                    ·
                      rfl

theorem cell22_4056872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_4056872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056872 prefixEnd_4056872 := by exact prefixLift 4056872
  have htrace : WordTrace (prefixWord ++ tailWord_4056872) baseStart_4056872 baseEnd_4056872 := by
    simpa [prefixWord, tailWord_4056872, baseEnd_4056872] using wordTrace_append hprefix tailTrace_4056872
  have hstable : (prefixWord ++ tailWord_4056872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056872).length < 2 ^ (prefixWord ++ tailWord_4056872).sum := by decide
  have hdescent : baseEnd_4056872 < baseStart_4056872 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056885 : List Nat := [1, 3, 3, 1, 4, 2, 1, 7]
def baseStart_4056885 : Nat := 118140960795 + 4056885 * 2 ^ 59
def prefixEnd_4056885 : Nat := 4983230072969 + 3 ^ 40 * 4056885 * 2
def baseEnd_4056885 : Nat := 154306071482627048331869

theorem tailTrace_4056885 : CollatzResearch.WordTrace tailWord_4056885 prefixEnd_4056885 154306071482627048331869 := by
  unfold tailWord_4056885
  simp only [CollatzResearch.WordTrace]
  refine ⟨147966751907605980641644109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98644501271737320427762739 147966751907605980641644109)
  ·
    refine ⟨55487531965352242740616541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147966751907605980641644109 55487531965352242740616541)
    ·
      refine ⟨20807824487007091027731203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55487531965352242740616541 20807824487007091027731203)
      ·
        refine ⟨31211736730510636541596805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20807824487007091027731203 31211736730510636541596805)
        ·
          refine ⟨5852200636970744351549401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31211736730510636541596805 5852200636970744351549401)
          ·
            refine ⟨4389150477728058263662051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5852200636970744351549401 4389150477728058263662051)
            ·
              refine ⟨6583725716592087395493077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4389150477728058263662051 6583725716592087395493077)
              ·
                refine ⟨154306071482627048331869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6583725716592087395493077 154306071482627048331869)
                ·
                  rfl

theorem cell22_4056885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 7].length) (baseStart_4056885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056885 prefixEnd_4056885 := by exact prefixLift 4056885
  have htrace : WordTrace (prefixWord ++ tailWord_4056885) baseStart_4056885 baseEnd_4056885 := by
    simpa [prefixWord, tailWord_4056885, baseEnd_4056885] using wordTrace_append hprefix tailTrace_4056885
  have hstable : (prefixWord ++ tailWord_4056885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056885).length < 2 ^ (prefixWord ++ tailWord_4056885).sum := by decide
  have hdescent : baseEnd_4056885 < baseStart_4056885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056896 : List Nat := [2, 1, 1, 2, 2, 1, 1, 1, 11]
def baseStart_4056896 : Nat := 118140960795 + 4056896 * 2 ^ 59
def prefixEnd_4056896 : Nat := 4983230072969 + 3 ^ 40 * 4056896 * 2
def baseEnd_4056896 : Nat := 462919469622814357653929

theorem tailTrace_4056896 : CollatzResearch.WordTrace tailWord_4056896 prefixEnd_4056896 462919469622814357653929 := by
  unfold tailWord_4056896
  simp only [CollatzResearch.WordTrace]
  refine ⟨73983576555283064760147271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98644768740377419680196361 73983576555283064760147271)
  ·
    refine ⟨110975364832924597140220907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73983576555283064760147271 110975364832924597140220907)
    ·
      refine ⟨166463047249386895710331361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110975364832924597140220907 166463047249386895710331361)
      ·
        refine ⟨124847285437040171782748521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166463047249386895710331361 124847285437040171782748521)
        ·
          refine ⟨93635464077780128837061391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124847285437040171782748521 93635464077780128837061391)
          ·
            refine ⟨140453196116670193255592087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93635464077780128837061391 140453196116670193255592087)
            ·
              refine ⟨210679794175005289883388131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140453196116670193255592087 210679794175005289883388131)
              ·
                refine ⟨316019691262507934825082197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210679794175005289883388131 316019691262507934825082197)
                ·
                  refine ⟨462919469622814357653929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 316019691262507934825082197 462919469622814357653929)
                  ·
                    rfl

theorem cell22_4056896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 11].length) (baseStart_4056896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056896 prefixEnd_4056896 := by exact prefixLift 4056896
  have htrace : WordTrace (prefixWord ++ tailWord_4056896) baseStart_4056896 baseEnd_4056896 := by
    simpa [prefixWord, tailWord_4056896, baseEnd_4056896] using wordTrace_append hprefix tailTrace_4056896
  have hstable : (prefixWord ++ tailWord_4056896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056896).length < 2 ^ (prefixWord ++ tailWord_4056896).sum := by decide
  have hdescent : baseEnd_4056896 < baseStart_4056896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056917 : List Nat := [1, 3, 2, 2, 2, 2, 1, 5, 1, 3]
def baseStart_4056917 : Nat := 118140960795 + 4056917 * 2 ^ 59
def prefixEnd_4056917 : Nat := 4983230072969 + 3 ^ 40 * 4056917 * 2
def baseEnd_4056917 : Nat := 1388765597597606018186723

theorem tailTrace_4056917 : CollatzResearch.WordTrace tailWord_4056917 prefixEnd_4056917 1388765597597606018186723 := by
  unfold tailWord_4056917
  simp only [CollatzResearch.WordTrace]
  refine ⟨147967919043490050106809005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98645279362326700071206003 147967919043490050106809005)
  ·
    refine ⟨55487969641308768790053377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147967919043490050106809005 55487969641308768790053377)
    ·
      refine ⟨41615977230981576592540033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55487969641308768790053377 41615977230981576592540033)
      ·
        refine ⟨31211982923236182444405025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41615977230981576592540033 31211982923236182444405025)
        ·
          refine ⟨23408987192427136833303769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31211982923236182444405025 23408987192427136833303769)
          ·
            refine ⟨17556740394320352624977827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23408987192427136833303769 17556740394320352624977827)
            ·
              refine ⟨26335110591480528937466741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17556740394320352624977827 26335110591480528937466741)
              ·
                refine ⟨2468916617951299587887507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26335110591480528937466741 2468916617951299587887507)
                ·
                  refine ⟨3703374926926949381831261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2468916617951299587887507 3703374926926949381831261)
                  ·
                    refine ⟨1388765597597606018186723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3703374926926949381831261 1388765597597606018186723)
                    ·
                      rfl

theorem cell22_4056917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_4056917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056917 prefixEnd_4056917 := by exact prefixLift 4056917
  have htrace : WordTrace (prefixWord ++ tailWord_4056917) baseStart_4056917 baseEnd_4056917 := by
    simpa [prefixWord, tailWord_4056917, baseEnd_4056917] using wordTrace_append hprefix tailTrace_4056917
  have hstable : (prefixWord ++ tailWord_4056917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056917).length < 2 ^ (prefixWord ++ tailWord_4056917).sum := by decide
  have hdescent : baseEnd_4056917 < baseStart_4056917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056928 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 2, 5]
def baseStart_4056928 : Nat := 118140960795 + 4056928 * 2 ^ 59
def prefixEnd_4056928 : Nat := 4983230072969 + 3 ^ 40 * 4056928 * 2
def baseEnd_4056928 : Nat := 1388769363122405656161689

theorem tailTrace_4056928 : CollatzResearch.WordTrace tailWord_4056928 prefixEnd_4056928 1388769363122405656161689 := by
  unfold tailWord_4056928
  simp only [CollatzResearch.WordTrace]
  refine ⟨73984160123225099492729719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98645546830966799323639625 73984160123225099492729719)
  ·
    refine ⟨110976240184837649239094579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73984160123225099492729719 110976240184837649239094579)
    ·
      refine ⟨166464360277256473858641869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110976240184837649239094579 166464360277256473858641869)
      ·
        refine ⟨62424135103971177696990701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166464360277256473858641869 62424135103971177696990701)
        ·
          refine ⟨23409050663989191636371513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62424135103971177696990701 23409050663989191636371513)
          ·
            refine ⟨17556787997991893727278635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23409050663989191636371513 17556787997991893727278635)
            ·
              refine ⟨26335181996987840590917953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17556787997991893727278635 26335181996987840590917953)
              ·
                refine ⟨19751386497740880443188465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26335181996987840590917953 19751386497740880443188465)
                ·
                  refine ⟨14813539873305660332391349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19751386497740880443188465 14813539873305660332391349)
                  ·
                    refine ⟨1388769363122405656161689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14813539873305660332391349 1388769363122405656161689)
                    ·
                      rfl

theorem cell22_4056928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 2, 5].length) (baseStart_4056928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056928 prefixEnd_4056928 := by exact prefixLift 4056928
  have htrace : WordTrace (prefixWord ++ tailWord_4056928) baseStart_4056928 baseEnd_4056928 := by
    simpa [prefixWord, tailWord_4056928, baseEnd_4056928] using wordTrace_append hprefix tailTrace_4056928
  have hstable : (prefixWord ++ tailWord_4056928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056928).length < 2 ^ (prefixWord ++ tailWord_4056928).sum := by decide
  have hdescent : baseEnd_4056928 < baseStart_4056928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056930 : List Nat := [3, 3, 2, 1, 2, 2, 1, 1, 7]
def baseStart_4056930 : Nat := 118140960795 + 4056930 * 2 ^ 59
def prefixEnd_4056930 : Nat := 4983230072969 + 3 ^ 40 * 4056930 * 2
def baseEnd_4056930 : Nat := 462923349254426105870561

theorem tailTrace_4056930 : CollatzResearch.WordTrace tailWord_4056930 prefixEnd_4056930 462923349254426105870561 := by
  unfold tailWord_4056930
  simp only [CollatzResearch.WordTrace]
  refine ⟨36992098298110738331758061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98645595461628635551354829 36992098298110738331758061)
  ·
    refine ⟨13872036861791526874409273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36992098298110738331758061 13872036861791526874409273)
    ·
      refine ⟨10404027646343645155806955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13872036861791526874409273 10404027646343645155806955)
      ·
        refine ⟨15606041469515467733710433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10404027646343645155806955 15606041469515467733710433)
        ·
          refine ⟨11704531102136600800282825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15606041469515467733710433 11704531102136600800282825)
          ·
            refine ⟨8778398326602450600212119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11704531102136600800282825 8778398326602450600212119)
            ·
              refine ⟨13167597489903675900318179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8778398326602450600212119 13167597489903675900318179)
              ·
                refine ⟨19751396234855513850477269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13167597489903675900318179 19751396234855513850477269)
                ·
                  refine ⟨462923349254426105870561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19751396234855513850477269 462923349254426105870561)
                  ·
                    rfl

theorem cell22_4056930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_4056930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056930 prefixEnd_4056930 := by exact prefixLift 4056930
  have htrace : WordTrace (prefixWord ++ tailWord_4056930) baseStart_4056930 baseEnd_4056930 := by
    simpa [prefixWord, tailWord_4056930, baseEnd_4056930] using wordTrace_append hprefix tailTrace_4056930
  have hstable : (prefixWord ++ tailWord_4056930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056930).length < 2 ^ (prefixWord ++ tailWord_4056930).sum := by decide
  have hdescent : baseEnd_4056930 < baseStart_4056930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4056960 : List Nat := [2, 1, 1, 2, 1, 2, 6, 2, 1, 4]
def baseStart_4056960 : Nat := 118140960795 + 4056960 * 2 ^ 59
def prefixEnd_4056960 : Nat := 4983230072969 + 3 ^ 40 * 4056960 * 2
def baseEnd_4056960 : Nat := 1388780317376368239361591

theorem tailTrace_4056960 : CollatzResearch.WordTrace tailWord_4056960 prefixEnd_4056960 1388780317376368239361591 := by
  unfold tailWord_4056960
  simp only [CollatzResearch.WordTrace]
  refine ⟨73984743691167134225312167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98646324921556178967082889 73984743691167134225312167)
  ·
    refine ⟨110977115536750701337968251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73984743691167134225312167 110977115536750701337968251)
    ·
      refine ⟨166465673305126052006952377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110977115536750701337968251 166465673305126052006952377)
      ·
        refine ⟨124849254978844539005214283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166465673305126052006952377 124849254978844539005214283)
        ·
          refine ⟨187273882468266808507821425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124849254978844539005214283 187273882468266808507821425)
          ·
            refine ⟨140455411851200106380866069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187273882468266808507821425 140455411851200106380866069)
            ·
              refine ⟨6583847430525004986603097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140455411851200106380866069 6583847430525004986603097)
              ·
                refine ⟨4937885572893753739952323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6583847430525004986603097 4937885572893753739952323)
                ·
                  refine ⟨7406828359340630609928485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4937885572893753739952323 7406828359340630609928485)
                  ·
                    refine ⟨1388780317376368239361591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7406828359340630609928485 1388780317376368239361591)
                    ·
                      rfl

theorem cell22_4056960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 1, 4].length) (baseStart_4056960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4056960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4056960 prefixEnd_4056960 := by exact prefixLift 4056960
  have htrace : WordTrace (prefixWord ++ tailWord_4056960) baseStart_4056960 baseEnd_4056960 := by
    simpa [prefixWord, tailWord_4056960, baseEnd_4056960] using wordTrace_append hprefix tailTrace_4056960
  have hstable : (prefixWord ++ tailWord_4056960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4056960).length < 2 ^ (prefixWord ++ tailWord_4056960).sum := by decide
  have hdescent : baseEnd_4056960 < baseStart_4056960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4056960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057022 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_4057022 : Nat := 118140960795 + 4057022 * 2 ^ 59
def prefixEnd_4057022 : Nat := 4983230072969 + 3 ^ 40 * 4057022 * 2
def baseEnd_4057022 : Nat := 1388801541243420744311401

theorem tailTrace_4057022 : CollatzResearch.WordTrace tailWord_4057022 prefixEnd_4057022 1388801541243420744311401 := by
  unfold tailWord_4057022
  simp only [CollatzResearch.WordTrace]
  refine ⟨18496468588513706629922665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98647832472073102026254213 18496468588513706629922665)
  ·
    refine ⟨13872351441385279972441999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18496468588513706629922665 13872351441385279972441999)
    ·
      refine ⟨20808527162077919958662999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13872351441385279972441999 20808527162077919958662999)
      ·
        refine ⟨31212790743116879937994499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20808527162077919958662999 31212790743116879937994499)
        ·
          refine ⟨46819186114675319906991749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31212790743116879937994499 46819186114675319906991749)
          ·
            refine ⟨8778597396501622482560953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46819186114675319906991749 8778597396501622482560953)
            ·
              refine ⟨6583948047376216861920715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8778597396501622482560953 6583948047376216861920715)
              ·
                refine ⟨9875922071064325292881073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6583948047376216861920715 9875922071064325292881073)
                ·
                  refine ⟨7406941553298243969660805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9875922071064325292881073 7406941553298243969660805)
                  ·
                    refine ⟨1388801541243420744311401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7406941553298243969660805 1388801541243420744311401)
                    ·
                      rfl

theorem cell22_4057022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_4057022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057022 prefixEnd_4057022 := by exact prefixLift 4057022
  have htrace : WordTrace (prefixWord ++ tailWord_4057022) baseStart_4057022 baseEnd_4057022 := by
    simpa [prefixWord, tailWord_4057022, baseEnd_4057022] using wordTrace_append hprefix tailTrace_4057022
  have hstable : (prefixWord ++ tailWord_4057022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057022).length < 2 ^ (prefixWord ++ tailWord_4057022).sum := by decide
  have hdescent : baseEnd_4057022 < baseStart_4057022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057086 : List Nat := [4, 2, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_4057086 : Nat := 118140960795 + 4057086 * 2 ^ 59
def prefixEnd_4057086 : Nat := 4983230072969 + 3 ^ 40 * 4057086 * 2
def baseEnd_4057086 : Nat := 1388823449751345910711205

theorem tailTrace_4057086 : CollatzResearch.WordTrace tailWord_4057086 prefixEnd_4057086 1388823449751345910711205 := by
  unfold tailWord_4057086
  simp only [CollatzResearch.WordTrace]
  refine ⟨18496760372484723996213889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98649388653251861313140741 18496760372484723996213889)
  ·
    refine ⟨13872570279363542997160417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18496760372484723996213889 13872570279363542997160417)
    ·
      refine ⟨10404427709522657247870313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13872570279363542997160417 10404427709522657247870313)
      ·
        refine ⟨7803320782141992935902735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10404427709522657247870313 7803320782141992935902735)
        ·
          refine ⟨11704981173212989403854103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7803320782141992935902735 11704981173212989403854103)
          ·
            refine ⟨17557471759819484105781155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11704981173212989403854103 17557471759819484105781155)
            ·
              refine ⟨26336207639729226158671733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17557471759819484105781155 26336207639729226158671733)
              ·
                refine ⟨2469019466224614952375475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26336207639729226158671733 2469019466224614952375475)
                ·
                  refine ⟨3703529199336922428563213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469019466224614952375475 3703529199336922428563213)
                  ·
                    refine ⟨1388823449751345910711205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3703529199336922428563213 1388823449751345910711205)
                    ·
                      rfl

theorem cell22_4057086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_4057086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057086 prefixEnd_4057086 := by exact prefixLift 4057086
  have htrace : WordTrace (prefixWord ++ tailWord_4057086) baseStart_4057086 baseEnd_4057086 := by
    simpa [prefixWord, tailWord_4057086, baseEnd_4057086] using wordTrace_append hprefix tailTrace_4057086
  have hstable : (prefixWord ++ tailWord_4057086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057086).length < 2 ^ (prefixWord ++ tailWord_4057086).sum := by decide
  have hdescent : baseEnd_4057086 < baseStart_4057086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057142 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 3, 5]
def baseStart_4057142 : Nat := 118140960795 + 4057142 * 2 ^ 59
def prefixEnd_4057142 : Nat := 4983230072969 + 3 ^ 40 * 4057142 * 2
def baseEnd_4057142 : Nat := 1388842619695780431311033

theorem tailTrace_4057142 : CollatzResearch.WordTrace tailWord_4057142 prefixEnd_4057142 1388842619695780431311033 := by
  unfold tailWord_4057142
  simp only [CollatzResearch.WordTrace]
  refine ⟨9248507841729682095859355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98650750311783275689166453 9248507841729682095859355)
  ·
    refine ⟨13872761762594523143789033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9248507841729682095859355 13872761762594523143789033)
    ·
      refine ⟨10404571321945892357841775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13872761762594523143789033 10404571321945892357841775)
      ·
        refine ⟨15606856982918838536762663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10404571321945892357841775 15606856982918838536762663)
        ·
          refine ⟨23410285474378257805143995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15606856982918838536762663 23410285474378257805143995)
          ·
            refine ⟨35115428211567386707715993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23410285474378257805143995 35115428211567386707715993)
            ·
              refine ⟨26336571158675540030786995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35115428211567386707715993 26336571158675540030786995)
              ·
                refine ⟨39504856738013310046180493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26336571158675540030786995 39504856738013310046180493)
                ·
                  refine ⟨14814321276754991267317685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39504856738013310046180493 14814321276754991267317685)
                  ·
                    refine ⟨1388842619695780431311033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14814321276754991267317685 1388842619695780431311033)
                    ·
                      rfl

theorem cell22_4057142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_4057142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057142 prefixEnd_4057142 := by exact prefixLift 4057142
  have htrace : WordTrace (prefixWord ++ tailWord_4057142) baseStart_4057142 baseEnd_4057142 := by
    simpa [prefixWord, tailWord_4057142, baseEnd_4057142] using wordTrace_append hprefix tailTrace_4057142
  have hstable : (prefixWord ++ tailWord_4057142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057142).length < 2 ^ (prefixWord ++ tailWord_4057142).sum := by decide
  have hdescent : baseEnd_4057142 < baseStart_4057142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057176 : List Nat := [2, 1, 2, 2, 1, 6, 2, 1, 2, 3]
def baseStart_4057176 : Nat := 118140960795 + 4057176 * 2 ^ 59
def prefixEnd_4057176 : Nat := 4983230072969 + 3 ^ 40 * 4057176 * 2
def baseEnd_4057176 : Nat := 1388854258590615675960929

theorem tailTrace_4057176 : CollatzResearch.WordTrace tailWord_4057176 prefixEnd_4057176 1388854258590615675960929 := by
  unfold tailWord_4057176
  simp only [CollatzResearch.WordTrace]
  refine ⟨73988682774775868670243691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98651577033034491560324921 73988682774775868670243691)
  ·
    refine ⟨110983024162163803005365537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73988682774775868670243691 110983024162163803005365537)
    ·
      refine ⟨83237268121622852254024153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110983024162163803005365537 83237268121622852254024153)
      ·
        refine ⟨62427951091217139190518115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83237268121622852254024153 62427951091217139190518115)
        ·
          refine ⟨93641926636825708785777173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62427951091217139190518115 93641926636825708785777173)
          ·
            refine ⟨4389465311101205099333305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93641926636825708785777173 4389465311101205099333305)
            ·
              refine ⟨3292098983325903824499979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4389465311101205099333305 3292098983325903824499979)
              ·
                refine ⟨4938148474988855736749969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3292098983325903824499979 4938148474988855736749969)
                ·
                  refine ⟨3703611356241641802562477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4938148474988855736749969 3703611356241641802562477)
                  ·
                    refine ⟨1388854258590615675960929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3703611356241641802562477 1388854258590615675960929)
                    ·
                      rfl

theorem cell22_4057176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 1, 2, 3].length) (baseStart_4057176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057176 prefixEnd_4057176 := by exact prefixLift 4057176
  have htrace : WordTrace (prefixWord ++ tailWord_4057176) baseStart_4057176 baseEnd_4057176 := by
    simpa [prefixWord, tailWord_4057176, baseEnd_4057176] using wordTrace_append hprefix tailTrace_4057176
  have hstable : (prefixWord ++ tailWord_4057176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057176).length < 2 ^ (prefixWord ++ tailWord_4057176).sum := by decide
  have hdescent : baseEnd_4057176 < baseStart_4057176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057187 : List Nat := [1, 1, 1, 5, 1, 1, 2, 4, 3, 3]
def baseStart_4057187 : Nat := 118140960795 + 4057187 * 2 ^ 59
def prefixEnd_4057187 : Nat := 4983230072969 + 3 ^ 40 * 4057187 * 2
def baseEnd_4057187 : Nat := 1388858024115415313935895

theorem tailTrace_4057187 : CollatzResearch.WordTrace tailWord_4057187 prefixEnd_4057187 1388858024115415313935895 := by
  unfold tailWord_4057187
  simp only [CollatzResearch.WordTrace]
  refine ⟨147977766752511886219137815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98651844501674590812758543 147977766752511886219137815)
  ·
    refine ⟨221966650128767829328706723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147977766752511886219137815 221966650128767829328706723)
    ·
      refine ⟨332949975193151743993060085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221966650128767829328706723 332949975193151743993060085)
      ·
        refine ⟨31214060174357975999349383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 332949975193151743993060085 31214060174357975999349383)
        ·
          refine ⟨46821090261536963999024075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31214060174357975999349383 46821090261536963999024075)
          ·
            refine ⟨70231635392305445998536113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46821090261536963999024075 70231635392305445998536113)
            ·
              refine ⟨52673726544229084498902085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70231635392305445998536113 52673726544229084498902085)
              ·
                refine ⟨9876323727042953343544141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52673726544229084498902085 9876323727042953343544141)
                ·
                  refine ⟨3703621397641107503829053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9876323727042953343544141 3703621397641107503829053)
                  ·
                    refine ⟨1388858024115415313935895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3703621397641107503829053 1388858024115415313935895)
                    ·
                      rfl

theorem cell22_4057187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 3].length) (baseStart_4057187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057187 prefixEnd_4057187 := by exact prefixLift 4057187
  have htrace : WordTrace (prefixWord ++ tailWord_4057187) baseStart_4057187 baseEnd_4057187 := by
    simpa [prefixWord, tailWord_4057187, baseEnd_4057187] using wordTrace_append hprefix tailTrace_4057187
  have hstable : (prefixWord ++ tailWord_4057187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057187).length < 2 ^ (prefixWord ++ tailWord_4057187).sum := by decide
  have hdescent : baseEnd_4057187 < baseStart_4057187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057221 : List Nat := [1, 3, 1, 1, 5, 2, 1, 4, 1, 3]
def baseStart_4057221 : Nat := 118140960795 + 4057221 * 2 ^ 59
def prefixEnd_4057221 : Nat := 4983230072969 + 3 ^ 40 * 4057221 * 2
def baseEnd_4057221 : Nat := 1388869663010250558585791

theorem tailTrace_4057221 : CollatzResearch.WordTrace tailWord_4057221 prefixEnd_4057221 1388869663010250558585791 := by
  unfold tailWord_4057221
  simp only [CollatzResearch.WordTrace]
  refine ⟨147979006834388710025875517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98652671222925806683917011 147979006834388710025875517)
  ·
    refine ⟨55492127562895766259703319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147979006834388710025875517 55492127562895766259703319)
    ·
      refine ⟨83238191344343649389554979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55492127562895766259703319 83238191344343649389554979)
      ·
        refine ⟨124857287016515474084332469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83238191344343649389554979 124857287016515474084332469)
        ·
          refine ⟨11705370657798325695406169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124857287016515474084332469 11705370657798325695406169)
          ·
            refine ⟨8779027993348744271554627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11705370657798325695406169 8779027993348744271554627)
            ·
              refine ⟨13168541990023116407331941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8779027993348744271554627 13168541990023116407331941)
              ·
                refine ⟨2469101623129334326374739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13168541990023116407331941 2469101623129334326374739)
                ·
                  refine ⟨3703652434694001489562109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469101623129334326374739 3703652434694001489562109)
                  ·
                    refine ⟨1388869663010250558585791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3703652434694001489562109 1388869663010250558585791)
                    ·
                      rfl

theorem cell22_4057221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_4057221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057221 prefixEnd_4057221 := by exact prefixLift 4057221
  have htrace : WordTrace (prefixWord ++ tailWord_4057221) baseStart_4057221 baseEnd_4057221 := by
    simpa [prefixWord, tailWord_4057221, baseEnd_4057221] using wordTrace_append hprefix tailTrace_4057221
  have hstable : (prefixWord ++ tailWord_4057221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057221).length < 2 ^ (prefixWord ++ tailWord_4057221).sum := by decide
  have hdescent : baseEnd_4057221 < baseStart_4057221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057260 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 2, 9]
def baseStart_4057260 : Nat := 118140960795 + 4057260 * 2 ^ 59
def prefixEnd_4057260 : Nat := 4983230072969 + 3 ^ 40 * 4057260 * 2
def baseEnd_4057260 : Nat := 1388883013507267456860671

theorem tailTrace_4057260 : CollatzResearch.WordTrace tailWord_4057260 prefixEnd_4057260 1388883013507267456860671 := by
  unfold tailWord_4057260
  simp only [CollatzResearch.WordTrace]
  refine ⟨73990214640623709843272617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98653619520831613124363489 73990214640623709843272617)
  ·
    refine ⟨55492660980467782382454463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73990214640623709843272617 55492660980467782382454463)
    ·
      refine ⟨83238991470701673573681695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55492660980467782382454463 83238991470701673573681695)
      ·
        refine ⟨124858487206052510360522543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83238991470701673573681695 124858487206052510360522543)
        ·
          refine ⟨187287730809078765540783815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124858487206052510360522543 187287730809078765540783815)
          ·
            refine ⟨280931596213618148311175723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187287730809078765540783815 280931596213618148311175723)
            ·
              refine ⟨421397394320427222466763585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280931596213618148311175723 421397394320427222466763585)
              ·
                refine ⟨316048045740320416850072689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421397394320427222466763585 316048045740320416850072689)
                ·
                  refine ⟨237036034305240312637554517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316048045740320416850072689 237036034305240312637554517)
                  ·
                    refine ⟨1388883013507267456860671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 237036034305240312637554517 1388883013507267456860671)
                    ·
                      rfl

theorem cell22_4057260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 9].length) (baseStart_4057260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057260 prefixEnd_4057260 := by exact prefixLift 4057260
  have htrace : WordTrace (prefixWord ++ tailWord_4057260) baseStart_4057260 baseEnd_4057260 := by
    simpa [prefixWord, tailWord_4057260, baseEnd_4057260] using wordTrace_append hprefix tailTrace_4057260
  have hstable : (prefixWord ++ tailWord_4057260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057260).length < 2 ^ (prefixWord ++ tailWord_4057260).sum := by decide
  have hdescent : baseEnd_4057260 < baseStart_4057260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057268 : List Nat := [2, 5, 3, 1, 1, 1, 1, 1, 7]
def baseStart_4057268 : Nat := 118140960795 + 4057268 * 2 ^ 59
def prefixEnd_4057268 : Nat := 4983230072969 + 3 ^ 40 * 4057268 * 2
def baseEnd_4057268 : Nat := 462961917356919367553549

theorem tailTrace_4057268 : CollatzResearch.WordTrace tailWord_4057268 prefixEnd_4057268 462961917356919367553549 := by
  unfold tailWord_4057268
  simp only [CollatzResearch.WordTrace]
  refine ⟨73990360532609218526418229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98653814043478958035224305 73990360532609218526418229)
  ·
    refine ⟨6936596299932114236851709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73990360532609218526418229 6936596299932114236851709)
    ·
      refine ⟨2601223612474542838819391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6936596299932114236851709 2601223612474542838819391)
      ·
        refine ⟨3901835418711814258229087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2601223612474542838819391 3901835418711814258229087)
        ·
          refine ⟨5852753128067721387343631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3901835418711814258229087 5852753128067721387343631)
          ·
            refine ⟨8779129692101582081015447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5852753128067721387343631 8779129692101582081015447)
            ·
              refine ⟨13168694538152373121523171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8779129692101582081015447 13168694538152373121523171)
              ·
                refine ⟨19753041807228559682284757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13168694538152373121523171 19753041807228559682284757)
                ·
                  refine ⟨462961917356919367553549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19753041807228559682284757 462961917356919367553549)
                  ·
                    rfl

theorem cell22_4057268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_4057268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057268 prefixEnd_4057268 := by exact prefixLift 4057268
  have htrace : WordTrace (prefixWord ++ tailWord_4057268) baseStart_4057268 baseEnd_4057268 := by
    simpa [prefixWord, tailWord_4057268, baseEnd_4057268] using wordTrace_append hprefix tailTrace_4057268
  have hstable : (prefixWord ++ tailWord_4057268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057268).length < 2 ^ (prefixWord ++ tailWord_4057268).sum := by decide
  have hdescent : baseEnd_4057268 < baseStart_4057268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057294 : List Nat := [4, 1, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_4057294 : Nat := 118140960795 + 4057294 * 2 ^ 59
def prefixEnd_4057294 : Nat := 4983230072969 + 3 ^ 40 * 4057294 * 2
def baseEnd_4057294 : Nat := 1388894652402102701510567

theorem tailTrace_4057294 : CollatzResearch.WordTrace tailWord_4057294 prefixEnd_4057294 1388894652402102701510567 := by
  unfold tailWord_4057294
  simp only [CollatzResearch.WordTrace]
  refine ⟨18497708670390530436660367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98654446242082828995521957 18497708670390530436660367)
  ·
    refine ⟨27746563005585795654990551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18497708670390530436660367 27746563005585795654990551)
    ·
      refine ⟨41619844508378693482485827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27746563005585795654990551 41619844508378693482485827)
      ·
        refine ⟨62429766762568040223728741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41619844508378693482485827 62429766762568040223728741)
        ·
          refine ⟨11705581267981507541949139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62429766762568040223728741 11705581267981507541949139)
          ·
            refine ⟨17558371901972261312923709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11705581267981507541949139 17558371901972261312923709)
            ·
              refine ⟨6584389463239597992346391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17558371901972261312923709 6584389463239597992346391)
              ·
                refine ⟨9876584194859396988519587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6584389463239597992346391 9876584194859396988519587)
                ·
                  refine ⟨14814876292289095482779381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9876584194859396988519587 14814876292289095482779381)
                  ·
                    refine ⟨1388894652402102701510567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14814876292289095482779381 1388894652402102701510567)
                    ·
                      rfl

theorem cell22_4057294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_4057294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057294 prefixEnd_4057294 := by exact prefixLift 4057294
  have htrace : WordTrace (prefixWord ++ tailWord_4057294) baseStart_4057294 baseEnd_4057294 := by
    simpa [prefixWord, tailWord_4057294, baseEnd_4057294] using wordTrace_append hprefix tailTrace_4057294
  have hstable : (prefixWord ++ tailWord_4057294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057294).length < 2 ^ (prefixWord ++ tailWord_4057294).sum := by decide
  have hdescent : baseEnd_4057294 < baseStart_4057294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057309 : List Nat := [1, 4, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_4057309 : Nat := 118140960795 + 4057309 * 2 ^ 59
def prefixEnd_4057309 : Nat := 4983230072969 + 3 ^ 40 * 4057309 * 2
def baseEnd_4057309 : Nat := 1388899787208647662385521

theorem tailTrace_4057309 : CollatzResearch.WordTrace tailWord_4057309 prefixEnd_4057309 1388899787208647662385521 := by
  unfold tailWord_4057309
  simp only [CollatzResearch.WordTrace]
  refine ⟨147982216458069901055078981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98654810972046600703385987 147982216458069901055078981)
  ·
    refine ⟨27746665585888106447827309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147982216458069901055078981 27746665585888106447827309)
    ·
      refine ⟨10404999594708039917935241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27746665585888106447827309 10404999594708039917935241)
      ·
        refine ⟨7803749696031029938451431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10404999594708039917935241 7803749696031029938451431)
        ·
          refine ⟨11705624544046544907677147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7803749696031029938451431 11705624544046544907677147)
          ·
            refine ⟨17558436816069817361515721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11705624544046544907677147 17558436816069817361515721)
            ·
              refine ⟨13168827612052363021136791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17558436816069817361515721 13168827612052363021136791)
              ·
                refine ⟨19753241418078544531705187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13168827612052363021136791 19753241418078544531705187)
                ·
                  refine ⟨29629862127117816797557781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19753241418078544531705187 29629862127117816797557781)
                  ·
                    refine ⟨1388899787208647662385521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29629862127117816797557781 1388899787208647662385521)
                    ·
                      rfl

theorem cell22_4057309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_4057309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057309 prefixEnd_4057309 := by exact prefixLift 4057309
  have htrace : WordTrace (prefixWord ++ tailWord_4057309) baseStart_4057309 baseEnd_4057309 := by
    simpa [prefixWord, tailWord_4057309, baseEnd_4057309] using wordTrace_append hprefix tailTrace_4057309
  have hstable : (prefixWord ++ tailWord_4057309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057309).length < 2 ^ (prefixWord ++ tailWord_4057309).sum := by decide
  have hdescent : baseEnd_4057309 < baseStart_4057309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057431 : List Nat := [1, 1, 3, 2, 3, 1, 4, 3, 4]
def baseStart_4057431 : Nat := 118140960795 + 4057431 * 2 ^ 59
def prefixEnd_4057431 : Nat := 4983230072969 + 3 ^ 40 * 4057431 * 2
def baseEnd_4057431 : Nat := 462980516767293336945049

theorem tailTrace_4057431 : CollatzResearch.WordTrace tailWord_4057431 prefixEnd_4057431 462980516767293336945049 := by
  unfold tailWord_4057431
  simp only [CollatzResearch.WordTrace]
  refine ⟨147986666163627915891020147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98657777442418610594013431 147986666163627915891020147)
  ·
    refine ⟨221979999245441873836530221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147986666163627915891020147 221979999245441873836530221)
    ·
      refine ⟨83242499717040702688698833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 221979999245441873836530221 83242499717040702688698833)
      ·
        refine ⟨62431874787780527016524125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83242499717040702688698833 62431874787780527016524125)
        ·
          refine ⟨23411953045417697631196547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62431874787780527016524125 23411953045417697631196547)
          ·
            refine ⟨35117929568126546446794821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23411953045417697631196547 35117929568126546446794821)
            ·
              refine ⟨6584611794023727458774029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35117929568126546446794821 6584611794023727458774029)
              ·
                refine ⟨2469229422758897797040261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6584611794023727458774029 2469229422758897797040261)
                ·
                  refine ⟨462980516767293336945049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2469229422758897797040261 462980516767293336945049)
                  ·
                    rfl

theorem cell22_4057431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 3, 4].length) (baseStart_4057431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057431 prefixEnd_4057431 := by exact prefixLift 4057431
  have htrace : WordTrace (prefixWord ++ tailWord_4057431) baseStart_4057431 baseEnd_4057431 := by
    simpa [prefixWord, tailWord_4057431, baseEnd_4057431] using wordTrace_append hprefix tailTrace_4057431
  have hstable : (prefixWord ++ tailWord_4057431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057431).length < 2 ^ (prefixWord ++ tailWord_4057431).sum := by decide
  have hdescent : baseEnd_4057431 < baseStart_4057431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057444 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 4, 4]
def baseStart_4057444 : Nat := 118140960795 + 4057444 * 2 ^ 59
def prefixEnd_4057444 : Nat := 4983230072969 + 3 ^ 40 * 4057444 * 2
def baseEnd_4057444 : Nat := 1388946000467552310260107

theorem tailTrace_4057444 : CollatzResearch.WordTrace tailWord_4057444 prefixEnd_4057444 1388946000467552310260107 := by
  unfold tailWord_4057444
  simp only [CollatzResearch.WordTrace]
  refine ⟨73993570156290409555621693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98658093541720546074162257 73993570156290409555621693)
  ·
    refine ⟨27747588808608903583358135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73993570156290409555621693 27747588808608903583358135)
    ·
      refine ⟨41621383212913355375037203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27747588808608903583358135 41621383212913355375037203)
      ·
        refine ⟨62432074819370033062555805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41621383212913355375037203 62432074819370033062555805)
        ·
          refine ⟨23412028057263762398458427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62432074819370033062555805 23412028057263762398458427)
          ·
            refine ⟨35118042085895643597687641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23412028057263762398458427 35118042085895643597687641)
            ·
              refine ⟨26338531564421732698265731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35118042085895643597687641 26338531564421732698265731)
              ·
                refine ⟨39507797346632599047398597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26338531564421732698265731 39507797346632599047398597)
                ·
                  refine ⟨7407712002493612321387237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39507797346632599047398597 7407712002493612321387237)
                  ·
                    refine ⟨1388946000467552310260107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7407712002493612321387237 1388946000467552310260107)
                    ·
                      rfl

theorem cell22_4057444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 4, 4].length) (baseStart_4057444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057444 prefixEnd_4057444 := by exact prefixLift 4057444
  have htrace : WordTrace (prefixWord ++ tailWord_4057444) baseStart_4057444 baseEnd_4057444 := by
    simpa [prefixWord, tailWord_4057444, baseEnd_4057444] using wordTrace_append hprefix tailTrace_4057444
  have hstable : (prefixWord ++ tailWord_4057444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057444).length < 2 ^ (prefixWord ++ tailWord_4057444).sum := by decide
  have hdescent : baseEnd_4057444 < baseStart_4057444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057482 : List Nat := [3, 1, 2, 5, 2, 1, 1, 3, 4]
def baseStart_4057482 : Nat := 118140960795 + 4057482 * 2 ^ 59
def prefixEnd_4057482 : Nat := 4983230072969 + 3 ^ 40 * 4057482 * 2
def baseEnd_4057482 : Nat := 462986336214710959269997

theorem tailTrace_4057482 : CollatzResearch.WordTrace tailWord_4057482 prefixEnd_4057482 462986336214710959269997 := by
  unfold tailWord_4057482
  simp only [CollatzResearch.WordTrace]
  refine ⟨36997131571610787900281675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98659017524295434400751133 36997131571610787900281675)
  ·
    refine ⟨55495697357416181850422513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36997131571610787900281675 55495697357416181850422513)
    ·
      refine ⟨41621773018062136387816885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55495697357416181850422513 41621773018062136387816885)
      ·
        refine ⟨3902041220443325286357833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41621773018062136387816885 3902041220443325286357833)
        ·
          refine ⟨2926530915332493964768375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3902041220443325286357833 2926530915332493964768375)
          ·
            refine ⟨4389796372998740947152563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2926530915332493964768375 4389796372998740947152563)
            ·
              refine ⟨6584694559498111420728845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4389796372998740947152563 6584694559498111420728845)
              ·
                refine ⟨2469260459811791782773317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6584694559498111420728845 2469260459811791782773317)
                ·
                  refine ⟨462986336214710959269997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2469260459811791782773317 462986336214710959269997)
                  ·
                    rfl

theorem cell22_4057482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_4057482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057482 prefixEnd_4057482 := by exact prefixLift 4057482
  have htrace : WordTrace (prefixWord ++ tailWord_4057482) baseStart_4057482 baseEnd_4057482 := by
    simpa [prefixWord, tailWord_4057482, baseEnd_4057482] using wordTrace_append hprefix tailTrace_4057482
  have hstable : (prefixWord ++ tailWord_4057482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057482).length < 2 ^ (prefixWord ++ tailWord_4057482).sum := by decide
  have hdescent : baseEnd_4057482 < baseStart_4057482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057504 : List Nat := [2, 1, 1, 4, 1, 3, 2, 1, 7]
def baseStart_4057504 : Nat := 118140960795 + 4057504 * 2 ^ 59
def prefixEnd_4057504 : Nat := 4983230072969 + 3 ^ 40 * 4057504 * 2
def baseEnd_4057504 : Nat := 462988846564577384586641

theorem tailTrace_4057504 : CollatzResearch.WordTrace tailWord_4057504 prefixEnd_4057504 462988846564577384586641 := by
  unfold tailWord_4057504
  simp only [CollatzResearch.WordTrace]
  refine ⟨73994664346181724679213783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98659552461575632905618377 73994664346181724679213783)
  ·
    refine ⟨110991996519272587018820675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73994664346181724679213783 110991996519272587018820675)
    ·
      refine ⟨166487994778908880528231013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110991996519272587018820675 166487994778908880528231013)
      ·
        refine ⟨31216499021045415099043315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166487994778908880528231013 31216499021045415099043315)
        ·
          refine ⟨46824748531568122648564973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31216499021045415099043315 46824748531568122648564973)
          ·
            refine ⟨17559280699338045993211865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46824748531568122648564973 17559280699338045993211865)
            ·
              refine ⟨13169460524503534494908899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17559280699338045993211865 13169460524503534494908899)
              ·
                refine ⟨19754190786755301742363349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13169460524503534494908899 19754190786755301742363349)
                ·
                  refine ⟨462988846564577384586641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19754190786755301742363349 462988846564577384586641)
                  ·
                    rfl

theorem cell22_4057504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 2, 1, 7].length) (baseStart_4057504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057504 prefixEnd_4057504 := by exact prefixLift 4057504
  have htrace : WordTrace (prefixWord ++ tailWord_4057504) baseStart_4057504 baseEnd_4057504 := by
    simpa [prefixWord, tailWord_4057504, baseEnd_4057504] using wordTrace_append hprefix tailTrace_4057504
  have hstable : (prefixWord ++ tailWord_4057504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057504).length < 2 ^ (prefixWord ++ tailWord_4057504).sum := by decide
  have hdescent : baseEnd_4057504 < baseStart_4057504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057508 : List Nat := [2, 3, 1, 2, 1, 1, 2, 6, 1, 3]
def baseStart_4057508 : Nat := 118140960795 + 4057508 * 2 ^ 59
def prefixEnd_4057508 : Nat := 4983230072969 + 3 ^ 40 * 4057508 * 2
def baseEnd_4057508 : Nat := 1388967908975477476659911

theorem tailTrace_4057508 : CollatzResearch.WordTrace tailWord_4057508 prefixEnd_4057508 1388967908975477476659911 := by
  unfold tailWord_4057508
  simp only [CollatzResearch.WordTrace]
  refine ⟨73994737292174479020786589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98659649722899305361048785 73994737292174479020786589)
  ·
    refine ⟨27748026484565429632794971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73994737292174479020786589 27748026484565429632794971)
    ·
      refine ⟨41622039726848144449192457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27748026484565429632794971 41622039726848144449192457)
      ·
        refine ⟨31216529795136108336894343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41622039726848144449192457 31216529795136108336894343)
        ·
          refine ⟨46824794692704162505341515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31216529795136108336894343 46824794692704162505341515)
          ·
            refine ⟨70237192039056243758012273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46824794692704162505341515 70237192039056243758012273)
            ·
              refine ⟨52677894029292182818509205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70237192039056243758012273 52677894029292182818509205)
              ·
                refine ⟨2469276282623071069617619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 52677894029292182818509205 2469276282623071069617619)
                ·
                  refine ⟨3703914423934606604426429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469276282623071069617619 3703914423934606604426429)
                  ·
                    refine ⟨1388967908975477476659911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3703914423934606604426429 1388967908975477476659911)
                    ·
                      rfl

theorem cell22_4057508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_4057508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057508 prefixEnd_4057508 := by exact prefixLift 4057508
  have htrace : WordTrace (prefixWord ++ tailWord_4057508) baseStart_4057508 baseEnd_4057508 := by
    simpa [prefixWord, tailWord_4057508, baseEnd_4057508] using wordTrace_append hprefix tailTrace_4057508
  have hstable : (prefixWord ++ tailWord_4057508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057508).length < 2 ^ (prefixWord ++ tailWord_4057508).sum := by decide
  have hdescent : baseEnd_4057508 < baseStart_4057508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057521 : List Nat := [1, 2, 2, 4, 1, 3, 1, 3, 5]
def baseStart_4057521 : Nat := 118140960795 + 4057521 * 2 ^ 59
def prefixEnd_4057521 : Nat := 4983230072969 + 3 ^ 40 * 4057521 * 2
def baseEnd_4057521 : Nat := 462990786380383258694957

theorem tailTrace_4057521 : CollatzResearch.WordTrace tailWord_4057521 prefixEnd_4057521 462990786380383258694957 := by
  unfold tailWord_4057521
  simp only [CollatzResearch.WordTrace]
  refine ⟨147989948733301861261796417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98659965822201240841197611 147989948733301861261796417)
  ·
    refine ⟨110992461549976395946347313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147989948733301861261796417 110992461549976395946347313)
    ·
      refine ⟨83244346162482296959760485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110992461549976395946347313 83244346162482296959760485)
      ·
        refine ⟨15608314905465430679955091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83244346162482296959760485 15608314905465430679955091)
        ·
          refine ⟨23412472358198146019932637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15608314905465430679955091 23412472358198146019932637)
          ·
            refine ⟨8779677134324304757474739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23412472358198146019932637 8779677134324304757474739)
            ·
              refine ⟨13169515701486457136212109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8779677134324304757474739 13169515701486457136212109)
              ·
                refine ⟨4938568388057421426079541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13169515701486457136212109 4938568388057421426079541)
                ·
                  refine ⟨462990786380383258694957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4938568388057421426079541 462990786380383258694957)
                  ·
                    rfl

theorem cell22_4057521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 3, 5].length) (baseStart_4057521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057521 prefixEnd_4057521 := by exact prefixLift 4057521
  have htrace : WordTrace (prefixWord ++ tailWord_4057521) baseStart_4057521 baseEnd_4057521 := by
    simpa [prefixWord, tailWord_4057521, baseEnd_4057521] using wordTrace_append hprefix tailTrace_4057521
  have hstable : (prefixWord ++ tailWord_4057521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057521).length < 2 ^ (prefixWord ++ tailWord_4057521).sum := by decide
  have hdescent : baseEnd_4057521 < baseStart_4057521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057570 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 2, 5]
def baseStart_4057570 : Nat := 118140960795 + 4057570 * 2 ^ 59
def prefixEnd_4057570 : Nat := 4983230072969 + 3 ^ 40 * 4057570 * 2
def baseEnd_4057570 : Nat := 1388989132842529981609721

theorem tailTrace_4057570 : CollatzResearch.WordTrace tailWord_4057570 prefixEnd_4057570 1388989132842529981609721 := by
  unfold tailWord_4057570
  simp only [CollatzResearch.WordTrace]
  refine ⟨36997933977531085657582541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98661157273416228420220109 36997933977531085657582541)
  ·
    refine ⟨13874225241574157121593453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36997933977531085657582541 13874225241574157121593453)
    ·
      refine ⟨5202834465590308920597545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13874225241574157121593453 5202834465590308920597545)
      ·
        refine ⟨3902125849192731690448159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5202834465590308920597545 3902125849192731690448159)
        ·
          refine ⟨5853188773789097535672239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3902125849192731690448159 5853188773789097535672239)
          ·
            refine ⟨8779783160683646303508359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5853188773789097535672239 8779783160683646303508359)
            ·
              refine ⟨13169674741025469455262539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8779783160683646303508359 13169674741025469455262539)
              ·
                refine ⟨19754512111538204182893809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13169674741025469455262539 19754512111538204182893809)
                ·
                  refine ⟨14815884083653653137170357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19754512111538204182893809 14815884083653653137170357)
                  ·
                    refine ⟨1388989132842529981609721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14815884083653653137170357 1388989132842529981609721)
                    ·
                      rfl

theorem cell22_4057570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_4057570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057570 prefixEnd_4057570 := by exact prefixLift 4057570
  have htrace : WordTrace (prefixWord ++ tailWord_4057570) baseStart_4057570 baseEnd_4057570 := by
    simpa [prefixWord, tailWord_4057570, baseEnd_4057570] using wordTrace_append hprefix tailTrace_4057570
  have hstable : (prefixWord ++ tailWord_4057570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057570).length < 2 ^ (prefixWord ++ tailWord_4057570).sum := by decide
  have hdescent : baseEnd_4057570 < baseStart_4057570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057579 : List Nat := [1, 1, 1, 1, 2, 3, 4, 2, 1, 6]
def baseStart_4057579 : Nat := 118140960795 + 4057579 * 2 ^ 59
def prefixEnd_4057579 : Nat := 4983230072969 + 3 ^ 40 * 4057579 * 2
def baseEnd_4057579 : Nat := 1388992213726456958134693

theorem tailTrace_4057579 : CollatzResearch.WordTrace tailWord_4057579 prefixEnd_4057579 1388992213726456958134693 := by
  unfold tailWord_4057579
  simp only [CollatzResearch.WordTrace]
  refine ⟨147992064167091737167407791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98661376111394491444938527 147992064167091737167407791)
  ·
    refine ⟨221988096250637605751111687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147992064167091737167407791 221988096250637605751111687)
    ·
      refine ⟨332982144375956408626667531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 221988096250637605751111687 332982144375956408626667531)
      ·
        refine ⟨499473216563934612940001297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332982144375956408626667531 499473216563934612940001297)
        ·
          refine ⟨374604912422950959705000973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499473216563934612940001297 374604912422950959705000973)
          ·
            refine ⟨140476842158606609889375365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374604912422950959705000973 140476842158606609889375365)
            ·
              refine ⟨26339407904738739354257881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140476842158606609889375365 26339407904738739354257881)
              ·
                refine ⟨19754555928554054515693411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26339407904738739354257881 19754555928554054515693411)
                ·
                  refine ⟨29631833892831081773540117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19754555928554054515693411 29631833892831081773540117)
                  ·
                    refine ⟨1388992213726456958134693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29631833892831081773540117 1388992213726456958134693)
                    ·
                      rfl

theorem cell22_4057579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 2, 1, 6].length) (baseStart_4057579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057579 prefixEnd_4057579 := by exact prefixLift 4057579
  have htrace : WordTrace (prefixWord ++ tailWord_4057579) baseStart_4057579 baseEnd_4057579 := by
    simpa [prefixWord, tailWord_4057579, baseEnd_4057579] using wordTrace_append hprefix tailTrace_4057579
  have hstable : (prefixWord ++ tailWord_4057579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057579).length < 2 ^ (prefixWord ++ tailWord_4057579).sum := by decide
  have hdescent : baseEnd_4057579 < baseStart_4057579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057632 : List Nat := [2, 1, 1, 6, 2, 1, 3, 1, 2, 3]
def baseStart_4057632 : Nat := 118140960795 + 4057632 * 2 ^ 59
def prefixEnd_4057632 : Nat := 4983230072969 + 3 ^ 40 * 4057632 * 2
def baseEnd_4057632 : Nat := 1389010356709582486559531

theorem tailTrace_4057632 : CollatzResearch.WordTrace tailWord_4057632 prefixEnd_4057632 1389010356709582486559531 := by
  unfold tailWord_4057632
  simp only [CollatzResearch.WordTrace]
  refine ⟨73996998617949863609543575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98662664823933151479391433 73996998617949863609543575)
  ·
    refine ⟨110995497926924795414315363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73996998617949863609543575 110995497926924795414315363)
    ·
      refine ⟨166493246890387193121473045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110995497926924795414315363 166493246890387193121473045)
      ·
        refine ⟨7804370947986899677569049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166493246890387193121473045 7804370947986899677569049)
        ·
          refine ⟨5853278210990174758176787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7804370947986899677569049 5853278210990174758176787)
          ·
            refine ⟨8779917316485262137265181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5853278210990174758176787 8779917316485262137265181)
            ·
              refine ⟨3292468993681973301474443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8779917316485262137265181 3292468993681973301474443)
              ·
                refine ⟨4938703490522959952211665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3292468993681973301474443 4938703490522959952211665)
                ·
                  refine ⟨3704027617892219964158749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4938703490522959952211665 3704027617892219964158749)
                  ·
                    refine ⟨1389010356709582486559531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3704027617892219964158749 1389010356709582486559531)
                    ·
                      rfl

theorem cell22_4057632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3, 1, 2, 3].length) (baseStart_4057632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057632 prefixEnd_4057632 := by exact prefixLift 4057632
  have htrace : WordTrace (prefixWord ++ tailWord_4057632) baseStart_4057632 baseEnd_4057632 := by
    simpa [prefixWord, tailWord_4057632, baseEnd_4057632] using wordTrace_append hprefix tailTrace_4057632
  have hstable : (prefixWord ++ tailWord_4057632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057632).length < 2 ^ (prefixWord ++ tailWord_4057632).sum := by decide
  have hdescent : baseEnd_4057632 < baseStart_4057632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057677 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_4057677 : Nat := 118140960795 + 4057677 * 2 ^ 59
def prefixEnd_4057677 : Nat := 4983230072969 + 3 ^ 40 * 4057677 * 2
def baseEnd_4057677 : Nat := 1389025761129217369184393

theorem tailTrace_4057677 : CollatzResearch.WordTrace tailWord_4057677 prefixEnd_4057677 1389025761129217369184393 := by
  unfold tailWord_4057677
  simp only [CollatzResearch.WordTrace]
  refine ⟨147995638520736699904475285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98663759013824466602983523 147995638520736699904475285)
  ·
    refine ⟨6937295555659532808022279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 147995638520736699904475285 6937295555659532808022279)
    ·
      refine ⟨10405943333489299212033419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6937295555659532808022279 10405943333489299212033419)
      ·
        refine ⟨15608915000233948818050129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10405943333489299212033419 15608915000233948818050129)
        ·
          refine ⟨11706686250175461613537597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15608915000233948818050129 11706686250175461613537597)
          ·
            refine ⟨4390007343815798105076599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11706686250175461613537597 4390007343815798105076599)
            ·
              refine ⟨6585011015723697157614899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390007343815798105076599 6585011015723697157614899)
              ·
                refine ⟨9877516523585545736422349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6585011015723697157614899 9877516523585545736422349)
                ·
                  refine ⟨3704068696344579651158381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9877516523585545736422349 3704068696344579651158381)
                  ·
                    refine ⟨1389025761129217369184393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3704068696344579651158381 1389025761129217369184393)
                    ·
                      rfl

theorem cell22_4057677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_4057677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057677 prefixEnd_4057677 := by exact prefixLift 4057677
  have htrace : WordTrace (prefixWord ++ tailWord_4057677) baseStart_4057677 baseEnd_4057677 := by
    simpa [prefixWord, tailWord_4057677, baseEnd_4057677] using wordTrace_append hprefix tailTrace_4057677
  have hstable : (prefixWord ++ tailWord_4057677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057677).length < 2 ^ (prefixWord ++ tailWord_4057677).sum := by decide
  have hdescent : baseEnd_4057677 < baseStart_4057677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057778 : List Nat := [3, 2, 1, 1, 1, 2, 1, 1, 7, 3]
def baseStart_4057778 : Nat := 118140960795 + 4057778 * 2 ^ 59
def prefixEnd_4057778 : Nat := 4983230072969 + 3 ^ 40 * 4057778 * 2
def baseEnd_4057778 : Nat := 1389060335493286772409083

theorem tailTrace_4057778 : CollatzResearch.WordTrace tailWord_4057778 prefixEnd_4057778 1389060335493286772409083 := by
  unfold tailWord_4057778
  simp only [CollatzResearch.WordTrace]
  refine ⟨36999830573342698538475497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98666214862247196102601325 36999830573342698538475497)
  ·
    refine ⟨27749872930007023903856623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36999830573342698538475497 27749872930007023903856623)
    ·
      refine ⟨41624809395010535855784935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27749872930007023903856623 41624809395010535855784935)
      ·
        refine ⟨62437214092515803783677403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41624809395010535855784935 62437214092515803783677403)
        ·
          refine ⟨93655821138773705675516105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62437214092515803783677403 93655821138773705675516105)
          ·
            refine ⟨70241865854080279256637079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93655821138773705675516105 70241865854080279256637079)
            ·
              refine ⟨105362798781120418884955619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70241865854080279256637079 105362798781120418884955619)
              ·
                refine ⟨158044198171680628327433429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105362798781120418884955619 158044198171680628327433429)
                ·
                  refine ⟨3704160894648764726424221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 158044198171680628327433429 3704160894648764726424221)
                  ·
                    refine ⟨1389060335493286772409083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3704160894648764726424221 1389060335493286772409083)
                    ·
                      rfl

theorem cell22_4057778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_4057778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057778 prefixEnd_4057778 := by exact prefixLift 4057778
  have htrace : WordTrace (prefixWord ++ tailWord_4057778) baseStart_4057778 baseEnd_4057778 := by
    simpa [prefixWord, tailWord_4057778, baseEnd_4057778] using wordTrace_append hprefix tailTrace_4057778
  have hstable : (prefixWord ++ tailWord_4057778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057778).length < 2 ^ (prefixWord ++ tailWord_4057778).sum := by decide
  have hdescent : baseEnd_4057778 < baseStart_4057778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057829 : List Nat := [1, 3, 1, 4, 1, 4, 1, 3, 1, 3]
def baseStart_4057829 : Nat := 118140960795 + 4057829 * 2 ^ 59
def prefixEnd_4057829 : Nat := 4983230072969 + 3 ^ 40 * 4057829 * 2
def baseEnd_4057829 : Nat := 1389077793835539639383927

theorem tailTrace_4057829 : CollatzResearch.WordTrace tailWord_4057829 prefixEnd_4057829 1389077793835539639383927 := by
  unfold tailWord_4057829
  simp only [CollatzResearch.WordTrace]
  refine ⟨148001182416186029864008541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98667454944124019909339027 148001182416186029864008541)
  ·
    refine ⟨55500443406069761199003203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148001182416186029864008541 55500443406069761199003203)
    ·
      refine ⟨83250665109104641798504805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55500443406069761199003203 83250665109104641798504805)
      ·
        refine ⟨15609499707957120337219651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83250665109104641798504805 15609499707957120337219651)
        ·
          refine ⟨23414249561935680505829477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15609499707957120337219651 23414249561935680505829477)
          ·
            refine ⟨4390171792862940094843027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23414249561935680505829477 4390171792862940094843027)
            ·
              refine ⟨6585257689294410142264541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4390171792862940094843027 6585257689294410142264541)
              ·
                refine ⟨2469471633485403803349203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6585257689294410142264541 2469471633485403803349203)
                ·
                  refine ⟨3704207450228105705023805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469471633485403803349203 3704207450228105705023805)
                  ·
                    refine ⟨1389077793835539639383927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3704207450228105705023805 1389077793835539639383927)
                    ·
                      rfl

theorem cell22_4057829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_4057829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057829 prefixEnd_4057829 := by exact prefixLift 4057829
  have htrace : WordTrace (prefixWord ++ tailWord_4057829) baseStart_4057829 baseEnd_4057829 := by
    simpa [prefixWord, tailWord_4057829, baseEnd_4057829] using wordTrace_append hprefix tailTrace_4057829
  have hstable : (prefixWord ++ tailWord_4057829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057829).length < 2 ^ (prefixWord ++ tailWord_4057829).sum := by decide
  have hdescent : baseEnd_4057829 < baseStart_4057829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057868 : List Nat := [2, 2, 1, 2, 2, 1, 1, 5, 1, 5]
def baseStart_4057868 : Nat := 118140960795 + 4057868 * 2 ^ 59
def prefixEnd_4057868 : Nat := 4983230072969 + 3 ^ 40 * 4057868 * 2
def baseEnd_4057868 : Nat := 1389091144332556537658807

theorem tailTrace_4057868 : CollatzResearch.WordTrace tailWord_4057868 prefixEnd_4057868 1389091144332556537658807 := by
  unfold tailWord_4057868
  simp only [CollatzResearch.WordTrace]
  refine ⟨74001302431522369762339129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98668403242029826349785505 74001302431522369762339129)
  ·
    refine ⟨55500976823641777321754347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74001302431522369762339129 55500976823641777321754347)
    ·
      refine ⟨83251465235462665982631521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55500976823641777321754347 83251465235462665982631521)
      ·
        refine ⟨62438598926596999486973641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83251465235462665982631521 62438598926596999486973641)
        ·
          refine ⟨46828949194947749615230231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62438598926596999486973641 46828949194947749615230231)
          ·
            refine ⟨70243423792421624422845347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46828949194947749615230231 70243423792421624422845347)
            ·
              refine ⟨105365135688632436634268021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70243423792421624422845347 105365135688632436634268021)
              ·
                refine ⟨9877981470809290934462627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 105365135688632436634268021 9877981470809290934462627)
                ·
                  refine ⟨14816972206213936401693941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9877981470809290934462627 14816972206213936401693941)
                  ·
                    refine ⟨1389091144332556537658807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14816972206213936401693941 1389091144332556537658807)
                    ·
                      rfl

theorem cell22_4057868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_4057868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057868 prefixEnd_4057868 := by exact prefixLift 4057868
  have htrace : WordTrace (prefixWord ++ tailWord_4057868) baseStart_4057868 baseEnd_4057868 := by
    simpa [prefixWord, tailWord_4057868, baseEnd_4057868] using wordTrace_append hprefix tailTrace_4057868
  have hstable : (prefixWord ++ tailWord_4057868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057868).length < 2 ^ (prefixWord ++ tailWord_4057868).sum := by decide
  have hdescent : baseEnd_4057868 < baseStart_4057868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057928 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 2, 6]
def baseStart_4057928 : Nat := 118140960795 + 4057928 * 2 ^ 59
def prefixEnd_4057928 : Nat := 4983230072969 + 3 ^ 40 * 4057928 * 2
def baseEnd_4057928 : Nat := 1389111683558736381158623

theorem tailTrace_4057928 : CollatzResearch.WordTrace tailWord_4057928 prefixEnd_4057928 1389111683558736381158623 := by
  unfold tailWord_4057928
  simp only [CollatzResearch.WordTrace]
  refine ⟨74002396621413684885931219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98669862161884913181241625 74002396621413684885931219)
  ·
    refine ⟨111003594932120527328896829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74002396621413684885931219 111003594932120527328896829)
    ·
      refine ⟨41626348099545197748336311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111003594932120527328896829 41626348099545197748336311)
      ·
        refine ⟨62439522149317796622504467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41626348099545197748336311 62439522149317796622504467)
        ·
          refine ⟨93659283223976694933756701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62439522149317796622504467 93659283223976694933756701)
          ·
            refine ⟨35122231208991260600158763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93659283223976694933756701 35122231208991260600158763)
            ·
              refine ⟨52683346813486890900238145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35122231208991260600158763 52683346813486890900238145)
              ·
                refine ⟨39512510110115168175178609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52683346813486890900238145 39512510110115168175178609)
                ·
                  refine ⟨29634382582586376131383957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39512510110115168175178609 29634382582586376131383957)
                  ·
                    refine ⟨1389111683558736381158623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29634382582586376131383957 1389111683558736381158623)
                    ·
                      rfl

theorem cell22_4057928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2, 6].length) (baseStart_4057928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057928 prefixEnd_4057928 := by exact prefixLift 4057928
  have htrace : WordTrace (prefixWord ++ tailWord_4057928) baseStart_4057928 baseEnd_4057928 := by
    simpa [prefixWord, tailWord_4057928, baseEnd_4057928] using wordTrace_append hprefix tailTrace_4057928
  have hstable : (prefixWord ++ tailWord_4057928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057928).length < 2 ^ (prefixWord ++ tailWord_4057928).sum := by decide
  have hdescent : baseEnd_4057928 < baseStart_4057928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057960 : List Nat := [2, 1, 4, 2, 1, 3, 1, 1, 7]
def baseStart_4057960 : Nat := 118140960795 + 4057960 * 2 ^ 59
def prefixEnd_4057960 : Nat := 4983230072969 + 3 ^ 40 * 4057960 * 2
def baseEnd_4057960 : Nat := 463040879270899654786175

theorem tailTrace_4057960 : CollatzResearch.WordTrace tailWord_4057960 prefixEnd_4057960 463040879270899654786175 := by
  unfold tailWord_4057960
  simp only [CollatzResearch.WordTrace]
  refine ⟨74002980189355719618513667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98670640252474292824684889 74002980189355719618513667)
  ·
    refine ⟨111004470284033579427770501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74002980189355719618513667 111004470284033579427770501)
    ·
      refine ⟨20813338178256296142706969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111004470284033579427770501 20813338178256296142706969)
      ·
        refine ⟨15610003633692222107030227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20813338178256296142706969 15610003633692222107030227)
        ·
          refine ⟨23415005450538333160545341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15610003633692222107030227 23415005450538333160545341)
          ·
            refine ⟨8780627043951874935204503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23415005450538333160545341 8780627043951874935204503)
            ·
              refine ⟨13170940565927812402806755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8780627043951874935204503 13170940565927812402806755)
              ·
                refine ⟨19756410848891718604210133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13170940565927812402806755 19756410848891718604210133)
                ·
                  refine ⟨463040879270899654786175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19756410848891718604210133 463040879270899654786175)
                  ·
                    rfl

theorem cell22_4057960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 1, 7].length) (baseStart_4057960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057960 prefixEnd_4057960 := by exact prefixLift 4057960
  have htrace : WordTrace (prefixWord ++ tailWord_4057960) baseStart_4057960 baseEnd_4057960 := by
    simpa [prefixWord, tailWord_4057960, baseEnd_4057960] using wordTrace_append hprefix tailTrace_4057960
  have hstable : (prefixWord ++ tailWord_4057960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057960).length < 2 ^ (prefixWord ++ tailWord_4057960).sum := by decide
  have hdescent : baseEnd_4057960 < baseStart_4057960 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4057977 : List Nat := [1, 2, 1, 3, 2, 4, 3, 1, 5]
def baseStart_4057977 : Nat := 118140960795 + 4057977 * 2 ^ 59
def prefixEnd_4057977 : Nat := 4983230072969 + 3 ^ 40 * 4057977 * 2
def baseEnd_4057977 : Nat := 463042819086705528894491

theorem tailTrace_4057977 : CollatzResearch.WordTrace tailWord_4057977 prefixEnd_4057977 463042819086705528894491 := by
  unfold tailWord_4057977
  simp only [CollatzResearch.WordTrace]
  refine ⟨148006580419649851140396185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98671053613099900760264123 148006580419649851140396185)
  ·
    refine ⟨111004935314737388355297139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148006580419649851140396185 111004935314737388355297139)
    ·
      refine ⟨166507402972106082532945709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111004935314737388355297139 166507402972106082532945709)
      ·
        refine ⟨62440276114539780949854641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166507402972106082532945709 62440276114539780949854641)
        ·
          refine ⟨46830207085904835712390981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62440276114539780949854641 46830207085904835712390981)
          ·
            refine ⟨8780663828607156696073309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46830207085904835712390981 8780663828607156696073309)
            ·
              refine ⟨3292748935727683761027491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8780663828607156696073309 3292748935727683761027491)
              ·
                refine ⟨4939123403591525641541237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3292748935727683761027491 4939123403591525641541237)
                ·
                  refine ⟨463042819086705528894491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4939123403591525641541237 463042819086705528894491)
                  ·
                    rfl

theorem cell22_4057977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 3, 1, 5].length) (baseStart_4057977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4057977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4057977 prefixEnd_4057977 := by exact prefixLift 4057977
  have htrace : WordTrace (prefixWord ++ tailWord_4057977) baseStart_4057977 baseEnd_4057977 := by
    simpa [prefixWord, tailWord_4057977, baseEnd_4057977] using wordTrace_append hprefix tailTrace_4057977
  have hstable : (prefixWord ++ tailWord_4057977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4057977).length < 2 ^ (prefixWord ++ tailWord_4057977).sum := by decide
  have hdescent : baseEnd_4057977 < baseStart_4057977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4057977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058101 : List Nat := [1, 3, 5, 2, 1, 1, 3, 6]
def baseStart_4058101 : Nat := 118140960795 + 4058101 * 2 ^ 59
def prefixEnd_4058101 : Nat := 4983230072969 + 3 ^ 40 * 4058101 * 2
def baseEnd_4058101 : Nat := 154352322777135732953677

theorem tailTrace_4058101 : CollatzResearch.WordTrace tailWord_4058101 prefixEnd_4058101 154352322777135732953677 := by
  unfold tailWord_4058101
  simp only [CollatzResearch.WordTrace]
  refine ⟨148011103071200620317910157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98674068714133746878606771 148011103071200620317910157)
  ·
    refine ⟨55504163651700232619216309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148011103071200620317910157 55504163651700232619216309)
    ·
      refine ⟨5203515342346896808051529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55504163651700232619216309 5203515342346896808051529)
      ·
        refine ⟨3902636506760172606038647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5203515342346896808051529 3902636506760172606038647)
        ·
          refine ⟨5853954760140258909057971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3902636506760172606038647 5853954760140258909057971)
          ·
            refine ⟨8780932140210388363586957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5853954760140258909057971 8780932140210388363586957)
            ·
              refine ⟨3292849552578895636345109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8780932140210388363586957 3292849552578895636345109)
              ·
                refine ⟨154352322777135732953677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3292849552578895636345109 154352322777135732953677)
                ·
                  rfl

theorem cell22_4058101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 6].length) (baseStart_4058101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4058101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4058101 prefixEnd_4058101 := by exact prefixLift 4058101
  have htrace : WordTrace (prefixWord ++ tailWord_4058101) baseStart_4058101 baseEnd_4058101 := by
    simpa [prefixWord, tailWord_4058101, baseEnd_4058101] using wordTrace_append hprefix tailTrace_4058101
  have hstable : (prefixWord ++ tailWord_4058101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058101).length < 2 ^ (prefixWord ++ tailWord_4058101).sum := by decide
  have hdescent : baseEnd_4058101 < baseStart_4058101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058264 : List Nat := [2, 1, 2, 4, 2, 1, 2, 3, 5]
def baseStart_4058264 : Nat := 118140960795 + 4058264 * 2 ^ 59
def prefixEnd_4058264 : Nat := 4983230072969 + 3 ^ 40 * 4058264 * 2
def baseEnd_4058264 : Nat := 463075567741781168252531

theorem tailTrace_4058264 : CollatzResearch.WordTrace tailWord_4058264 prefixEnd_4058264 463075567741781168252531 := by
  unfold tailWord_4058264
  simp only [CollatzResearch.WordTrace]
  refine ⟨74008524084805049578046923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98678032113073399437395897 74008524084805049578046923)
  ·
    refine ⟨111012786127207574367070385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74008524084805049578046923 111012786127207574367070385)
    ·
      refine ⟨83259589595405680775302789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111012786127207574367070385 83259589595405680775302789)
      ·
        refine ⟨15611173049138565145369273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83259589595405680775302789 15611173049138565145369273)
        ·
          refine ⟨11708379786853923859026955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15611173049138565145369273 11708379786853923859026955)
          ·
            refine ⟨17562569680280885788540433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11708379786853923859026955 17562569680280885788540433)
            ·
              refine ⟨13171927260210664341405325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17562569680280885788540433 13171927260210664341405325)
              ·
                refine ⟨4939472722578999128026997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13171927260210664341405325 4939472722578999128026997)
                ·
                  refine ⟨463075567741781168252531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4939472722578999128026997 463075567741781168252531)
                  ·
                    rfl

theorem cell22_4058264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 5].length) (baseStart_4058264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4058264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4058264 prefixEnd_4058264 := by exact prefixLift 4058264
  have htrace : WordTrace (prefixWord ++ tailWord_4058264) baseStart_4058264 baseEnd_4058264 := by
    simpa [prefixWord, tailWord_4058264, baseEnd_4058264] using wordTrace_append hprefix tailTrace_4058264
  have hstable : (prefixWord ++ tailWord_4058264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058264).length < 2 ^ (prefixWord ++ tailWord_4058264).sum := by decide
  have hdescent : baseEnd_4058264 < baseStart_4058264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058285 : List Nat := [1, 5, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_4058285 : Nat := 118140960795 + 4058285 * 2 ^ 59
def prefixEnd_4058285 : Nat := 4983230072969 + 3 ^ 40 * 4058285 * 2
def baseEnd_4058285 : Nat := 1389233891954506449982529

theorem tailTrace_4058285 : CollatzResearch.WordTrace tailWord_4058285 prefixEnd_4058285 1389233891954506449982529 := by
  unfold tailWord_4058285
  simp only [CollatzResearch.WordTrace]
  refine ⟨148017814102534019742608309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98678542735022679828405539 148017814102534019742608309)
  ·
    refine ⟨13876670072112564350869529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148017814102534019742608309 13876670072112564350869529)
    ·
      refine ⟨10407502554084423263152147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13876670072112564350869529 10407502554084423263152147)
      ·
        refine ⟨15611253831126634894728221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10407502554084423263152147 15611253831126634894728221)
        ·
          refine ⟨5854220186672488085523083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15611253831126634894728221 5854220186672488085523083)
          ·
            refine ⟨8781330280008732128284625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5854220186672488085523083 8781330280008732128284625)
            ·
              refine ⟨6585997710006549096213469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8781330280008732128284625 6585997710006549096213469)
              ·
                refine ⟨2469749141252455911080051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6585997710006549096213469 2469749141252455911080051)
                ·
                  refine ⟨3704623711878683866620077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469749141252455911080051 3704623711878683866620077)
                  ·
                    refine ⟨1389233891954506449982529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3704623711878683866620077 1389233891954506449982529)
                    ·
                      rfl

theorem cell22_4058285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_4058285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4058285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4058285 prefixEnd_4058285 := by exact prefixLift 4058285
  have htrace : WordTrace (prefixWord ++ tailWord_4058285) baseStart_4058285 baseEnd_4058285 := by
    simpa [prefixWord, tailWord_4058285, baseEnd_4058285] using wordTrace_append hprefix tailTrace_4058285
  have hstable : (prefixWord ++ tailWord_4058285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058285).length < 2 ^ (prefixWord ++ tailWord_4058285).sum := by decide
  have hdescent : baseEnd_4058285 < baseStart_4058285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058420 : List Nat := [2, 5, 1, 1, 1, 1, 3, 4, 1, 3]
def baseStart_4058420 : Nat := 118140960795 + 4058420 * 2 ^ 59
def prefixEnd_4058420 : Nat := 4983230072969 + 3 ^ 40 * 4058420 * 2
def baseEnd_4058420 : Nat := 1389280105213411097857115

theorem tailTrace_4058420 : CollatzResearch.WordTrace tailWord_4058420 prefixEnd_4058420 1389280105213411097857115 := by
  unfold tailWord_4058420
  simp only [CollatzResearch.WordTrace]
  refine ⟨74011368978522468899386357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98681825304696625199181809 74011368978522468899386357)
  ·
    refine ⟨6938565841736481459317471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74011368978522468899386357 6938565841736481459317471)
    ·
      refine ⟨10407848762604722188976207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6938565841736481459317471 10407848762604722188976207)
      ·
        refine ⟨15611773143907083283464311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10407848762604722188976207 15611773143907083283464311)
        ·
          refine ⟨23417659715860624925196467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15611773143907083283464311 23417659715860624925196467)
          ·
            refine ⟨35126489573790937387794701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23417659715860624925196467 35126489573790937387794701)
            ·
              refine ⟨13172433590171601520423013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35126489573790937387794701 13172433590171601520423013)
              ·
                refine ⟨2469831298157175285079315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13172433590171601520423013 2469831298157175285079315)
                ·
                  refine ⟨3704746947235762927618973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469831298157175285079315 3704746947235762927618973)
                  ·
                    refine ⟨1389280105213411097857115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3704746947235762927618973 1389280105213411097857115)
                    ·
                      rfl

theorem cell22_4058420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_4058420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4058420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4058420 prefixEnd_4058420 := by exact prefixLift 4058420
  have htrace : WordTrace (prefixWord ++ tailWord_4058420) baseStart_4058420 baseEnd_4058420 := by
    simpa [prefixWord, tailWord_4058420, baseEnd_4058420] using wordTrace_append hprefix tailTrace_4058420
  have hstable : (prefixWord ++ tailWord_4058420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058420).length < 2 ^ (prefixWord ++ tailWord_4058420).sum := by decide
  have hdescent : baseEnd_4058420 < baseStart_4058420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058444 : List Nat := [2, 2, 1, 3, 2, 2, 1, 1, 8]
def baseStart_4058444 : Nat := 118140960795 + 4058444 * 2 ^ 59
def prefixEnd_4058444 : Nat := 4983230072969 + 3 ^ 40 * 4058444 * 2
def baseEnd_4058444 : Nat := 463096106967961011752347

theorem tailTrace_4058444 : CollatzResearch.WordTrace tailWord_4058444 prefixEnd_4058444 463096106967961011752347 := by
  unfold tailWord_4058444
  simp only [CollatzResearch.WordTrace]
  refine ⟨74011806654478994948823193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98682408872638659931764257 74011806654478994948823193)
  ·
    refine ⟨55508854990859246211617395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74011806654478994948823193 55508854990859246211617395)
    ·
      refine ⟨83263282486288869317426093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55508854990859246211617395 83263282486288869317426093)
      ·
        refine ⟨31223730932358325994034785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83263282486288869317426093 31223730932358325994034785)
        ·
          refine ⟨23417798199268744495526089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31223730932358325994034785 23417798199268744495526089)
          ·
            refine ⟨17563348649451558371644567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23417798199268744495526089 17563348649451558371644567)
            ·
              refine ⟨26345022974177337557466851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17563348649451558371644567 26345022974177337557466851)
              ·
                refine ⟨39517534461266006336200277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26345022974177337557466851 39517534461266006336200277)
                ·
                  refine ⟨463096106967961011752347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39517534461266006336200277 463096106967961011752347)
                  ·
                    rfl

theorem cell22_4058444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 8].length) (baseStart_4058444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4058444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4058444 prefixEnd_4058444 := by exact prefixLift 4058444
  have htrace : WordTrace (prefixWord ++ tailWord_4058444) baseStart_4058444 baseEnd_4058444 := by
    simpa [prefixWord, tailWord_4058444, baseEnd_4058444] using wordTrace_append hprefix tailTrace_4058444
  have hstable : (prefixWord ++ tailWord_4058444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058444).length < 2 ^ (prefixWord ++ tailWord_4058444).sum := by decide
  have hdescent : baseEnd_4058444 < baseStart_4058444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058446 : List Nat := [4, 1, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_4058446 : Nat := 118140960795 + 4058446 * 2 ^ 59
def prefixEnd_4058446 : Nat := 4983230072969 + 3 ^ 40 * 4058446 * 2
def baseEnd_4058446 : Nat := 1389289005544755696707035

theorem tailTrace_4058446 : CollatzResearch.WordTrace tailWord_4058446 prefixEnd_4058446 1389289005544755696707035 := by
  unfold tailWord_4058446
  simp only [CollatzResearch.WordTrace]
  refine ⟨18502960781868843029902399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98682457503300496159479461 18502960781868843029902399)
  ·
    refine ⟨27754441172803264544853599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18502960781868843029902399 27754441172803264544853599)
    ·
      refine ⟨41631661759204896817280399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27754441172803264544853599 41631661759204896817280399)
      ·
        refine ⟨62447492638807345225920599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41631661759204896817280399 62447492638807345225920599)
        ·
          refine ⟨93671238958211017838880899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62447492638807345225920599 93671238958211017838880899)
          ·
            refine ⟨140506858437316526758321349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93671238958211017838880899 140506858437316526758321349)
            ·
              refine ⟨26345035956996848767185253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 140506858437316526758321349 26345035956996848767185253)
              ·
                refine ⟨4939694241936909143847235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26345035956996848767185253 4939694241936909143847235)
                ·
                  refine ⟨7409541362905363715770853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4939694241936909143847235 7409541362905363715770853)
                  ·
                    refine ⟨1389289005544755696707035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7409541362905363715770853 1389289005544755696707035)
                    ·
                      rfl

theorem cell22_4058446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_4058446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4058446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4058446 prefixEnd_4058446 := by exact prefixLift 4058446
  have htrace : WordTrace (prefixWord ++ tailWord_4058446) baseStart_4058446 baseEnd_4058446 := by
    simpa [prefixWord, tailWord_4058446, baseEnd_4058446] using wordTrace_append hprefix tailTrace_4058446
  have hstable : (prefixWord ++ tailWord_4058446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058446).length < 2 ^ (prefixWord ++ tailWord_4058446).sum := by decide
  have hdescent : baseEnd_4058446 < baseStart_4058446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058519 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 1, 8]
def baseStart_4058519 : Nat := 118140960795 + 4058519 * 2 ^ 59
def prefixEnd_4058519 : Nat := 4983230072969 + 3 ^ 40 * 4058519 * 2
def baseEnd_4058519 : Nat := 1389313994936607839631811

theorem tailTrace_4058519 : CollatzResearch.WordTrace tailWord_4058519 prefixEnd_4058519 1389313994936607839631811 := by
  unfold tailWord_4058519
  simp only [CollatzResearch.WordTrace]
  refine ⟨148026348783686277706626611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98684232522457518471084407 148026348783686277706626611)
  ·
    refine ⟨222039523175529416559939917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148026348783686277706626611 222039523175529416559939917)
    ·
      refine ⟨83264821190823531209977469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222039523175529416559939917 83264821190823531209977469)
      ·
        refine ⟨31224307946558824203741551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83264821190823531209977469 31224307946558824203741551)
        ·
          refine ⟨46836461919838236305612327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31224307946558824203741551 46836461919838236305612327)
          ·
            refine ⟨70254692879757354458418491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46836461919838236305612327 70254692879757354458418491)
            ·
              refine ⟨105382039319636031687627737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70254692879757354458418491 105382039319636031687627737)
              ·
                refine ⟨79036529489727023765720803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105382039319636031687627737 79036529489727023765720803)
                ·
                  refine ⟨118554794234590535648581205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79036529489727023765720803 118554794234590535648581205)
                  ·
                    refine ⟨1389313994936607839631811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118554794234590535648581205 1389313994936607839631811)
                    ·
                      rfl

theorem cell22_4058519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_4058519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4058519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4058519 prefixEnd_4058519 := by exact prefixLift 4058519
  have htrace : WordTrace (prefixWord ++ tailWord_4058519) baseStart_4058519 baseEnd_4058519 := by
    simpa [prefixWord, tailWord_4058519, baseEnd_4058519] using wordTrace_append hprefix tailTrace_4058519
  have hstable : (prefixWord ++ tailWord_4058519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058519).length < 2 ^ (prefixWord ++ tailWord_4058519).sum := by decide
  have hdescent : baseEnd_4058519 < baseStart_4058519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058551 : List Nat := [1, 1, 3, 1, 3, 2, 3, 3, 5]
def baseStart_4058551 : Nat := 118140960795 + 4058551 * 2 ^ 59
def prefixEnd_4058551 : Nat := 4983230072969 + 3 ^ 40 * 4058551 * 2
def baseEnd_4058551 : Nat := 463108316396856807610571

theorem tailTrace_4058551 : CollatzResearch.WordTrace tailWord_4058551 prefixEnd_4058551 463108316396856807610571 := by
  unfold tailWord_4058551
  simp only [CollatzResearch.WordTrace]
  refine ⟨148027515919570347171791507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98685010613046898114527671 148027515919570347171791507)
  ·
    refine ⟨222041273879355520757687261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148027515919570347171791507 222041273879355520757687261)
    ·
      refine ⟨83265477704758320284132723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222041273879355520757687261 83265477704758320284132723)
      ·
        refine ⟨124898216557137480426199085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83265477704758320284132723 124898216557137480426199085)
        ·
          refine ⟨46836831208926555159824657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124898216557137480426199085 46836831208926555159824657)
          ·
            refine ⟨35127623406694916369868493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46836831208926555159824657 35127623406694916369868493)
            ·
              refine ⟨13172858777510593638700685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35127623406694916369868493 13172858777510593638700685)
              ·
                refine ⟨4939822041566472614512757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13172858777510593638700685 4939822041566472614512757)
                ·
                  refine ⟨463108316396856807610571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4939822041566472614512757 463108316396856807610571)
                  ·
                    rfl

theorem cell22_4058551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 5].length) (baseStart_4058551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4058551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4058551 prefixEnd_4058551 := by exact prefixLift 4058551
  have htrace : WordTrace (prefixWord ++ tailWord_4058551) baseStart_4058551 baseEnd_4058551 := by
    simpa [prefixWord, tailWord_4058551, baseEnd_4058551] using wordTrace_append hprefix tailTrace_4058551
  have hstable : (prefixWord ++ tailWord_4058551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058551).length < 2 ^ (prefixWord ++ tailWord_4058551).sum := by decide
  have hdescent : baseEnd_4058551 < baseStart_4058551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058589 : List Nat := [1, 4, 3, 1, 1, 4, 2, 2, 1, 3]
def baseStart_4058589 : Nat := 118140960795 + 4058589 * 2 ^ 59
def prefixEnd_4058589 : Nat := 4983230072969 + 3 ^ 40 * 4058589 * 2
def baseEnd_4058589 : Nat := 1389337957367150990381597

theorem tailTrace_4058589 : CollatzResearch.WordTrace tailWord_4058589 prefixEnd_4058589 1389337957367150990381597 := by
  unfold tailWord_4058589
  simp only [CollatzResearch.WordTrace]
  refine ⟨148028901893432679661674821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98685934595621786441116547 148028901893432679661674821)
  ·
    refine ⟨27755419105018627436564029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148028901893432679661674821 27755419105018627436564029)
    ·
      refine ⟨10408282164381985288711511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27755419105018627436564029 10408282164381985288711511)
      ·
        refine ⟨15612423246572977933067267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10408282164381985288711511 15612423246572977933067267)
        ·
          refine ⟨23418634869859466899600901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15612423246572977933067267 23418634869859466899600901)
          ·
            refine ⟨4390994038098650043675169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23418634869859466899600901 4390994038098650043675169)
            ·
              refine ⟨3293245528573987532756377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4390994038098650043675169 3293245528573987532756377)
              ·
                refine ⟨2469934146430490649567283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3293245528573987532756377 2469934146430490649567283)
                ·
                  refine ⟨3704901219645735974350925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2469934146430490649567283 3704901219645735974350925)
                  ·
                    refine ⟨1389337957367150990381597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3704901219645735974350925 1389337957367150990381597)
                    ·
                      rfl

theorem cell22_4058589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_4058589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4058589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4058589 prefixEnd_4058589 := by exact prefixLift 4058589
  have htrace : WordTrace (prefixWord ++ tailWord_4058589) baseStart_4058589 baseEnd_4058589 := by
    simpa [prefixWord, tailWord_4058589, baseEnd_4058589] using wordTrace_append hprefix tailTrace_4058589
  have hstable : (prefixWord ++ tailWord_4058589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058589).length < 2 ^ (prefixWord ++ tailWord_4058589).sum := by decide
  have hdescent : baseEnd_4058589 < baseStart_4058589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058613 : List Nat := [1, 3, 5, 1, 1, 1, 1, 1, 8]
def baseStart_4058613 : Nat := 118140960795 + 4058613 * 2 ^ 59
def prefixEnd_4058613 : Nat := 4983230072969 + 3 ^ 40 * 4058613 * 2
def baseEnd_4058613 : Nat := 463115391019207642593841

theorem tailTrace_4058613 : CollatzResearch.WordTrace tailWord_4058613 prefixEnd_4058613 463115391019207642593841 := by
  unfold tailWord_4058613
  simp only [CollatzResearch.WordTrace]
  refine ⟨148029777245345731760548493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98686518163563821173698995 148029777245345731760548493)
  ·
    refine ⟨55511166467004649410205685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148029777245345731760548493 55511166467004649410205685)
    ·
      refine ⟨5204171856281685882206783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55511166467004649410205685 5204171856281685882206783)
      ·
        refine ⟨7806257784422528823310175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5204171856281685882206783 7806257784422528823310175)
        ·
          refine ⟨11709386676633793234965263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7806257784422528823310175 11709386676633793234965263)
          ·
            refine ⟨17564080014950689852447895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11709386676633793234965263 17564080014950689852447895)
            ·
              refine ⟨26346120022426034778671843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17564080014950689852447895 26346120022426034778671843)
              ·
                refine ⟨39519180033639052168007765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26346120022426034778671843 39519180033639052168007765)
                ·
                  refine ⟨463115391019207642593841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39519180033639052168007765 463115391019207642593841)
                  ·
                    rfl

theorem cell22_4058613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_4058613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4058613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4058613 prefixEnd_4058613 := by exact prefixLift 4058613
  have htrace : WordTrace (prefixWord ++ tailWord_4058613) baseStart_4058613 baseEnd_4058613 := by
    simpa [prefixWord, tailWord_4058613, baseEnd_4058613] using wordTrace_append hprefix tailTrace_4058613
  have hstable : (prefixWord ++ tailWord_4058613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058613).length < 2 ^ (prefixWord ++ tailWord_4058613).sum := by decide
  have hdescent : baseEnd_4058613 < baseStart_4058613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058645 : List Nat := [1, 3, 2, 1, 3, 2, 3, 2, 2, 3]
def baseStart_4058645 : Nat := 118140960795 + 4058645 * 2 ^ 59
def prefixEnd_4058645 : Nat := 4983230072969 + 3 ^ 40 * 4058645 * 2
def baseEnd_4058645 : Nat := 1389357127311585510981425

theorem tailTrace_4058645 : CollatzResearch.WordTrace tailWord_4058645 prefixEnd_4058645 1389357127311585510981425 := by
  unfold tailWord_4058645
  simp only [CollatzResearch.WordTrace]
  refine ⟨148030944381229801225713389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98687296254153200817142259 148030944381229801225713389)
  ·
    refine ⟨55511604142961175459642521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148030944381229801225713389 55511604142961175459642521)
    ·
      refine ⟨41633703107220881594731891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55511604142961175459642521 41633703107220881594731891)
      ·
        refine ⟨62450554660831322392097837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41633703107220881594731891 62450554660831322392097837)
        ·
          refine ⟨23418957997811745897036689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62450554660831322392097837 23418957997811745897036689)
          ·
            refine ⟨17564218498358809422777517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23418957997811745897036689 17564218498358809422777517)
            ·
              refine ⟨6586581936884553533541569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17564218498358809422777517 6586581936884553533541569)
              ·
                refine ⟨4939936452663415150156177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6586581936884553533541569 4939936452663415150156177)
                ·
                  refine ⟨3704952339497561362617133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4939936452663415150156177 3704952339497561362617133)
                  ·
                    refine ⟨1389357127311585510981425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3704952339497561362617133 1389357127311585510981425)
                    ·
                      rfl

theorem cell22_4058645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_4058645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4058645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4058645 prefixEnd_4058645 := by exact prefixLift 4058645
  have htrace : WordTrace (prefixWord ++ tailWord_4058645) baseStart_4058645 baseEnd_4058645 := by
    simpa [prefixWord, tailWord_4058645, baseEnd_4058645] using wordTrace_append hprefix tailTrace_4058645
  have hstable : (prefixWord ++ tailWord_4058645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058645).length < 2 ^ (prefixWord ++ tailWord_4058645).sum := by decide
  have hdescent : baseEnd_4058645 < baseStart_4058645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058814 : List Nat := [4, 2, 1, 1, 2, 4, 1, 2, 2, 3]
def baseStart_4058814 : Nat := 118140960795 + 4058814 * 2 ^ 59
def prefixEnd_4058814 : Nat := 4983230072969 + 3 ^ 40 * 4058814 * 2
def baseEnd_4058814 : Nat := 1389414979465325403505907

theorem tailTrace_4058814 : CollatzResearch.WordTrace tailWord_4058814 prefixEnd_4058814 1389414979465325403505907 := by
  unfold tailWord_4058814
  simp only [CollatzResearch.WordTrace]
  refine ⟨18504638539702192886076937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98691405545078362059076997 18504638539702192886076937)
  ·
    refine ⟨13878478904776644664557703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18504638539702192886076937 13878478904776644664557703)
    ·
      refine ⟨20817718357164966996836555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13878478904776644664557703 20817718357164966996836555)
      ·
        refine ⟨31226577535747450495254833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20817718357164966996836555 31226577535747450495254833)
        ·
          refine ⟨23419933151810587871441125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31226577535747450495254833 23419933151810587871441125)
          ·
            refine ⟨4391237465964485225895211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23419933151810587871441125 4391237465964485225895211)
            ·
              refine ⟨6586856198946727838842817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4391237465964485225895211 6586856198946727838842817)
              ·
                refine ⟨4940142149210045879132113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6586856198946727838842817 4940142149210045879132113)
                ·
                  refine ⟨3705106611907534409349085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4940142149210045879132113 3705106611907534409349085)
                  ·
                    refine ⟨1389414979465325403505907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3705106611907534409349085 1389414979465325403505907)
                    ·
                      rfl

theorem cell22_4058814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_4058814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4058814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4058814 prefixEnd_4058814 := by exact prefixLift 4058814
  have htrace : WordTrace (prefixWord ++ tailWord_4058814) baseStart_4058814 baseEnd_4058814 := by
    simpa [prefixWord, tailWord_4058814, baseEnd_4058814] using wordTrace_append hprefix tailTrace_4058814
  have hstable : (prefixWord ++ tailWord_4058814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058814).length < 2 ^ (prefixWord ++ tailWord_4058814).sum := by decide
  have hdescent : baseEnd_4058814 < baseStart_4058814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058844 : List Nat := [2, 2, 5, 1, 2, 2, 2, 6]
def baseStart_4058844 : Nat := 118140960795 + 4058844 * 2 ^ 59
def prefixEnd_4058844 : Nat := 4983230072969 + 3 ^ 40 * 4058844 * 2
def baseEnd_4058844 : Nat := 154380583230935036139535

theorem tailTrace_4058844 : CollatzResearch.WordTrace tailWord_4058844 prefixEnd_4058844 154380583230935036139535 := by
  unfold tailWord_4058844
  simp only [CollatzResearch.WordTrace]
  refine ⟨74019101253754429106103793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98692135005005905474805057 74019101253754429106103793)
  ·
    refine ⟨55514325940315821829577845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74019101253754429106103793 55514325940315821829577845)
    ·
      refine ⟨5204468056904608296522923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55514325940315821829577845 5204468056904608296522923)
      ·
        refine ⟨7806702085356912444784385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5204468056904608296522923 7806702085356912444784385)
        ·
          refine ⟨5855026564017684333588289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7806702085356912444784385 5855026564017684333588289)
          ·
            refine ⟨4391269923013263250191217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5855026564017684333588289 4391269923013263250191217)
            ·
              refine ⟨3293452442259947437643413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4391269923013263250191217 3293452442259947437643413)
              ·
                refine ⟨154380583230935036139535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3293452442259947437643413 154380583230935036139535)
                ·
                  rfl

theorem cell22_4058844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 6].length) (baseStart_4058844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4058844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4058844 prefixEnd_4058844 := by exact prefixLift 4058844
  have htrace : WordTrace (prefixWord ++ tailWord_4058844) baseStart_4058844 baseEnd_4058844 := by
    simpa [prefixWord, tailWord_4058844, baseEnd_4058844] using wordTrace_append hprefix tailTrace_4058844
  have hstable : (prefixWord ++ tailWord_4058844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058844).length < 2 ^ (prefixWord ++ tailWord_4058844).sum := by decide
  have hdescent : baseEnd_4058844 < baseStart_4058844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058915 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 6, 3]
def baseStart_4058915 : Nat := 118140960795 + 4058915 * 2 ^ 59
def prefixEnd_4058915 : Nat := 4983230072969 + 3 ^ 40 * 4058915 * 2
def baseEnd_4058915 : Nat := 1389449553829394806730597

theorem tailTrace_4058915 : CollatzResearch.WordTrace tailWord_4058915 prefixEnd_4058915 1389449553829394806730597 := by
  unfold tailWord_4058915
  simp only [CollatzResearch.WordTrace]
  refine ⟨148040792090251637338042199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98693861393501091558694799 148040792090251637338042199)
  ·
    refine ⟨222061188135377456007063299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148040792090251637338042199 222061188135377456007063299)
    ·
      refine ⟨333091782203066184010594949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222061188135377456007063299 333091782203066184010594949)
      ·
        refine ⟨62454709163074909501986553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333091782203066184010594949 62454709163074909501986553)
        ·
          refine ⟨46841031872306182126489915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62454709163074909501986553 46841031872306182126489915)
          ·
            refine ⟨70261547808459273189734873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46841031872306182126489915 70261547808459273189734873)
            ·
              refine ⟨52696160856344454892301155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70261547808459273189734873 52696160856344454892301155)
              ·
                refine ⟨79044241284516682338451733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52696160856344454892301155 79044241284516682338451733)
                ·
                  refine ⟨3705198810211719484614925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 79044241284516682338451733 3705198810211719484614925)
                  ·
                    refine ⟨1389449553829394806730597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3705198810211719484614925 1389449553829394806730597)
                    ·
                      rfl

theorem cell22_4058915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 6, 3].length) (baseStart_4058915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4058915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4058915 prefixEnd_4058915 := by exact prefixLift 4058915
  have htrace : WordTrace (prefixWord ++ tailWord_4058915) baseStart_4058915 baseEnd_4058915 := by
    simpa [prefixWord, tailWord_4058915, baseEnd_4058915] using wordTrace_append hprefix tailTrace_4058915
  have hstable : (prefixWord ++ tailWord_4058915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058915).length < 2 ^ (prefixWord ++ tailWord_4058915).sum := by decide
  have hdescent : baseEnd_4058915 < baseStart_4058915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058962 : List Nat := [3, 2, 2, 1, 1, 4, 3, 6]
def baseStart_4058962 : Nat := 118140960795 + 4058962 * 2 ^ 59
def prefixEnd_4058962 : Nat := 4983230072969 + 3 ^ 40 * 4058962 * 2
def baseEnd_4058962 : Nat := 154385071432211372311717

theorem tailTrace_4058962 : CollatzResearch.WordTrace tailWord_4058962 prefixEnd_4058962 154385071432211372311717 := by
  unfold tailWord_4058962
  simp only [CollatzResearch.WordTrace]
  refine ⟨37010626580270341091250785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98695004214054242910002093 37010626580270341091250785)
  ·
    refine ⟨27757969935202755818438089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37010626580270341091250785 27757969935202755818438089)
    ·
      refine ⟨20818477451402066863828567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27757969935202755818438089 20818477451402066863828567)
      ·
        refine ⟨31227716177103100295742851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20818477451402066863828567 31227716177103100295742851)
        ·
          refine ⟨46841574265654650443614277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31227716177103100295742851 46841574265654650443614277)
          ·
            refine ⟨8782795174810246958177677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46841574265654650443614277 8782795174810246958177677)
            ·
              refine ⟨3293548190553842609316629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8782795174810246958177677 3293548190553842609316629)
              ·
                refine ⟨154385071432211372311717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3293548190553842609316629 154385071432211372311717)
                ·
                  rfl

theorem cell22_4058962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 6].length) (baseStart_4058962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4058962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4058962 prefixEnd_4058962 := by exact prefixLift 4058962
  have htrace : WordTrace (prefixWord ++ tailWord_4058962) baseStart_4058962 baseEnd_4058962 := by
    simpa [prefixWord, tailWord_4058962, baseEnd_4058962] using wordTrace_append hprefix tailTrace_4058962
  have hstable : (prefixWord ++ tailWord_4058962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058962).length < 2 ^ (prefixWord ++ tailWord_4058962).sum := by decide
  have hdescent : baseEnd_4058962 < baseStart_4058962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4058964 : List Nat := [2, 4, 1, 1, 3, 3, 1, 1, 2, 4]
def baseStart_4058964 : Nat := 118140960795 + 4058964 * 2 ^ 59
def prefixEnd_4058964 : Nat := 4983230072969 + 3 ^ 40 * 4058964 * 2
def baseEnd_4058964 : Nat := 1389466327530775012255447

theorem tailTrace_4058964 : CollatzResearch.WordTrace tailWord_4058964 prefixEnd_4058964 1389466327530775012255447 := by
  unfold tailWord_4058964
  simp only [CollatzResearch.WordTrace]
  refine ⟨74021289633537059353287973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98695052844716079137717297 74021289633537059353287973)
  ·
    refine ⟨13878991806288198628741495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74021289633537059353287973 13878991806288198628741495)
    ·
      refine ⟨20818487709432297943112243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13878991806288198628741495 20818487709432297943112243)
      ·
        refine ⟨31227731564148446914668365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20818487709432297943112243 31227731564148446914668365)
        ·
          refine ⟨11710399336555667593000637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31227731564148446914668365 11710399336555667593000637)
          ·
            refine ⟨4391399751208375347375239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11710399336555667593000637 4391399751208375347375239)
            ·
              refine ⟨6587099626812563021062859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4391399751208375347375239 6587099626812563021062859)
              ·
                refine ⟨9880649440218844531594289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6587099626812563021062859 9880649440218844531594289)
                ·
                  refine ⟨7410487080164133398695717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9880649440218844531594289 7410487080164133398695717)
                  ·
                    refine ⟨1389466327530775012255447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7410487080164133398695717 1389466327530775012255447)
                    ·
                      rfl

theorem cell22_4058964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_4058964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4058964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4058964 prefixEnd_4058964 := by exact prefixLift 4058964
  have htrace : WordTrace (prefixWord ++ tailWord_4058964) baseStart_4058964 baseEnd_4058964 := by
    simpa [prefixWord, tailWord_4058964, baseEnd_4058964] using wordTrace_append hprefix tailTrace_4058964
  have hstable : (prefixWord ++ tailWord_4058964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4058964).length < 2 ^ (prefixWord ++ tailWord_4058964).sum := by decide
  have hdescent : baseEnd_4058964 < baseStart_4058964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4058964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059028 : List Nat := [2, 4, 2, 1, 1, 4, 1, 3, 1, 3]
def baseStart_4059028 : Nat := 118140960795 + 4059028 * 2 ^ 59
def prefixEnd_4059028 : Nat := 4983230072969 + 3 ^ 40 * 4059028 * 2
def baseEnd_4059028 : Nat := 1389488236038700178655251

theorem tailTrace_4059028 : CollatzResearch.WordTrace tailWord_4059028 prefixEnd_4059028 1389488236038700178655251 := by
  unfold tailWord_4059028
  simp only [CollatzResearch.WordTrace]
  refine ⟨74022456769421128818452869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98696609025894838424603825 74022456769421128818452869)
  ·
    refine ⟨13879210644266461653459913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74022456769421128818452869 13879210644266461653459913)
    ·
      refine ⟨10409407983199846240094935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13879210644266461653459913 10409407983199846240094935)
      ·
        refine ⟨15614111974799769360142403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10409407983199846240094935 15614111974799769360142403)
        ·
          refine ⟨23421167962199654040213605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15614111974799769360142403 23421167962199654040213605)
          ·
            refine ⟨4391468992912435132540051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23421167962199654040213605 4391468992912435132540051)
            ·
              refine ⟨6587203489368652698810077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4391468992912435132540051 6587203489368652698810077)
              ·
                refine ⟨2470201308513244762053779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6587203489368652698810077 2470201308513244762053779)
                ·
                  refine ⟨3705301962769867143080669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2470201308513244762053779 3705301962769867143080669)
                  ·
                    refine ⟨1389488236038700178655251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3705301962769867143080669 1389488236038700178655251)
                    ·
                      rfl

theorem cell22_4059028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 1, 3].length) (baseStart_4059028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059028 prefixEnd_4059028 := by exact prefixLift 4059028
  have htrace : WordTrace (prefixWord ++ tailWord_4059028) baseStart_4059028 baseEnd_4059028 := by
    simpa [prefixWord, tailWord_4059028, baseEnd_4059028] using wordTrace_append hprefix tailTrace_4059028
  have hstable : (prefixWord ++ tailWord_4059028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059028).length < 2 ^ (prefixWord ++ tailWord_4059028).sum := by decide
  have hdescent : baseEnd_4059028 < baseStart_4059028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059082 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 2, 4]
def baseStart_4059082 : Nat := 118140960795 + 4059082 * 2 ^ 59
def prefixEnd_4059082 : Nat := 4983230072969 + 3 ^ 40 * 4059082 * 2
def baseEnd_4059082 : Nat := 1389506721342262037805085

theorem tailTrace_4059082 : CollatzResearch.WordTrace tailWord_4059082 prefixEnd_4059082 1389506721342262037805085 := by
  unfold tailWord_4059082
  simp only [CollatzResearch.WordTrace]
  refine ⟨37011720770161656214842875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98697922053764416572914333 37011720770161656214842875)
  ·
    refine ⟨55517581155242484322264313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37011720770161656214842875 55517581155242484322264313)
    ·
      refine ⟨41638185866431863241698235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55517581155242484322264313 41638185866431863241698235)
      ·
        refine ⟨62457278799647794862547353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41638185866431863241698235 62457278799647794862547353)
        ·
          refine ⟨46842959099735846146910515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62457278799647794862547353 46842959099735846146910515)
          ·
            refine ⟨70264438649603769220365773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46842959099735846146910515 70264438649603769220365773)
            ·
              refine ⟨26349164493601413457637165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70264438649603769220365773 26349164493601413457637165)
              ·
                refine ⟨9880936685100530046613937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26349164493601413457637165 9880936685100530046613937)
                ·
                  refine ⟨7410702513825397534960453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9880936685100530046613937 7410702513825397534960453)
                  ·
                    refine ⟨1389506721342262037805085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7410702513825397534960453 1389506721342262037805085)
                    ·
                      rfl

theorem cell22_4059082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_4059082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059082 prefixEnd_4059082 := by exact prefixLift 4059082
  have htrace : WordTrace (prefixWord ++ tailWord_4059082) baseStart_4059082 baseEnd_4059082 := by
    simpa [prefixWord, tailWord_4059082, baseEnd_4059082] using wordTrace_append hprefix tailTrace_4059082
  have hstable : (prefixWord ++ tailWord_4059082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059082).length < 2 ^ (prefixWord ++ tailWord_4059082).sum := by decide
  have hdescent : baseEnd_4059082 < baseStart_4059082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059097 : List Nat := [1, 2, 1, 2, 7, 9]
def baseStart_4059097 : Nat := 118140960795 + 4059097 * 2 ^ 59
def prefixEnd_4059097 : Nat := 4983230072969 + 3 ^ 40 * 4059097 * 2
def baseEnd_4059097 : Nat := 17154467359861814798519

theorem tailTrace_4059097 : CollatzResearch.WordTrace tailWord_4059097 prefixEnd_4059097 17154467359861814798519 := by
  unfold tailWord_4059097
  simp only [CollatzResearch.WordTrace]
  refine ⟨148047430175592282421167545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98698286783728188280778363 148047430175592282421167545)
  ·
    refine ⟨111035572631694211815875659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148047430175592282421167545 111035572631694211815875659)
    ·
      refine ⟨166553358947541317723813489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111035572631694211815875659 166553358947541317723813489)
      ·
        refine ⟨124915019210655988292860117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166553358947541317723813489 124915019210655988292860117)
        ·
          refine ⟨2927695762749749725613909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 124915019210655988292860117 2927695762749749725613909)
          ·
            refine ⟨17154467359861814798519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2927695762749749725613909 17154467359861814798519)
            ·
              rfl

theorem cell22_4059097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 9].length) (baseStart_4059097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059097 prefixEnd_4059097 := by exact prefixLift 4059097
  have htrace : WordTrace (prefixWord ++ tailWord_4059097) baseStart_4059097 baseEnd_4059097 := by
    simpa [prefixWord, tailWord_4059097, baseEnd_4059097] using wordTrace_append hprefix tailTrace_4059097
  have hstable : (prefixWord ++ tailWord_4059097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059097).length < 2 ^ (prefixWord ++ tailWord_4059097).sum := by decide
  have hdescent : baseEnd_4059097 < baseStart_4059097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059129 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 3, 3]
def baseStart_4059129 : Nat := 118140960795 + 4059129 * 2 ^ 59
def prefixEnd_4059129 : Nat := 4983230072969 + 3 ^ 40 * 4059129 * 2
def baseEnd_4059129 : Nat := 1389522810402769581879941

theorem tailTrace_4059129 : CollatzResearch.WordTrace tailWord_4059129 prefixEnd_4059129 1389522810402769581879941 := by
  unfold tailWord_4059129
  simp only [CollatzResearch.WordTrace]
  refine ⟨148048597311476351886332441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98699064874317567924221627 148048597311476351886332441)
  ·
    refine ⟨111036447983607263914749331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148048597311476351886332441 111036447983607263914749331)
    ·
      refine ⟨166554671975410895872123997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111036447983607263914749331 166554671975410895872123997)
      ·
        refine ⟨62458001990779085952046499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166554671975410895872123997 62458001990779085952046499)
        ·
          refine ⟨93687002986168628928069749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62458001990779085952046499 93687002986168628928069749)
          ·
            refine ⟨8783156529953308962006539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93687002986168628928069749 8783156529953308962006539)
            ·
              refine ⟨13174734794929963443009809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8783156529953308962006539 13174734794929963443009809)
              ·
                refine ⟨9881051096197472582257357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13174734794929963443009809 9881051096197472582257357)
                ·
                  refine ⟨3705394161074052218346509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9881051096197472582257357 3705394161074052218346509)
                  ·
                    refine ⟨1389522810402769581879941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3705394161074052218346509 1389522810402769581879941)
                    ·
                      rfl

theorem cell22_4059129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 3, 3].length) (baseStart_4059129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059129 prefixEnd_4059129 := by exact prefixLift 4059129
  have htrace : WordTrace (prefixWord ++ tailWord_4059129) baseStart_4059129 baseEnd_4059129 := by
    simpa [prefixWord, tailWord_4059129, baseEnd_4059129] using wordTrace_append hprefix tailTrace_4059129
  have hstable : (prefixWord ++ tailWord_4059129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059129).length < 2 ^ (prefixWord ++ tailWord_4059129).sum := by decide
  have hdescent : baseEnd_4059129 < baseStart_4059129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059159 : List Nat := [1, 1, 3, 5, 2, 1, 1, 1, 7]
def baseStart_4059159 : Nat := 118140960795 + 4059159 * 2 ^ 59
def prefixEnd_4059159 : Nat := 4983230072969 + 3 ^ 40 * 4059159 * 2
def baseEnd_4059159 : Nat := 463177693338619834543283

theorem tailTrace_4059159 : CollatzResearch.WordTrace tailWord_4059159 prefixEnd_4059159 463177693338619834543283 := by
  unfold tailWord_4059159
  simp only [CollatzResearch.WordTrace]
  refine ⟨148049691501367667009924531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98699794334245111339949687 148049691501367667009924531)
  ·
    refine ⟨222074537252051500514886797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148049691501367667009924531 222074537252051500514886797)
    ·
      refine ⟨83277951469519312693082549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222074537252051500514886797 83277951469519312693082549)
      ·
        refine ⟨7807307950267435564976489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83277951469519312693082549 7807307950267435564976489)
        ·
          refine ⟨5855480962700576673732367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7807307950267435564976489 5855480962700576673732367)
          ·
            refine ⟨8783221444050865010598551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5855480962700576673732367 8783221444050865010598551)
            ·
              refine ⟨13174832166076297515897827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8783221444050865010598551 13174832166076297515897827)
              ·
                refine ⟨19762248249114446273846741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13174832166076297515897827 19762248249114446273846741)
                ·
                  refine ⟨463177693338619834543283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19762248249114446273846741 463177693338619834543283)
                  ·
                    rfl

theorem cell22_4059159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 1, 7].length) (baseStart_4059159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059159 prefixEnd_4059159 := by exact prefixLift 4059159
  have htrace : WordTrace (prefixWord ++ tailWord_4059159) baseStart_4059159 baseEnd_4059159 := by
    simpa [prefixWord, tailWord_4059159, baseEnd_4059159] using wordTrace_append hprefix tailTrace_4059159
  have hstable : (prefixWord ++ tailWord_4059159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059159).length < 2 ^ (prefixWord ++ tailWord_4059159).sum := by decide
  have hdescent : baseEnd_4059159 < baseStart_4059159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059187 : List Nat := [1, 1, 1, 2, 4, 1, 4, 2, 6]
def baseStart_4059187 : Nat := 118140960795 + 4059187 * 2 ^ 59
def prefixEnd_4059187 : Nat := 4983230072969 + 3 ^ 40 * 4059187 * 2
def baseEnd_4059187 : Nat := 463180888329358921309921

theorem tailTrace_4059187 : CollatzResearch.WordTrace tailWord_4059187 prefixEnd_4059187 463180888329358921309921 := by
  unfold tailWord_4059187
  simp only [CollatzResearch.WordTrace]
  refine ⟨148050712745266227791943815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98700475163510818527962543 148050712745266227791943815)
  ·
    refine ⟨222076069117899341687915723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148050712745266227791943815 222076069117899341687915723)
    ·
      refine ⟨333114103676849012531873585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222076069117899341687915723 333114103676849012531873585)
      ·
        refine ⟨249835577757636759398905189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333114103676849012531873585 249835577757636759398905189)
        ·
          refine ⟨46844170829556892387294723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 249835577757636759398905189 46844170829556892387294723)
          ·
            refine ⟨70266256244335338580942085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46844170829556892387294723 70266256244335338580942085)
            ·
              refine ⟨13174923045812875983926641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70266256244335338580942085 13174923045812875983926641)
              ·
                refine ⟨9881192284359656987944981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13174923045812875983926641 9881192284359656987944981)
                ·
                  refine ⟨463180888329358921309921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9881192284359656987944981 463180888329358921309921)
                  ·
                    rfl

theorem cell22_4059187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 2, 6].length) (baseStart_4059187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059187 prefixEnd_4059187 := by exact prefixLift 4059187
  have htrace : WordTrace (prefixWord ++ tailWord_4059187) baseStart_4059187 baseEnd_4059187 := by
    simpa [prefixWord, tailWord_4059187, baseEnd_4059187] using wordTrace_append hprefix tailTrace_4059187
  have hstable : (prefixWord ++ tailWord_4059187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059187).length < 2 ^ (prefixWord ++ tailWord_4059187).sum := by decide
  have hdescent : baseEnd_4059187 < baseStart_4059187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059189 : List Nat := [1, 3, 3, 1, 1, 1, 3, 4, 1, 4]
def baseStart_4059189 : Nat := 118140960795 + 4059189 * 2 ^ 59
def prefixEnd_4059189 : Nat := 4983230072969 + 3 ^ 40 * 4059189 * 2
def baseEnd_4059189 : Nat := 1389543349628949425379757

theorem tailTrace_4059189 : CollatzResearch.WordTrace tailWord_4059189 prefixEnd_4059189 1389543349628949425379757 := by
  unfold tailWord_4059189
  simp only [CollatzResearch.WordTrace]
  refine ⟨148050785691258982133516621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98700523794172654755677747 148050785691258982133516621)
  ·
    refine ⟨55519044634222118300068733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148050785691258982133516621 55519044634222118300068733)
    ·
      refine ⟨20819641737833294362525775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55519044634222118300068733 20819641737833294362525775)
      ·
        refine ⟨31229462606749941543788663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20819641737833294362525775 31229462606749941543788663)
        ·
          refine ⟨46844193910124912315682995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31229462606749941543788663 46844193910124912315682995)
          ·
            refine ⟨70266290865187368473524493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46844193910124912315682995 70266290865187368473524493)
            ·
              refine ⟨26349859074445263177571685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70266290865187368473524493 26349859074445263177571685)
              ·
                refine ⟨4940598576458486845794691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26349859074445263177571685 4940598576458486845794691)
                ·
                  refine ⟨7410897864687730268692037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4940598576458486845794691 7410897864687730268692037)
                  ·
                    refine ⟨1389543349628949425379757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7410897864687730268692037 1389543349628949425379757)
                    ·
                      rfl

theorem cell22_4059189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_4059189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059189 prefixEnd_4059189 := by exact prefixLift 4059189
  have htrace : WordTrace (prefixWord ++ tailWord_4059189) baseStart_4059189 baseEnd_4059189 := by
    simpa [prefixWord, tailWord_4059189, baseEnd_4059189] using wordTrace_append hprefix tailTrace_4059189
  have hstable : (prefixWord ++ tailWord_4059189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059189).length < 2 ^ (prefixWord ++ tailWord_4059189).sum := by decide
  have hdescent : baseEnd_4059189 < baseStart_4059189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059232 : List Nat := [2, 1, 1, 3, 2, 3, 1, 9]
def baseStart_4059232 : Nat := 118140960795 + 4059232 * 2 ^ 59
def prefixEnd_4059232 : Nat := 4983230072969 + 3 ^ 40 * 4059232 * 2
def baseEnd_4059232 : Nat := 154395341045301294061625

theorem tailTrace_4059232 : CollatzResearch.WordTrace tailWord_4059232 prefixEnd_4059232 154395341045301294061625 := by
  unfold tailWord_4059232
  simp only [CollatzResearch.WordTrace]
  refine ⟨74026177015051600238665975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98701569353402133651554633 74026177015051600238665975)
  ·
    refine ⟨111039265522577400357998963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74026177015051600238665975 111039265522577400357998963)
    ·
      refine ⟨166558898283866100536998445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111039265522577400357998963 166558898283866100536998445)
      ·
        refine ⟨62459586856449787701374417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166558898283866100536998445 62459586856449787701374417)
        ·
          refine ⟨46844690142337340776030813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62459586856449787701374417 46844690142337340776030813)
          ·
            refine ⟨17566758803376502791011555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46844690142337340776030813 17566758803376502791011555)
            ·
              refine ⟨26350138205064754186517333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17566758803376502791011555 26350138205064754186517333)
              ·
                refine ⟨154395341045301294061625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26350138205064754186517333 154395341045301294061625)
                ·
                  rfl

theorem cell22_4059232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 9].length) (baseStart_4059232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059232 prefixEnd_4059232 := by exact prefixLift 4059232
  have htrace : WordTrace (prefixWord ++ tailWord_4059232) baseStart_4059232 baseEnd_4059232 := by
    simpa [prefixWord, tailWord_4059232, baseEnd_4059232] using wordTrace_append hprefix tailTrace_4059232
  have hstable : (prefixWord ++ tailWord_4059232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059232).length < 2 ^ (prefixWord ++ tailWord_4059232).sum := by decide
  have hdescent : baseEnd_4059232 < baseStart_4059232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059298 : List Nat := [3, 3, 1, 3, 1, 2, 1, 2, 3, 3]
def baseStart_4059298 : Nat := 118140960795 + 4059298 * 2 ^ 59
def prefixEnd_4059298 : Nat := 4983230072969 + 3 ^ 40 * 4059298 * 2
def baseEnd_4059298 : Nat := 1389580662556509474404423

theorem tailTrace_4059298 : CollatzResearch.WordTrace tailWord_4059298 prefixEnd_4059298 1389580662556509474404423 := by
  unfold tailWord_4059298
  simp only [CollatzResearch.WordTrace]
  refine ⟨37013690311966023437308637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98703174165242729166156365 37013690311966023437308637)
  ·
    refine ⟨13880133866987258788990739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37013690311966023437308637 13880133866987258788990739)
    ·
      refine ⟨20820200800480888183486109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13880133866987258788990739 20820200800480888183486109)
      ·
        refine ⟨7807575300180333068807291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20820200800480888183486109 7807575300180333068807291)
        ·
          refine ⟨11711362950270499603210937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7807575300180333068807291 11711362950270499603210937)
          ·
            refine ⟨8783522212702874702408203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11711362950270499603210937 8783522212702874702408203)
            ·
              refine ⟨13175283319054312053612305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8783522212702874702408203 13175283319054312053612305)
              ·
                refine ⟨9881462489290734040209229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13175283319054312053612305 9881462489290734040209229)
                ·
                  refine ⟨3705548433484025265078461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9881462489290734040209229 3705548433484025265078461)
                  ·
                    refine ⟨1389580662556509474404423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3705548433484025265078461 1389580662556509474404423)
                    ·
                      rfl

theorem cell22_4059298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 3, 3].length) (baseStart_4059298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059298 prefixEnd_4059298 := by exact prefixLift 4059298
  have htrace : WordTrace (prefixWord ++ tailWord_4059298) baseStart_4059298 baseEnd_4059298 := by
    simpa [prefixWord, tailWord_4059298, baseEnd_4059298] using wordTrace_append hprefix tailTrace_4059298
  have hstable : (prefixWord ++ tailWord_4059298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059298).length < 2 ^ (prefixWord ++ tailWord_4059298).sum := by decide
  have hdescent : baseEnd_4059298 < baseStart_4059298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059339 : List Nat := [1, 1, 1, 1, 3, 2, 6, 1, 6]
def baseStart_4059339 : Nat := 118140960795 + 4059339 * 2 ^ 59
def prefixEnd_4059339 : Nat := 4983230072969 + 3 ^ 40 * 4059339 * 2
def baseEnd_4059339 : Nat := 463198232564799678043099

theorem tailTrace_4059339 : CollatzResearch.WordTrace tailWord_4059339 prefixEnd_4059339 463198232564799678043099 := by
  unfold tailWord_4059339
  simp only [CollatzResearch.WordTrace]
  refine ⟨148056256640715557751477071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98704171093810371834318047 148056256640715557751477071)
  ·
    refine ⟨222084384961073336627215607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148056256640715557751477071 222084384961073336627215607)
    ·
      refine ⟨333126577441610004940823411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222084384961073336627215607 333126577441610004940823411)
      ·
        refine ⟨499689866162415007411235117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333126577441610004940823411 499689866162415007411235117)
        ·
          refine ⟨187383699810905627779213169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 499689866162415007411235117 187383699810905627779213169)
          ·
            refine ⟨140537774858179220834409877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 187383699810905627779213169 140537774858179220834409877)
            ·
              refine ⟨6587708196477150976612963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140537774858179220834409877 6587708196477150976612963)
              ·
                refine ⟨9881562294715726464919445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6587708196477150976612963 9881562294715726464919445)
                ·
                  refine ⟨463198232564799678043099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9881562294715726464919445 463198232564799678043099)
                  ·
                    rfl

theorem cell22_4059339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 1, 6].length) (baseStart_4059339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059339 prefixEnd_4059339 := by exact prefixLift 4059339
  have htrace : WordTrace (prefixWord ++ tailWord_4059339) baseStart_4059339 baseEnd_4059339 := by
    simpa [prefixWord, tailWord_4059339, baseEnd_4059339] using wordTrace_append hprefix tailTrace_4059339
  have hstable : (prefixWord ++ tailWord_4059339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059339).length < 2 ^ (prefixWord ++ tailWord_4059339).sum := by decide
  have hdescent : baseEnd_4059339 < baseStart_4059339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059386 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 2, 4]
def baseStart_4059386 : Nat := 118140960795 + 4059386 * 2 ^ 59
def prefixEnd_4059386 : Nat := 4983230072969 + 3 ^ 40 * 4059386 * 2
def baseEnd_4059386 : Nat := 1389610786754906578204153

theorem tailTrace_4059386 : CollatzResearch.WordTrace tailWord_4059386 prefixEnd_4059386 1389610786754906578204153 := by
  unfold tailWord_4059386
  simp only [CollatzResearch.WordTrace]
  refine ⟨37014492717886321194609503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98705313914363523185625341 37014492717886321194609503)
  ·
    refine ⟨55521739076829481791914255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37014492717886321194609503 55521739076829481791914255)
    ·
      refine ⟨83282608615244222687871383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55521739076829481791914255 83282608615244222687871383)
      ·
        refine ⟨124923912922866334031807075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83282608615244222687871383 124923912922866334031807075)
        ·
          refine ⟨187385869384299501047710613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124923912922866334031807075 187385869384299501047710613)
          ·
            refine ⟨8783712627389039111611435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187385869384299501047710613 8783712627389039111611435)
            ·
              refine ⟨13175568941083558667417153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8783712627389039111611435 13175568941083558667417153)
              ·
                refine ⟨9881676705812669000562865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13175568941083558667417153 9881676705812669000562865)
                ·
                  refine ⟨7411257529359501750422149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9881676705812669000562865 7411257529359501750422149)
                  ·
                    refine ⟨1389610786754906578204153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7411257529359501750422149 1389610786754906578204153)
                    ·
                      rfl

theorem cell22_4059386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_4059386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059386 prefixEnd_4059386 := by exact prefixLift 4059386
  have htrace : WordTrace (prefixWord ++ tailWord_4059386) baseStart_4059386 baseEnd_4059386 := by
    simpa [prefixWord, tailWord_4059386, baseEnd_4059386] using wordTrace_append hprefix tailTrace_4059386
  have hstable : (prefixWord ++ tailWord_4059386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059386).length < 2 ^ (prefixWord ++ tailWord_4059386).sum := by decide
  have hdescent : baseEnd_4059386 < baseStart_4059386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059390 : List Nat := [4, 2, 2, 1, 1, 1, 5, 2, 4]
def baseStart_4059390 : Nat := 118140960795 + 4059390 * 2 ^ 59
def prefixEnd_4059390 : Nat := 4983230072969 + 3 ^ 40 * 4059390 * 2
def baseEnd_4059390 : Nat := 463204052012217300368047

theorem tailTrace_4059390 : CollatzResearch.WordTrace tailWord_4059390 prefixEnd_4059390 463204052012217300368047 := by
  unfold tailWord_4059390
  simp only [CollatzResearch.WordTrace]
  refine ⟨18507264595441349182697953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98705411175687195641055749 18507264595441349182697953)
  ·
    refine ⟨13880448446581011887023465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18507264595441349182697953 13880448446581011887023465)
    ·
      refine ⟨10410336334935758915267599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13880448446581011887023465 10410336334935758915267599)
      ·
        refine ⟨15615504502403638372901399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10410336334935758915267599 15615504502403638372901399)
        ·
          refine ⟨23423256753605457559352099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15615504502403638372901399 23423256753605457559352099)
          ·
            refine ⟨35134885130408186339028149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23423256753605457559352099 35134885130408186339028149)
            ·
              refine ⟨3293895480975767469283889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35134885130408186339028149 3293895480975767469283889)
              ·
                refine ⟨2470421610731825601962917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3293895480975767469283889 2470421610731825601962917)
                ·
                  refine ⟨463204052012217300368047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2470421610731825601962917 463204052012217300368047)
                  ·
                    rfl

theorem cell22_4059390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_4059390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059390 prefixEnd_4059390 := by exact prefixLift 4059390
  have htrace : WordTrace (prefixWord ++ tailWord_4059390) baseStart_4059390 baseEnd_4059390 := by
    simpa [prefixWord, tailWord_4059390, baseEnd_4059390] using wordTrace_append hprefix tailTrace_4059390
  have hstable : (prefixWord ++ tailWord_4059390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059390).length < 2 ^ (prefixWord ++ tailWord_4059390).sum := by decide
  have hdescent : baseEnd_4059390 < baseStart_4059390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059416 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 5, 3]
def baseStart_4059416 : Nat := 118140960795 + 4059416 * 2 ^ 59
def prefixEnd_4059416 : Nat := 4983230072969 + 3 ^ 40 * 4059416 * 2
def baseEnd_4059416 : Nat := 1389621056367996499954061

theorem tailTrace_4059416 : CollatzResearch.WordTrace tailWord_4059416 prefixEnd_4059416 1389621056367996499954061 := by
  unfold tailWord_4059416
  simp only [CollatzResearch.WordTrace]
  refine ⟨74029532530718299951015051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98706043374291066601353401 74029532530718299951015051)
  ·
    refine ⟨111044298796077449926522577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74029532530718299951015051 111044298796077449926522577)
    ·
      refine ⟨83283224097058087444891933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111044298796077449926522577 83283224097058087444891933)
      ·
        refine ⟨31231209036396782791834475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83283224097058087444891933 31231209036396782791834475)
        ·
          refine ⟨46846813554595174187751713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31231209036396782791834475 46846813554595174187751713)
          ·
            refine ⟨35135110165946380640813785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46846813554595174187751713 35135110165946380640813785)
            ·
              refine ⟨26351332624459785480610339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35135110165946380640813785 26351332624459785480610339)
              ·
                refine ⟨39526998936689678220915509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26351332624459785480610339 39526998936689678220915509)
                ·
                  refine ⟨3705656150314657333210829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39526998936689678220915509 3705656150314657333210829)
                  ·
                    refine ⟨1389621056367996499954061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3705656150314657333210829 1389621056367996499954061)
                    ·
                      rfl

theorem cell22_4059416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 5, 3].length) (baseStart_4059416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059416 prefixEnd_4059416 := by exact prefixLift 4059416
  have htrace : WordTrace (prefixWord ++ tailWord_4059416) baseStart_4059416 baseEnd_4059416 := by
    simpa [prefixWord, tailWord_4059416, baseEnd_4059416] using wordTrace_append hprefix tailTrace_4059416
  have hstable : (prefixWord ++ tailWord_4059416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059416).length < 2 ^ (prefixWord ++ tailWord_4059416).sum := by decide
  have hdescent : baseEnd_4059416 < baseStart_4059416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059450 : List Nat := [3, 1, 1, 1, 4, 3, 1, 4, 1, 3]
def baseStart_4059450 : Nat := 118140960795 + 4059450 * 2 ^ 59
def prefixEnd_4059450 : Nat := 4983230072969 + 3 ^ 40 * 4059450 * 2
def baseEnd_4059450 : Nat := 1389632695262831744603957

theorem tailTrace_4059450 : CollatzResearch.WordTrace tailWord_4059450 prefixEnd_4059450 1389632695262831744603957 := by
  unfold tailWord_4059450
  simp only [CollatzResearch.WordTrace]
  refine ⟨37015076285828355927191951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98706870095542282472511869 37015076285828355927191951)
  ·
    refine ⟨55522614428742533890787927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37015076285828355927191951 55522614428742533890787927)
    ·
      refine ⟨83283921643113800836181891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55522614428742533890787927 83283921643113800836181891)
      ·
        refine ⟨124925882464670701254272837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83283921643113800836181891 124925882464670701254272837)
        ·
          refine ⟨23423602962125756485176157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124925882464670701254272837 23423602962125756485176157)
          ·
            refine ⟨8783851110797158681941059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23423602962125756485176157 8783851110797158681941059)
            ·
              refine ⟨13175776666195738022911589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8783851110797158681941059 13175776666195738022911589)
              ·
                refine ⟨2470458124911700879295923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13175776666195738022911589 2470458124911700879295923)
                ·
                  refine ⟨3705687187367551318943885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2470458124911700879295923 3705687187367551318943885)
                  ·
                    refine ⟨1389632695262831744603957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3705687187367551318943885 1389632695262831744603957)
                    ·
                      rfl

theorem cell22_4059450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_4059450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059450 prefixEnd_4059450 := by exact prefixLift 4059450
  have htrace : WordTrace (prefixWord ++ tailWord_4059450) baseStart_4059450 baseEnd_4059450 := by
    simpa [prefixWord, tailWord_4059450, baseEnd_4059450] using wordTrace_append hprefix tailTrace_4059450
  have hstable : (prefixWord ++ tailWord_4059450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059450).length < 2 ^ (prefixWord ++ tailWord_4059450).sum := by decide
  have hdescent : baseEnd_4059450 < baseStart_4059450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059484 : List Nat := [2, 2, 4, 3, 1, 1, 2, 3, 1, 3]
def baseStart_4059484 : Nat := 118140960795 + 4059484 * 2 ^ 59
def prefixEnd_4059484 : Nat := 4983230072969 + 3 ^ 40 * 4059484 * 2
def baseEnd_4059484 : Nat := 1389644334157666989253853

theorem tailTrace_4059484 : CollatzResearch.WordTrace tailWord_4059484 prefixEnd_4059484 1389644334157666989253853 := by
  unfold tailWord_4059484
  simp only [CollatzResearch.WordTrace]
  refine ⟨74030772612595123757752753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98707696816793498343670337 74030772612595123757752753)
  ·
    refine ⟨55523079459446342818314565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74030772612595123757752753 55523079459446342818314565)
    ·
      refine ⟨10410577398646189278433981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55523079459446342818314565 10410577398646189278433981)
      ·
        refine ⟨3903966524492320979412743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10410577398646189278433981 3903966524492320979412743)
        ·
          refine ⟨5855949786738481469119115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3903966524492320979412743 5855949786738481469119115)
          ·
            refine ⟨8783924680107722203678673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5855949786738481469119115 8783924680107722203678673)
            ·
              refine ⟨6587943510080791652759005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8783924680107722203678673 6587943510080791652759005)
              ·
                refine ⟨2470478816280296869784627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6587943510080791652759005 2470478816280296869784627)
                ·
                  refine ⟨3705718224420445304676941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2470478816280296869784627 3705718224420445304676941)
                  ·
                    refine ⟨1389644334157666989253853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3705718224420445304676941 1389644334157666989253853)
                    ·
                      rfl

theorem cell22_4059484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_4059484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059484 prefixEnd_4059484 := by exact prefixLift 4059484
  have htrace : WordTrace (prefixWord ++ tailWord_4059484) baseStart_4059484 baseEnd_4059484 := by
    simpa [prefixWord, tailWord_4059484, baseEnd_4059484] using wordTrace_append hprefix tailTrace_4059484
  have hstable : (prefixWord ++ tailWord_4059484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059484).length < 2 ^ (prefixWord ++ tailWord_4059484).sum := by decide
  have hdescent : baseEnd_4059484 < baseStart_4059484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059493 : List Nat := [1, 3, 1, 3, 1, 4, 1, 3, 1, 4]
def baseStart_4059493 : Nat := 118140960795 + 4059493 * 2 ^ 59
def prefixEnd_4059493 : Nat := 4983230072969 + 3 ^ 40 * 4059493 * 2
def baseEnd_4059493 : Nat := 1389647415041593965778825

theorem tailTrace_4059493 : CollatzResearch.WordTrace tailWord_4059493 prefixEnd_4059493 1389647415041593965778825 := by
  unfold tailWord_4059493
  simp only [CollatzResearch.WordTrace]
  refine ⟨148061873482157642052583133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98707915654771761368388755 148061873482157642052583133)
  ·
    refine ⟨55523202555809115769718675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148061873482157642052583133 55523202555809115769718675)
    ·
      refine ⟨83284803833713673654578013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55523202555809115769718675 83284803833713673654578013)
      ·
        refine ⟨31231801437642627620466755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83284803833713673654578013 31231801437642627620466755)
        ·
          refine ⟨46847702156463941430700133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31231801437642627620466755 46847702156463941430700133)
          ·
            refine ⟨8783944154336989018256275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46847702156463941430700133 8783944154336989018256275)
            ·
              refine ⟨13175916231505483527384413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8783944154336989018256275 13175916231505483527384413)
              ·
                refine ⟨4940968586814556322769155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13175916231505483527384413 4940968586814556322769155)
                ·
                  refine ⟨7411452880221834484153733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4940968586814556322769155 7411452880221834484153733)
                  ·
                    refine ⟨1389647415041593965778825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7411452880221834484153733 1389647415041593965778825)
                    ·
                      rfl

theorem cell22_4059493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_4059493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059493 prefixEnd_4059493 := by exact prefixLift 4059493
  have htrace : WordTrace (prefixWord ++ tailWord_4059493) baseStart_4059493 baseEnd_4059493 := by
    simpa [prefixWord, tailWord_4059493, baseEnd_4059493] using wordTrace_append hprefix tailTrace_4059493
  have hstable : (prefixWord ++ tailWord_4059493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059493).length < 2 ^ (prefixWord ++ tailWord_4059493).sum := by decide
  have hdescent : baseEnd_4059493 < baseStart_4059493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059613 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_4059613 : Nat := 118140960795 + 4059613 * 2 ^ 59
def prefixEnd_4059613 : Nat := 4983230072969 + 3 ^ 40 * 4059613 * 2
def baseEnd_4059613 : Nat := 1389688493493953652778457

theorem tailTrace_4059613 : CollatzResearch.WordTrace tailWord_4059613 prefixEnd_4059613 1389688493493953652778457 := by
  unfold tailWord_4059613
  simp only [CollatzResearch.WordTrace]
  refine ⟨148066250241722902546951493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98710833494481935031300995 148066250241722902546951493)
  ·
    refine ⟨27762421920323044227553405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148066250241722902546951493 27762421920323044227553405)
    ·
      refine ⟨10410908220121141585332527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27762421920323044227553405 10410908220121141585332527)
      ·
        refine ⟨15616362330181712377998791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10410908220121141585332527 15616362330181712377998791)
        ·
          refine ⟨23424543495272568566998187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15616362330181712377998791 23424543495272568566998187)
          ·
            refine ⟨35136815242908852850497281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23424543495272568566998187 35136815242908852850497281)
            ·
              refine ⟨26352611432181639637872961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35136815242908852850497281 26352611432181639637872961)
              ·
                refine ⟨19764458574136229728404721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26352611432181639637872961 19764458574136229728404721)
                ·
                  refine ⟨14823343930602172296303541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19764458574136229728404721 14823343930602172296303541)
                  ·
                    refine ⟨1389688493493953652778457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14823343930602172296303541 1389688493493953652778457)
                    ·
                      rfl

theorem cell22_4059613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_4059613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059613 prefixEnd_4059613 := by exact prefixLift 4059613
  have htrace : WordTrace (prefixWord ++ tailWord_4059613) baseStart_4059613 baseEnd_4059613 := by
    simpa [prefixWord, tailWord_4059613, baseEnd_4059613] using wordTrace_append hprefix tailTrace_4059613
  have hstable : (prefixWord ++ tailWord_4059613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059613).length < 2 ^ (prefixWord ++ tailWord_4059613).sum := by decide
  have hdescent : baseEnd_4059613 < baseStart_4059613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059658 : List Nat := [3, 1, 2, 2, 2, 1, 1, 4, 1, 5]
def baseStart_4059658 : Nat := 118140960795 + 4059658 * 2 ^ 59
def prefixEnd_4059658 : Nat := 4983230072969 + 3 ^ 40 * 4059658 * 2
def baseEnd_4059658 : Nat := 1389703897913588535403319

theorem tailTrace_4059658 : CollatzResearch.WordTrace tailWord_4059658 prefixEnd_4059658 1389703897913588535403319 := by
  unfold tailWord_4059658
  simp only [CollatzResearch.WordTrace]
  refine ⟨37016972881639968808084907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98711927684373250154893085 37016972881639968808084907)
  ·
    refine ⟨55525459322459953212127361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37016972881639968808084907 55525459322459953212127361)
    ·
      refine ⟨41644094491844964909095521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55525459322459953212127361 41644094491844964909095521)
      ·
        refine ⟨31233070868883723681821641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41644094491844964909095521 31233070868883723681821641)
        ·
          refine ⟨23424803151662792761366231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31233070868883723681821641 23424803151662792761366231)
          ·
            refine ⟨35137204727494189142049347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23424803151662792761366231 35137204727494189142049347)
            ·
              refine ⟨52705807091241283713074021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35137204727494189142049347 52705807091241283713074021)
              ·
                refine ⟨9882338829607740696201379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52705807091241283713074021 9882338829607740696201379)
                ·
                  refine ⟨14823508244411611044302069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9882338829607740696201379 14823508244411611044302069)
                  ·
                    refine ⟨1389703897913588535403319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14823508244411611044302069 1389703897913588535403319)
                    ·
                      rfl

theorem cell22_4059658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_4059658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059658 prefixEnd_4059658 := by exact prefixLift 4059658
  have htrace : WordTrace (prefixWord ++ tailWord_4059658) baseStart_4059658 baseEnd_4059658 := by
    simpa [prefixWord, tailWord_4059658, baseEnd_4059658] using wordTrace_append hprefix tailTrace_4059658
  have hstable : (prefixWord ++ tailWord_4059658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059658).length < 2 ^ (prefixWord ++ tailWord_4059658).sum := by decide
  have hdescent : baseEnd_4059658 < baseStart_4059658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059660 : List Nat := [2, 2, 1, 2, 4, 1, 1, 5, 4]
def baseStart_4059660 : Nat := 118140960795 + 4059660 * 2 ^ 59
def prefixEnd_4059660 : Nat := 4983230072969 + 3 ^ 40 * 4059660 * 2
def baseEnd_4059660 : Nat := 463234860851487065617771

theorem tailTrace_4059660 : CollatzResearch.WordTrace tailWord_4059660 prefixEnd_4059660 463234860851487065617771 := by
  unfold tailWord_4059660
  simp only [CollatzResearch.WordTrace]
  refine ⟨74033982236276314786956217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98711976315035086382608289 74033982236276314786956217)
  ·
    refine ⟨55525486677207236090217163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74033982236276314786956217 55525486677207236090217163)
    ·
      refine ⟨83288230015810854135325745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55525486677207236090217163 83288230015810854135325745)
      ·
        refine ⟨62466172511858140601494309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83288230015810854135325745 62466172511858140601494309)
        ·
          refine ⟨11712407345973401362780183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62466172511858140601494309 11712407345973401362780183)
          ·
            refine ⟨17568611018960102044170275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11712407345973401362780183 17568611018960102044170275)
            ·
              refine ⟨26352916528440153066255413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17568611018960102044170275 26352916528440153066255413)
              ·
                refine ⟨2470585924541264349961445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26352916528440153066255413 2470585924541264349961445)
                ·
                  refine ⟨463234860851487065617771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2470585924541264349961445 463234860851487065617771)
                  ·
                    rfl

theorem cell22_4059660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 5, 4].length) (baseStart_4059660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059660 prefixEnd_4059660 := by exact prefixLift 4059660
  have htrace : WordTrace (prefixWord ++ tailWord_4059660) baseStart_4059660 baseEnd_4059660 := by
    simpa [prefixWord, tailWord_4059660, baseEnd_4059660] using wordTrace_append hprefix tailTrace_4059660
  have hstable : (prefixWord ++ tailWord_4059660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059660).length < 2 ^ (prefixWord ++ tailWord_4059660).sum := by decide
  have hdescent : baseEnd_4059660 < baseStart_4059660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059662 : List Nat := [4, 1, 1, 2, 3, 1, 4, 1, 1, 4]
def baseStart_4059662 : Nat := 118140960795 + 4059662 * 2 ^ 59
def prefixEnd_4059662 : Nat := 4983230072969 + 3 ^ 40 * 4059662 * 2
def baseEnd_4059662 : Nat := 1389705267195333858303307

theorem tailTrace_4059662 : CollatzResearch.WordTrace tailWord_4059662 prefixEnd_4059662 1389705267195333858303307 := by
  unfold tailWord_4059662
  simp only [CollatzResearch.WordTrace]
  refine ⟨18508504677318172989435655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98712024945696922610323493 18508504677318172989435655)
  ·
    refine ⟨27762757015977259484153483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18508504677318172989435655 27762757015977259484153483)
    ·
      refine ⟨41644135523965889226230225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27762757015977259484153483 41644135523965889226230225)
      ·
        refine ⟨31233101642974416919672669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41644135523965889226230225 31233101642974416919672669)
        ·
          refine ⟨11712413116115406344877251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31233101642974416919672669 11712413116115406344877251)
          ·
            refine ⟨17568619674173109517315877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11712413116115406344877251 17568619674173109517315877)
            ·
              refine ⟨3294116188907458034496727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17568619674173109517315877 3294116188907458034496727)
              ·
                refine ⟨4941174283361187051745091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3294116188907458034496727 4941174283361187051745091)
                ·
                  refine ⟨7411761425041780577617637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4941174283361187051745091 7411761425041780577617637)
                  ·
                    refine ⟨1389705267195333858303307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7411761425041780577617637 1389705267195333858303307)
                    ·
                      rfl

theorem cell22_4059662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 4, 1, 1, 4].length) (baseStart_4059662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059662 prefixEnd_4059662 := by exact prefixLift 4059662
  have htrace : WordTrace (prefixWord ++ tailWord_4059662) baseStart_4059662 baseEnd_4059662 := by
    simpa [prefixWord, tailWord_4059662, baseEnd_4059662] using wordTrace_append hprefix tailTrace_4059662
  have hstable : (prefixWord ++ tailWord_4059662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059662).length < 2 ^ (prefixWord ++ tailWord_4059662).sum := by decide
  have hdescent : baseEnd_4059662 < baseStart_4059662 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059733 : List Nat := [1, 3, 2, 2, 1, 1, 4, 1, 7]
def baseStart_4059733 : Nat := 118140960795 + 4059733 * 2 ^ 59
def prefixEnd_4059733 : Nat := 4983230072969 + 3 ^ 40 * 4059733 * 2
def baseEnd_4059733 : Nat := 463243190648771113259363

theorem tailTrace_4059733 : CollatzResearch.WordTrace tailWord_4059733 prefixEnd_4059733 463243190648771113259363 := by
  unfold tailWord_4059733
  simp only [CollatzResearch.WordTrace]
  refine ⟨148070627001288163041319853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98713751334192108694213235 148070627001288163041319853)
  ·
    refine ⟨55526485125483061140494945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148070627001288163041319853 55526485125483061140494945)
    ·
      refine ⟨41644863844112295855371209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55526485125483061140494945 41644863844112295855371209)
      ·
        refine ⟨31233647883084221891528407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41644863844112295855371209 31233647883084221891528407)
        ·
          refine ⟨46850471824626332837292611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31233647883084221891528407 46850471824626332837292611)
          ·
            refine ⟨70275707736939499255938917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46850471824626332837292611 70275707736939499255938917)
            ·
              refine ⟨13176695200676156110488547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70275707736939499255938917 13176695200676156110488547)
              ·
                refine ⟨19765042801014234165732821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13176695200676156110488547 19765042801014234165732821)
                ·
                  refine ⟨463243190648771113259363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19765042801014234165732821 463243190648771113259363)
                  ·
                    rfl

theorem cell22_4059733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_4059733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059733 prefixEnd_4059733 := by exact prefixLift 4059733
  have htrace : WordTrace (prefixWord ++ tailWord_4059733) baseStart_4059733 baseEnd_4059733 := by
    simpa [prefixWord, tailWord_4059733, baseEnd_4059733] using wordTrace_append hprefix tailTrace_4059733
  have hstable : (prefixWord ++ tailWord_4059733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059733).length < 2 ^ (prefixWord ++ tailWord_4059733).sum := by decide
  have hdescent : baseEnd_4059733 < baseStart_4059733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059748 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_4059748 : Nat := 118140960795 + 4059748 * 2 ^ 59
def prefixEnd_4059748 : Nat := 4983230072969 + 3 ^ 40 * 4059748 * 2
def baseEnd_4059748 : Nat := 1389734706752858300653043

theorem tailTrace_4059748 : CollatzResearch.WordTrace tailWord_4059748 prefixEnd_4059748 1389734706752858300653043 := by
  unfold tailWord_4059748
  simp only [CollatzResearch.WordTrace]
  refine ⟨74035587048116910301557949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98714116064155880402077265 74035587048116910301557949)
  ·
    refine ⟨27763345143043841363084231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74035587048116910301557949 27763345143043841363084231)
    ·
      refine ⟨41645017714565762044626347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27763345143043841363084231 41645017714565762044626347)
      ·
        refine ⟨62467526571848643066939521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41645017714565762044626347 62467526571848643066939521)
        ·
          refine ⟨46850644928886482300204641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62467526571848643066939521 46850644928886482300204641)
          ·
            refine ⟨35137983696664861725153481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46850644928886482300204641 35137983696664861725153481)
            ·
              refine ⟨26353487772498646293865111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35137983696664861725153481 26353487772498646293865111)
              ·
                refine ⟨39530231658747969440797667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26353487772498646293865111 39530231658747969440797667)
                ·
                  refine ⟨59295347488121954161196501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39530231658747969440797667 59295347488121954161196501)
                  ·
                    refine ⟨1389734706752858300653043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 59295347488121954161196501 1389734706752858300653043)
                    ·
                      rfl

theorem cell22_4059748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_4059748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059748 prefixEnd_4059748 := by exact prefixLift 4059748
  have htrace : WordTrace (prefixWord ++ tailWord_4059748) baseStart_4059748 baseEnd_4059748 := by
    simpa [prefixWord, tailWord_4059748, baseEnd_4059748] using wordTrace_append hprefix tailTrace_4059748
  have hstable : (prefixWord ++ tailWord_4059748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059748).length < 2 ^ (prefixWord ++ tailWord_4059748).sum := by decide
  have hdescent : baseEnd_4059748 < baseStart_4059748 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059795 : List Nat := [1, 1, 1, 2, 1, 2, 2, 8, 4]
def baseStart_4059795 : Nat := 118140960795 + 4059795 * 2 ^ 59
def prefixEnd_4059795 : Nat := 4983230072969 + 3 ^ 40 * 4059795 * 2
def baseEnd_4059795 : Nat := 463250265271121948242633

theorem tailTrace_4059795 : CollatzResearch.WordTrace tailWord_4059795 prefixEnd_4059795 463250265271121948242633 := by
  unfold tailWord_4059795
  simp only [CollatzResearch.WordTrace]
  refine ⟨148072888327063547630076839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98715258884709031753384559 148072888327063547630076839)
  ·
    refine ⟨222109332490595321445115259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148072888327063547630076839 222109332490595321445115259)
    ·
      refine ⟨333163998735892982167672889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222109332490595321445115259 333163998735892982167672889)
      ·
        refine ⟨249872999051919736625754667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333163998735892982167672889 249872999051919736625754667)
        ·
          refine ⟨374809498577879604938632001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249872999051919736625754667 374809498577879604938632001)
          ·
            refine ⟨281107123933409703703974001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374809498577879604938632001 281107123933409703703974001)
            ·
              refine ⟨210830342950057277777980501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281107123933409703703974001 210830342950057277777980501)
              ·
                refine ⟨2470668081445983723960709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 210830342950057277777980501 2470668081445983723960709)
                ·
                  refine ⟨463250265271121948242633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2470668081445983723960709 463250265271121948242633)
                  ·
                    rfl

theorem cell22_4059795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 8, 4].length) (baseStart_4059795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059795 prefixEnd_4059795 := by exact prefixLift 4059795
  have htrace : WordTrace (prefixWord ++ tailWord_4059795) baseStart_4059795 baseEnd_4059795 := by
    simpa [prefixWord, tailWord_4059795, baseEnd_4059795] using wordTrace_append hprefix tailTrace_4059795
  have hstable : (prefixWord ++ tailWord_4059795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059795).length < 2 ^ (prefixWord ++ tailWord_4059795).sum := by decide
  have hdescent : baseEnd_4059795 < baseStart_4059795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059829 : List Nat := [1, 3, 3, 3, 1, 2, 2, 3, 4]
def baseStart_4059829 : Nat := 118140960795 + 4059829 * 2 ^ 59
def prefixEnd_4059829 : Nat := 4983230072969 + 3 ^ 40 * 4059829 * 2
def baseEnd_4059829 : Nat := 463254144902733696459265

theorem tailTrace_4059829 : CollatzResearch.WordTrace tailWord_4059829 prefixEnd_4059829 463254144902733696459265 := by
  unfold tailWord_4059829
  simp only [CollatzResearch.WordTrace]
  refine ⟨148074128408940371436814541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98716085605960247624543027 148074128408940371436814541)
  ·
    refine ⟨55527798153352639288805453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148074128408940371436814541 55527798153352639288805453)
    ·
      refine ⟨20822924307507239733302045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55527798153352639288805453 20822924307507239733302045)
      ·
        refine ⟨7808596615315214899988267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20822924307507239733302045 7808596615315214899988267)
        ·
          refine ⟨11712894922972822349982401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7808596615315214899988267 11712894922972822349982401)
          ·
            refine ⟨8784671192229616762486801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11712894922972822349982401 8784671192229616762486801)
            ·
              refine ⟨6588503394172212571865101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8784671192229616762486801 6588503394172212571865101)
              ·
                refine ⟨2470688772814579714449413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6588503394172212571865101 2470688772814579714449413)
                ·
                  refine ⟨463254144902733696459265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2470688772814579714449413 463254144902733696459265)
                  ·
                    rfl

theorem cell22_4059829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_4059829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059829 prefixEnd_4059829 := by exact prefixLift 4059829
  have htrace : WordTrace (prefixWord ++ tailWord_4059829) baseStart_4059829 baseEnd_4059829 := by
    simpa [prefixWord, tailWord_4059829, baseEnd_4059829] using wordTrace_append hprefix tailTrace_4059829
  have hstable : (prefixWord ++ tailWord_4059829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059829).length < 2 ^ (prefixWord ++ tailWord_4059829).sum := by decide
  have hdescent : baseEnd_4059829 < baseStart_4059829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059831 : List Nat := [1, 1, 3, 1, 7, 1, 2, 1, 1, 4]
def baseStart_4059831 : Nat := 118140960795 + 4059831 * 2 ^ 59
def prefixEnd_4059831 : Nat := 4983230072969 + 3 ^ 40 * 4059831 * 2
def baseEnd_4059831 : Nat := 1389763119349073750827789

theorem tailTrace_4059831 : CollatzResearch.WordTrace tailWord_4059831 prefixEnd_4059831 1389763119349073750827789 := by
  unfold tailWord_4059831
  simp only [CollatzResearch.WordTrace]
  refine ⟨148074201354933125778387347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98716134236622083852258231 148074201354933125778387347)
  ·
    refine ⟨222111302032399688667581021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148074201354933125778387347 222111302032399688667581021)
    ·
      refine ⟨83291738262149883250342883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222111302032399688667581021 83291738262149883250342883)
      ·
        refine ⟨124937607393224824875514325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83291738262149883250342883 124937607393224824875514325)
        ·
          refine ⟨2928225173278706833019867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 124937607393224824875514325 2928225173278706833019867)
          ·
            refine ⟨4392337759918060249529801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2928225173278706833019867 4392337759918060249529801)
            ·
              refine ⟨3294253319938545187147351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4392337759918060249529801 3294253319938545187147351)
              ·
                refine ⟨4941379979907817780721027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3294253319938545187147351 4941379979907817780721027)
                ·
                  refine ⟨7412069969861726671081541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4941379979907817780721027 7412069969861726671081541)
                  ·
                    refine ⟨1389763119349073750827789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7412069969861726671081541 1389763119349073750827789)
                    ·
                      rfl

theorem cell22_4059831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 1, 4].length) (baseStart_4059831 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059831 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059831 prefixEnd_4059831 := by exact prefixLift 4059831
  have htrace : WordTrace (prefixWord ++ tailWord_4059831) baseStart_4059831 baseEnd_4059831 := by
    simpa [prefixWord, tailWord_4059831, baseEnd_4059831] using wordTrace_append hprefix tailTrace_4059831
  have hstable : (prefixWord ++ tailWord_4059831).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059831).length < 2 ^ (prefixWord ++ tailWord_4059831).sum := by decide
  have hdescent : baseEnd_4059831 < baseStart_4059831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059844 : List Nat := [2, 3, 3, 1, 1, 2, 3, 2, 2, 3]
def baseStart_4059844 : Nat := 118140960795 + 4059844 * 2 ^ 59
def prefixEnd_4059844 : Nat := 4983230072969 + 3 ^ 40 * 4059844 * 2
def baseEnd_4059844 : Nat := 1389767569514746050252749

theorem tailTrace_4059844 : CollatzResearch.WordTrace tailWord_4059844 prefixEnd_4059844 1389767569514746050252749 := by
  unfold tailWord_4059844
  simp only [CollatzResearch.WordTrace]
  refine ⟨74037337751943014499305293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98716450335924019332407057 74037337751943014499305293)
  ·
    refine ⟨27764001656978630437239485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74037337751943014499305293 27764001656978630437239485)
    ·
      refine ⟨10411500621366986413964807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27764001656978630437239485 10411500621366986413964807)
      ·
        refine ⟨15617250932050479620947211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10411500621366986413964807 15617250932050479620947211)
        ·
          refine ⟨23425876398075719431420817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15617250932050479620947211 23425876398075719431420817)
          ·
            refine ⟨17569407298556789573565613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23425876398075719431420817 17569407298556789573565613)
            ·
              refine ⟨6588527736958796090087105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17569407298556789573565613 6588527736958796090087105)
              ·
                refine ⟨4941395802719097067565329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6588527736958796090087105 4941395802719097067565329)
                ·
                  refine ⟨3706046852039322800673997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4941395802719097067565329 3706046852039322800673997)
                  ·
                    refine ⟨1389767569514746050252749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3706046852039322800673997 1389767569514746050252749)
                    ·
                      rfl

theorem cell22_4059844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_4059844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059844 prefixEnd_4059844 := by exact prefixLift 4059844
  have htrace : WordTrace (prefixWord ++ tailWord_4059844) baseStart_4059844 baseEnd_4059844 := by
    simpa [prefixWord, tailWord_4059844, baseEnd_4059844] using wordTrace_append hprefix tailTrace_4059844
  have hstable : (prefixWord ++ tailWord_4059844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059844).length < 2 ^ (prefixWord ++ tailWord_4059844).sum := by decide
  have hdescent : baseEnd_4059844 < baseStart_4059844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059846 : List Nat := [6, 1, 2, 1, 2, 1, 2, 1, 6]
def baseStart_4059846 : Nat := 118140960795 + 4059846 * 2 ^ 59
def prefixEnd_4059846 : Nat := 4983230072969 + 3 ^ 40 * 4059846 * 2
def baseEnd_4059846 : Nat := 463256084718539570567581

theorem tailTrace_4059846 : CollatzResearch.WordTrace tailWord_4059846 prefixEnd_4059846 463256084718539570567581 := by
  unfold tailWord_4059846
  simp only [CollatzResearch.WordTrace]
  refine ⟨4627335889058711979380731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 98716498966585855560122261 4627335889058711979380731)
  ·
    refine ⟨6941003833588067969071097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4627335889058711979380731 6941003833588067969071097)
    ·
      refine ⟨5205752875191050976803323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6941003833588067969071097 5205752875191050976803323)
      ·
        refine ⟨7808629312786576465204985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5205752875191050976803323 7808629312786576465204985)
        ·
          refine ⟨5856471984589932348903739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7808629312786576465204985 5856471984589932348903739)
          ·
            refine ⟨8784707976884898523355609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5856471984589932348903739 8784707976884898523355609)
            ·
              refine ⟨6588530982663673892516707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8784707976884898523355609 6588530982663673892516707)
              ·
                refine ⟨9882796473995510838775061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6588530982663673892516707 9882796473995510838775061)
                ·
                  refine ⟨463256084718539570567581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9882796473995510838775061 463256084718539570567581)
                  ·
                    rfl

theorem cell22_4059846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_4059846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059846 prefixEnd_4059846 := by exact prefixLift 4059846
  have htrace : WordTrace (prefixWord ++ tailWord_4059846) baseStart_4059846 baseEnd_4059846 := by
    simpa [prefixWord, tailWord_4059846, baseEnd_4059846] using wordTrace_append hprefix tailTrace_4059846
  have hstable : (prefixWord ++ tailWord_4059846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059846).length < 2 ^ (prefixWord ++ tailWord_4059846).sum := by decide
  have hdescent : baseEnd_4059846 < baseStart_4059846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059861 : List Nat := [1, 3, 2, 5, 2, 1, 1, 1, 1, 5]
def baseStart_4059861 : Nat := 118140960795 + 4059861 * 2 ^ 59
def prefixEnd_4059861 : Nat := 4983230072969 + 3 ^ 40 * 4059861 * 2
def baseEnd_4059861 : Nat := 1389773388962163672577697

theorem tailTrace_4059861 : CollatzResearch.WordTrace tailWord_4059861 prefixEnd_4059861 1389773388962163672577697 := by
  unfold tailWord_4059861
  simp only [CollatzResearch.WordTrace]
  refine ⟨148075295544824440901979437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98716863696549627267986291 148075295544824440901979437)
  ·
    refine ⟨55528235829309165338242289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148075295544824440901979437 55528235829309165338242289)
    ·
      refine ⟨41646176871981874003681717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55528235829309165338242289 41646176871981874003681717)
      ·
        refine ⟨3904329081748300687845161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41646176871981874003681717 3904329081748300687845161)
        ·
          refine ⟨2928246811311225515883871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3904329081748300687845161 2928246811311225515883871)
          ·
            refine ⟨4392370216966838273825807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2928246811311225515883871 4392370216966838273825807)
            ·
              refine ⟨6588555325450257410738711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4392370216966838273825807 6588555325450257410738711)
              ·
                refine ⟨9882832988175386116108067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6588555325450257410738711 9882832988175386116108067)
                ·
                  refine ⟨14824249482263079174162101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9882832988175386116108067 14824249482263079174162101)
                  ·
                    refine ⟨1389773388962163672577697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14824249482263079174162101 1389773388962163672577697)
                    ·
                      rfl

theorem cell22_4059861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_4059861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059861 prefixEnd_4059861 := by exact prefixLift 4059861
  have htrace : WordTrace (prefixWord ++ tailWord_4059861) baseStart_4059861 baseEnd_4059861 := by
    simpa [prefixWord, tailWord_4059861, baseEnd_4059861] using wordTrace_append hprefix tailTrace_4059861
  have hstable : (prefixWord ++ tailWord_4059861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059861).length < 2 ^ (prefixWord ++ tailWord_4059861).sum := by decide
  have hdescent : baseEnd_4059861 < baseStart_4059861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059885 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 9]
def baseStart_4059885 : Nat := 118140960795 + 4059885 * 2 ^ 59
def prefixEnd_4059885 : Nat := 4983230072969 + 3 ^ 40 * 4059885 * 2
def baseEnd_4059885 : Nat := 463260534884211869992541

theorem tailTrace_4059885 : CollatzResearch.WordTrace tailWord_4059885 prefixEnd_4059885 463260534884211869992541 := by
  unfold tailWord_4059885
  simp only [CollatzResearch.WordTrace]
  refine ⟨148076170896737493000853109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98717447264491662000568739 148076170896737493000853109)
  ·
    refine ⟨13882141021569139968829979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148076170896737493000853109 13882141021569139968829979)
    ·
      refine ⟨20823211532353709953244969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13882141021569139968829979 20823211532353709953244969)
      ·
        refine ⟨15617408649265282464933727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20823211532353709953244969 15617408649265282464933727)
        ·
          refine ⟨23426112973897923697400591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15617408649265282464933727 23426112973897923697400591)
          ·
            refine ⟨35139169460846885546100887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23426112973897923697400591 35139169460846885546100887)
            ·
              refine ⟨52708754191270328319151331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35139169460846885546100887 52708754191270328319151331)
              ·
                refine ⟨79063131286905492478726997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52708754191270328319151331 79063131286905492478726997)
                ·
                  refine ⟨463260534884211869992541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 79063131286905492478726997 463260534884211869992541)
                  ·
                    rfl

theorem cell22_4059885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_4059885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059885 prefixEnd_4059885 := by exact prefixLift 4059885
  have htrace : WordTrace (prefixWord ++ tailWord_4059885) baseStart_4059885 baseEnd_4059885 := by
    simpa [prefixWord, tailWord_4059885, baseEnd_4059885] using wordTrace_append hprefix tailTrace_4059885
  have hstable : (prefixWord ++ tailWord_4059885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059885).length < 2 ^ (prefixWord ++ tailWord_4059885).sum := by decide
  have hdescent : baseEnd_4059885 < baseStart_4059885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059902 : List Nat := [4, 2, 2, 1, 2, 1, 2, 1, 7]
def baseStart_4059902 : Nat := 118140960795 + 4059902 * 2 ^ 59
def prefixEnd_4059902 : Nat := 4983230072969 + 3 ^ 40 * 4059902 * 2
def baseEnd_4059902 : Nat := 463262474700017744100857

theorem tailTrace_4059902 : CollatzResearch.WordTrace tailWord_4059902 prefixEnd_4059902 463262474700017744100857 := by
  unfold tailWord_4059902
  simp only [CollatzResearch.WordTrace]
  refine ⟨18509598867209488113027745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98717860625117269936147973 18509598867209488113027745)
  ·
    refine ⟨13882199150407116084770809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18509598867209488113027745 13882199150407116084770809)
    ·
      refine ⟨10411649362805337063578107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13882199150407116084770809 10411649362805337063578107)
      ·
        refine ⟨15617474044208005595367161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10411649362805337063578107 15617474044208005595367161)
        ·
          refine ⟨11713105533156004196525371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15617474044208005595367161 11713105533156004196525371)
          ·
            refine ⟨17569658299734006294788057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11713105533156004196525371 17569658299734006294788057)
            ·
              refine ⟨13177243724800504721091043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17569658299734006294788057 13177243724800504721091043)
              ·
                refine ⟨19765865587200757081636565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13177243724800504721091043 19765865587200757081636565)
                ·
                  refine ⟨463262474700017744100857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19765865587200757081636565 463262474700017744100857)
                  ·
                    rfl

theorem cell22_4059902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_4059902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059902 prefixEnd_4059902 := by exact prefixLift 4059902
  have htrace : WordTrace (prefixWord ++ tailWord_4059902) baseStart_4059902 baseEnd_4059902 := by
    simpa [prefixWord, tailWord_4059902, baseEnd_4059902] using wordTrace_append hprefix tailTrace_4059902
  have hstable : (prefixWord ++ tailWord_4059902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059902).length < 2 ^ (prefixWord ++ tailWord_4059902).sum := by decide
  have hdescent : baseEnd_4059902 < baseStart_4059902 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059906 : List Nat := [3, 4, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_4059906 : Nat := 118140960795 + 4059906 * 2 ^ 59
def prefixEnd_4059906 : Nat := 4983230072969 + 3 ^ 40 * 4059906 * 2
def baseEnd_4059906 : Nat := 1389788793381798555202559

theorem tailTrace_4059906 : CollatzResearch.WordTrace tailWord_4059906 prefixEnd_4059906 1389788793381798555202559 := by
  unfold tailWord_4059906
  simp only [CollatzResearch.WordTrace]
  refine ⟨37019234207415353396841893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98717957886440942391578381 37019234207415353396841893)
  ·
    refine ⟨6941106413890378761907855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37019234207415353396841893 6941106413890378761907855)
    ·
      refine ⟨10411659620835568142861783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6941106413890378761907855 10411659620835568142861783)
      ·
        refine ⟨15617489431253352214292675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10411659620835568142861783 15617489431253352214292675)
        ·
          refine ⟨23426234146880028321439013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15617489431253352214292675 23426234146880028321439013)
          ·
            refine ⟨4392418902540005310269815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23426234146880028321439013 4392418902540005310269815)
            ·
              refine ⟨6588628353810007965404723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4392418902540005310269815 6588628353810007965404723)
              ·
                refine ⟨9882942530715011948107085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6588628353810007965404723 9882942530715011948107085)
                ·
                  refine ⟨3706103449018129480540157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9882942530715011948107085 3706103449018129480540157)
                  ·
                    refine ⟨1389788793381798555202559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3706103449018129480540157 1389788793381798555202559)
                    ·
                      rfl

theorem cell22_4059906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_4059906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059906 prefixEnd_4059906 := by exact prefixLift 4059906
  have htrace : WordTrace (prefixWord ++ tailWord_4059906) baseStart_4059906 baseEnd_4059906 := by
    simpa [prefixWord, tailWord_4059906, baseEnd_4059906] using wordTrace_append hprefix tailTrace_4059906
  have hstable : (prefixWord ++ tailWord_4059906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059906).length < 2 ^ (prefixWord ++ tailWord_4059906).sum := by decide
  have hdescent : baseEnd_4059906 < baseStart_4059906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059915 : List Nat := [1, 1, 1, 1, 5, 1, 1, 4, 3, 4]
def baseStart_4059915 : Nat := 118140960795 + 4059915 * 2 ^ 59
def prefixEnd_4059915 : Nat := 4983230072969 + 3 ^ 40 * 4059915 * 2
def baseEnd_4059915 : Nat := 1389791874265725531727531

theorem tailTrace_4059915 : CollatzResearch.WordTrace tailWord_4059915 prefixEnd_4059915 1389791874265725531727531 := by
  unfold tailWord_4059915
  simp only [CollatzResearch.WordTrace]
  refine ⟨148077265086628808124445199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98718176724419205416296799 148077265086628808124445199)
  ·
    refine ⟨222115897629943212186667799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148077265086628808124445199 222115897629943212186667799)
    ·
      refine ⟨333173846444914818280001699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222115897629943212186667799 333173846444914818280001699)
      ·
        refine ⟨499760769667372227420002549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333173846444914818280001699 499760769667372227420002549)
        ·
          refine ⟨46852572156316146320625239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 499760769667372227420002549 46852572156316146320625239)
          ·
            refine ⟨70278858234474219480937859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46852572156316146320625239 70278858234474219480937859)
            ·
              refine ⟨105418287351711329221406789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70278858234474219480937859 105418287351711329221406789)
              ·
                refine ⟨19765928878445874229013773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 105418287351711329221406789 19765928878445874229013773)
                ·
                  refine ⟨7412223329417202835880165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19765928878445874229013773 7412223329417202835880165)
                  ·
                    refine ⟨1389791874265725531727531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7412223329417202835880165 1389791874265725531727531)
                    ·
                      rfl

theorem cell22_4059915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 3, 4].length) (baseStart_4059915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059915 prefixEnd_4059915 := by exact prefixLift 4059915
  have htrace : WordTrace (prefixWord ++ tailWord_4059915) baseStart_4059915 baseEnd_4059915 := by
    simpa [prefixWord, tailWord_4059915, baseEnd_4059915] using wordTrace_append hprefix tailTrace_4059915
  have hstable : (prefixWord ++ tailWord_4059915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059915).length < 2 ^ (prefixWord ++ tailWord_4059915).sum := by decide
  have hdescent : baseEnd_4059915 < baseStart_4059915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059930 : List Nat := [3, 1, 1, 3, 2, 1, 2, 1, 8]
def baseStart_4059930 : Nat := 118140960795 + 4059930 * 2 ^ 59
def prefixEnd_4059930 : Nat := 4983230072969 + 3 ^ 40 * 4059930 * 2
def baseEnd_4059930 : Nat := 463265669690756830867495

theorem tailTrace_4059930 : CollatzResearch.WordTrace tailWord_4059930 prefixEnd_4059930 463265669690756830867495 := by
  unfold tailWord_4059930
  simp only [CollatzResearch.WordTrace]
  refine ⟨37019453045393616421560311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98718541454382977124160829 37019453045393616421560311)
  ·
    refine ⟨55529179568090424632340467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37019453045393616421560311 55529179568090424632340467)
    ·
      refine ⟨83293769352135636948510701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55529179568090424632340467 83293769352135636948510701)
      ·
        refine ⟨31235163507050863855691513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83293769352135636948510701 31235163507050863855691513)
        ·
          refine ⟨23426372630288147891768635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31235163507050863855691513 23426372630288147891768635)
          ·
            refine ⟨35139558945432221837652953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23426372630288147891768635 35139558945432221837652953)
            ·
              refine ⟨26354669209074166378239715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35139558945432221837652953 26354669209074166378239715)
              ·
                refine ⟨39532003813611249567359573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26354669209074166378239715 39532003813611249567359573)
                ·
                  refine ⟨463265669690756830867495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39532003813611249567359573 463265669690756830867495)
                  ·
                    rfl

theorem cell22_4059930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_4059930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059930 prefixEnd_4059930 := by exact prefixLift 4059930
  have htrace : WordTrace (prefixWord ++ tailWord_4059930) baseStart_4059930 baseEnd_4059930 := by
    simpa [prefixWord, tailWord_4059930, baseEnd_4059930] using wordTrace_append hprefix tailTrace_4059930
  have hstable : (prefixWord ++ tailWord_4059930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059930).length < 2 ^ (prefixWord ++ tailWord_4059930).sum := by decide
  have hdescent : baseEnd_4059930 < baseStart_4059930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059932 : List Nat := [2, 2, 3, 1, 1, 4, 1, 1, 3, 4]
def baseStart_4059932 : Nat := 118140960795 + 4059932 * 2 ^ 59
def prefixEnd_4059932 : Nat := 4983230072969 + 3 ^ 40 * 4059932 * 2
def baseEnd_4059932 : Nat := 1389797693713143154052479

theorem tailTrace_4059932 : CollatzResearch.WordTrace tailWord_4059932 prefixEnd_4059932 1389797693713143154052479 := by
  unfold tailWord_4059932
  simp only [CollatzResearch.WordTrace]
  refine ⟨74038942563783610013907025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98718590085044813351876033 74038942563783610013907025)
  ·
    refine ⟨55529206922837707510430269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74038942563783610013907025 55529206922837707510430269)
    ·
      refine ⟨20823452596064140316411351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55529206922837707510430269 20823452596064140316411351)
      ·
        refine ⟨31235178894096210474617027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20823452596064140316411351 31235178894096210474617027)
        ·
          refine ⟨46852768341144315711925541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31235178894096210474617027 46852768341144315711925541)
          ·
            refine ⟨8784894063964559195986039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46852768341144315711925541 8784894063964559195986039)
            ·
              refine ⟨13177341095946838793979059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8784894063964559195986039 13177341095946838793979059)
              ·
                refine ⟨19766011643920258190968589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13177341095946838793979059 19766011643920258190968589)
                ·
                  refine ⟨7412254366470096821613221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19766011643920258190968589 7412254366470096821613221)
                  ·
                    refine ⟨1389797693713143154052479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7412254366470096821613221 1389797693713143154052479)
                    ·
                      rfl

theorem cell22_4059932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_4059932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059932 prefixEnd_4059932 := by exact prefixLift 4059932
  have htrace : WordTrace (prefixWord ++ tailWord_4059932) baseStart_4059932 baseEnd_4059932 := by
    simpa [prefixWord, tailWord_4059932, baseEnd_4059932] using wordTrace_append hprefix tailTrace_4059932
  have hstable : (prefixWord ++ tailWord_4059932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059932).length < 2 ^ (prefixWord ++ tailWord_4059932).sum := by decide
  have hdescent : baseEnd_4059932 < baseStart_4059932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059945 : List Nat := [1, 2, 1, 1, 1, 1, 1, 8, 1, 5]
def baseStart_4059945 : Nat := 118140960795 + 4059945 * 2 ^ 59
def prefixEnd_4059945 : Nat := 4983230072969 + 3 ^ 40 * 4059945 * 2
def baseEnd_4059945 : Nat := 1389802143878815453477439

theorem tailTrace_4059945 : CollatzResearch.WordTrace tailWord_4059945 prefixEnd_4059945 1389802143878815453477439 := by
  unfold tailWord_4059945
  simp only [CollatzResearch.WordTrace]
  refine ⟨148078359276520123248037289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98718906184346748832024859 148078359276520123248037289)
  ·
    refine ⟨111058769457390092436027967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148078359276520123248037289 111058769457390092436027967)
    ·
      refine ⟨166588154186085138654041951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111058769457390092436027967 166588154186085138654041951)
      ·
        refine ⟨249882231279127707981062927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166588154186085138654041951 249882231279127707981062927)
        ·
          refine ⟨374823346918691561971594391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249882231279127707981062927 374823346918691561971594391)
          ·
            refine ⟨562235020378037342957391587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374823346918691561971594391 562235020378037342957391587)
            ·
              refine ⟨843352530567056014436087381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 562235020378037342957391587 843352530567056014436087381)
              ·
                refine ⟨9883037467582687669172899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 843352530567056014436087381 9883037467582687669172899)
                ·
                  refine ⟨14824556201374031503759349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9883037467582687669172899 14824556201374031503759349)
                  ·
                    refine ⟨1389802143878815453477439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14824556201374031503759349 1389802143878815453477439)
                    ·
                      rfl

theorem cell22_4059945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_4059945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059945 prefixEnd_4059945 := by exact prefixLift 4059945
  have htrace : WordTrace (prefixWord ++ tailWord_4059945) baseStart_4059945 baseEnd_4059945 := by
    simpa [prefixWord, tailWord_4059945, baseEnd_4059945] using wordTrace_append hprefix tailTrace_4059945
  have hstable : (prefixWord ++ tailWord_4059945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059945).length < 2 ^ (prefixWord ++ tailWord_4059945).sum := by decide
  have hdescent : baseEnd_4059945 < baseStart_4059945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4059994 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 2, 4]
def baseStart_4059994 : Nat := 118140960795 + 4059994 * 2 ^ 59
def prefixEnd_4059994 : Nat := 4983230072969 + 3 ^ 40 * 4059994 * 2
def baseEnd_4059994 : Nat := 1389818917580195659002289

theorem tailTrace_4059994 : CollatzResearch.WordTrace tailWord_4059994 prefixEnd_4059994 1389818917580195659002289 := by
  unfold tailWord_4059994
  simp only [CollatzResearch.WordTrace]
  refine ⟨37020036613335651154142759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98720097635561736411047357 37020036613335651154142759)
  ·
    refine ⟨55530054920003476731214139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37020036613335651154142759 55530054920003476731214139)
    ·
      refine ⟨83295082380005215096821209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55530054920003476731214139 83295082380005215096821209)
      ·
        refine ⟨62471311785003911322615907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83295082380005215096821209 62471311785003911322615907)
        ·
          refine ⟨93706967677505866983923861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62471311785003911322615907 93706967677505866983923861)
          ·
            refine ⟨4392514109883087514871431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93706967677505866983923861 4392514109883087514871431)
            ·
              refine ⟨6588771164824631272307147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4392514109883087514871431 6588771164824631272307147)
              ·
                refine ⟨9883156747236946908460721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6588771164824631272307147 9883156747236946908460721)
                ·
                  refine ⟨7412367560427710181345541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9883156747236946908460721 7412367560427710181345541)
                  ·
                    refine ⟨1389818917580195659002289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7412367560427710181345541 1389818917580195659002289)
                    ·
                      rfl

theorem cell22_4059994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_4059994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4059994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4059994 prefixEnd_4059994 := by exact prefixLift 4059994
  have htrace : WordTrace (prefixWord ++ tailWord_4059994) baseStart_4059994 baseEnd_4059994 := by
    simpa [prefixWord, tailWord_4059994, baseEnd_4059994] using wordTrace_append hprefix tailTrace_4059994
  have hstable : (prefixWord ++ tailWord_4059994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4059994).length < 2 ^ (prefixWord ++ tailWord_4059994).sum := by decide
  have hdescent : baseEnd_4059994 < baseStart_4059994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4059994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060030 : List Nat := [4, 2, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_4060030 : Nat := 118140960795 + 4060030 * 2 ^ 59
def prefixEnd_4060030 : Nat := 4983230072969 + 3 ^ 40 * 4060030 * 2
def baseEnd_4060030 : Nat := 1389831241115903565102179

theorem tailTrace_4060030 : CollatzResearch.WordTrace tailWord_4060030 prefixEnd_4060030 1389831241115903565102179 := by
  unfold tailWord_4060030
  simp only [CollatzResearch.WordTrace]
  refine ⟨18510182435151522845610193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98720972987474788509921029 18510182435151522845610193)
  ·
    refine ⟨13882636826363642134207645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18510182435151522845610193 13882636826363642134207645)
    ·
      refine ⟨5205988809886365800327867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13882636826363642134207645 5205988809886365800327867)
      ·
        refine ⟨7808983214829548700491801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5205988809886365800327867 7808983214829548700491801)
        ·
          refine ⟨5856737411122161525368851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7808983214829548700491801 5856737411122161525368851)
          ·
            refine ⟨8785106116683242288053277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5856737411122161525368851 8785106116683242288053277)
            ·
              refine ⟨3294414793756215858019979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8785106116683242288053277 3294414793756215858019979)
              ·
                refine ⟨4941622190634323787029969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3294414793756215858019979 4941622190634323787029969)
                ·
                  refine ⟨3706216642975742840272477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4941622190634323787029969 3706216642975742840272477)
                  ·
                    refine ⟨1389831241115903565102179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3706216642975742840272477 1389831241115903565102179)
                    ·
                      rfl

theorem cell22_4060030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_4060030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060030 prefixEnd_4060030 := by exact prefixLift 4060030
  have htrace : WordTrace (prefixWord ++ tailWord_4060030) baseStart_4060030 baseEnd_4060030 := by
    simpa [prefixWord, tailWord_4060030, baseEnd_4060030] using wordTrace_append hprefix tailTrace_4060030
  have hstable : (prefixWord ++ tailWord_4060030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060030).length < 2 ^ (prefixWord ++ tailWord_4060030).sum := by decide
  have hdescent : baseEnd_4060030 < baseStart_4060030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060114 : List Nat := [3, 2, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_4060114 : Nat := 118140960795 + 4060114 * 2 ^ 59
def prefixEnd_4060114 : Nat := 4983230072969 + 3 ^ 40 * 4060114 * 2
def baseEnd_4060114 : Nat := 1389859996032555346001921

theorem tailTrace_4060114 : CollatzResearch.WordTrace tailWord_4060114 prefixEnd_4060114 1389859996032555346001921 := by
  unfold tailWord_4060114
  simp only [CollatzResearch.WordTrace]
  refine ⟨37021130803226966277734849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98723015475271910073959597 37021130803226966277734849)
  ·
    refine ⟨27765848102420224708301137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37021130803226966277734849 27765848102420224708301137)
    ·
      refine ⟨20824386076815168531225853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27765848102420224708301137 20824386076815168531225853)
      ·
        refine ⟨7809144778805688199209695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20824386076815168531225853 7809144778805688199209695)
        ·
          refine ⟨11713717168208532298814543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7809144778805688199209695 11713717168208532298814543)
          ·
            refine ⟨17570575752312798448221815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11713717168208532298814543 17570575752312798448221815)
            ·
              refine ⟨26355863628469197672332723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17570575752312798448221815 26355863628469197672332723)
              ·
                refine ⟨39533795442703796508499085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26355863628469197672332723 39533795442703796508499085)
                ·
                  refine ⟨14825173291013923690687157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39533795442703796508499085 14825173291013923690687157)
                  ·
                    refine ⟨1389859996032555346001921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14825173291013923690687157 1389859996032555346001921)
                    ·
                      rfl

theorem cell22_4060114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_4060114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060114 prefixEnd_4060114 := by exact prefixLift 4060114
  have htrace : WordTrace (prefixWord ++ tailWord_4060114) baseStart_4060114 baseEnd_4060114 := by
    simpa [prefixWord, tailWord_4060114, baseEnd_4060114] using wordTrace_append hprefix tailTrace_4060114
  have hstable : (prefixWord ++ tailWord_4060114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060114).length < 2 ^ (prefixWord ++ tailWord_4060114).sum := by decide
  have hdescent : baseEnd_4060114 < baseStart_4060114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060127 : List Nat := [1, 1, 2, 3, 5, 10]
def baseStart_4060127 : Nat := 118140960795 + 4060127 * 2 ^ 59
def prefixEnd_4060127 : Nat := 4983230072969 + 3 ^ 40 * 4060127 * 2
def baseEnd_4060127 : Nat := 17158820323434909202801

theorem tailTrace_4060127 : CollatzResearch.WordTrace tailWord_4060127 prefixEnd_4060127 17158820323434909202801 := by
  unfold tailWord_4060127
  simp only [CollatzResearch.WordTrace]
  refine ⟨148084997361860768331162635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98723331574573845554108423 148084997361860768331162635)
  ·
    refine ⟨222127496042791152496743953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148084997361860768331162635 222127496042791152496743953)
    ·
      refine ⟨166595622032093364372557965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222127496042791152496743953 166595622032093364372557965)
      ·
        refine ⟨62473358262035011639709237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166595622032093364372557965 62473358262035011639709237)
        ·
          refine ⟨5856877337065782341222741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62473358262035011639709237 5856877337065782341222741)
          ·
            refine ⟨17158820323434909202801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5856877337065782341222741 17158820323434909202801)
            ·
              rfl

theorem cell22_4060127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 10].length) (baseStart_4060127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060127 prefixEnd_4060127 := by exact prefixLift 4060127
  have htrace : WordTrace (prefixWord ++ tailWord_4060127) baseStart_4060127 baseEnd_4060127 := by
    simpa [prefixWord, tailWord_4060127, baseEnd_4060127] using wordTrace_append hprefix tailTrace_4060127
  have hstable : (prefixWord ++ tailWord_4060127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060127).length < 2 ^ (prefixWord ++ tailWord_4060127).sum := by decide
  have hdescent : baseEnd_4060127 < baseStart_4060127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060131 : List Nat := [1, 1, 1, 6, 1, 1, 4, 2, 2, 3]
def baseStart_4060131 : Nat := 118140960795 + 4060131 * 2 ^ 59
def prefixEnd_4060131 : Nat := 4983230072969 + 3 ^ 40 * 4060131 * 2
def baseEnd_4060131 : Nat := 1389865815479972968326869

theorem tailTrace_4060131 : CollatzResearch.WordTrace tailWord_4060131 prefixEnd_4060131 1389865815479972968326869 := by
  unfold tailWord_4060131
  simp only [CollatzResearch.WordTrace]
  refine ⟨148085143253846277014308247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98723428835897518009538831 148085143253846277014308247)
  ·
    refine ⟨222127714880769415521462371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148085143253846277014308247 222127714880769415521462371)
    ·
      refine ⟨333191572321154123282193557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222127714880769415521462371 333191572321154123282193557)
      ·
        refine ⟨15618354952554099528852823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 333191572321154123282193557 15618354952554099528852823)
        ·
          refine ⟨23427532428831149293279235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15618354952554099528852823 23427532428831149293279235)
          ·
            refine ⟨35141298643246723939918853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23427532428831149293279235 35141298643246723939918853)
            ·
              refine ⟨6588993495608760738734785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35141298643246723939918853 6588993495608760738734785)
              ·
                refine ⟨4941745121706570554051089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6588993495608760738734785 4941745121706570554051089)
                ·
                  refine ⟨3706308841279927915538317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4941745121706570554051089 3706308841279927915538317)
                  ·
                    refine ⟨1389865815479972968326869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3706308841279927915538317 1389865815479972968326869)
                    ·
                      rfl

theorem cell22_4060131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 2, 2, 3].length) (baseStart_4060131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060131 prefixEnd_4060131 := by exact prefixLift 4060131
  have htrace : WordTrace (prefixWord ++ tailWord_4060131) baseStart_4060131 baseEnd_4060131 := by
    simpa [prefixWord, tailWord_4060131, baseEnd_4060131] using wordTrace_append hprefix tailTrace_4060131
  have hstable : (prefixWord ++ tailWord_4060131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060131).length < 2 ^ (prefixWord ++ tailWord_4060131).sum := by decide
  have hdescent : baseEnd_4060131 < baseStart_4060131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060133 : List Nat := [1, 3, 1, 6, 1, 1, 1, 4, 4]
def baseStart_4060133 : Nat := 118140960795 + 4060133 * 2 ^ 59
def prefixEnd_4060133 : Nat := 4983230072969 + 3 ^ 40 * 4060133 * 2
def baseEnd_4060133 : Nat := 463288833373615209925621

theorem tailTrace_4060133 : CollatzResearch.WordTrace tailWord_4060133 prefixEnd_4060133 463288833373615209925621 := by
  unfold tailWord_4060133
  simp only [CollatzResearch.WordTrace]
  refine ⟨148085216199839031355881053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98723477466559354237254035 148085216199839031355881053)
  ·
    refine ⟨55531956074939636758455395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148085216199839031355881053 55531956074939636758455395)
    ·
      refine ⟨83297934112409455137683093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55531956074939636758455395 83297934112409455137683093)
      ·
        refine ⟨3904590661519193209578895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 83297934112409455137683093 3904590661519193209578895)
        ·
          refine ⟨5856885992278789814368343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3904590661519193209578895 5856885992278789814368343)
          ·
            refine ⟨8785328988418184721552515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5856885992278789814368343 8785328988418184721552515)
            ·
              refine ⟨13177993482627277082328773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8785328988418184721552515 13177993482627277082328773)
              ·
                refine ⟨2470873777992614452936645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13177993482627277082328773 2470873777992614452936645)
                ·
                  refine ⟨463288833373615209925621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2470873777992614452936645 463288833373615209925621)
                  ·
                    rfl

theorem cell22_4060133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_4060133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060133 prefixEnd_4060133 := by exact prefixLift 4060133
  have htrace : WordTrace (prefixWord ++ tailWord_4060133) baseStart_4060133 baseEnd_4060133 := by
    simpa [prefixWord, tailWord_4060133, baseEnd_4060133] using wordTrace_append hprefix tailTrace_4060133
  have hstable : (prefixWord ++ tailWord_4060133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060133).length < 2 ^ (prefixWord ++ tailWord_4060133).sum := by decide
  have hdescent : baseEnd_4060133 < baseStart_4060133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060157 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_4060157 : Nat := 118140960795 + 4060157 * 2 ^ 59
def prefixEnd_4060157 : Nat := 4983230072969 + 3 ^ 40 * 4060157 * 2
def baseEnd_4060157 : Nat := 1389874715811317567176789

theorem tailTrace_4060157 : CollatzResearch.WordTrace tailWord_4060157 prefixEnd_4060157 1389874715811317567176789 := by
  unfold tailWord_4060157
  simp only [CollatzResearch.WordTrace]
  refine ⟨148086091551752083454754725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98724061034501388969836483 148086091551752083454754725)
  ·
    refine ⟨27766142165953515647766511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148086091551752083454754725 27766142165953515647766511)
    ·
      refine ⟨41649213248930273471649767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27766142165953515647766511 41649213248930273471649767)
      ·
        refine ⟨62473819873395410207474651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41649213248930273471649767 62473819873395410207474651)
        ·
          refine ⟨93710729810093115311211977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62473819873395410207474651 93710729810093115311211977)
          ·
            refine ⟨70283047357569836483408983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93710729810093115311211977 70283047357569836483408983)
            ·
              refine ⟨105424571036354754725113475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70283047357569836483408983 105424571036354754725113475)
              ·
                refine ⟨158136856554532132087670213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105424571036354754725113475 158136856554532132087670213)
                ·
                  refine ⟨29650660603974774766438165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 158136856554532132087670213 29650660603974774766438165)
                  ·
                    refine ⟨1389874715811317567176789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29650660603974774766438165 1389874715811317567176789)
                    ·
                      rfl

theorem cell22_4060157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_4060157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060157 prefixEnd_4060157 := by exact prefixLift 4060157
  have htrace : WordTrace (prefixWord ++ tailWord_4060157) baseStart_4060157 baseEnd_4060157 := by
    simpa [prefixWord, tailWord_4060157, baseEnd_4060157] using wordTrace_append hprefix tailTrace_4060157
  have hstable : (prefixWord ++ tailWord_4060157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060157).length < 2 ^ (prefixWord ++ tailWord_4060157).sum := by decide
  have hdescent : baseEnd_4060157 < baseStart_4060157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060178 : List Nat := [3, 2, 5, 1, 1, 1, 9]
def baseStart_4060178 : Nat := 118140960795 + 4060178 * 2 ^ 59
def prefixEnd_4060178 : Nat := 4983230072969 + 3 ^ 40 * 4060178 * 2
def baseEnd_4060178 : Nat := 51477107575573352311175

theorem tailTrace_4060178 : CollatzResearch.WordTrace tailWord_4060178 prefixEnd_4060178 51477107575573352311175 := by
  unfold tailWord_4060178
  simp only [CollatzResearch.WordTrace]
  refine ⟨37021714371169001010317297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98724571656450669360846125 37021714371169001010317297)
  ·
    refine ⟨27766285778376750757737973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37021714371169001010317297 27766285778376750757737973)
    ·
      refine ⟨2603089291722820383537935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 27766285778376750757737973 2603089291722820383537935)
      ·
        refine ⟨3904633937584230575306903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2603089291722820383537935 3904633937584230575306903)
        ·
          refine ⟨5856950906376345862960355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3904633937584230575306903 5856950906376345862960355)
          ·
            refine ⟨8785426359564518794440533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5856950906376345862960355 8785426359564518794440533)
            ·
              refine ⟨51477107575573352311175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8785426359564518794440533 51477107575573352311175)
              ·
                rfl

theorem cell22_4060178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 1, 9].length) (baseStart_4060178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060178 prefixEnd_4060178 := by exact prefixLift 4060178
  have htrace : WordTrace (prefixWord ++ tailWord_4060178) baseStart_4060178 baseEnd_4060178 := by
    simpa [prefixWord, tailWord_4060178, baseEnd_4060178] using wordTrace_append hprefix tailTrace_4060178
  have hstable : (prefixWord ++ tailWord_4060178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060178).length < 2 ^ (prefixWord ++ tailWord_4060178).sum := by decide
  have hdescent : baseEnd_4060178 < baseStart_4060178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060193 : List Nat := [1, 2, 3, 2, 3, 1, 2, 4, 1, 3]
def baseStart_4060193 : Nat := 118140960795 + 4060193 * 2 ^ 59
def prefixEnd_4060193 : Nat := 4983230072969 + 3 ^ 40 * 4060193 * 2
def baseEnd_4060193 : Nat := 1389887039347025473276679

theorem tailTrace_4060193 : CollatzResearch.WordTrace tailWord_4060193 prefixEnd_4060193 1389887039347025473276679 := by
  unfold tailWord_4060193
  simp only [CollatzResearch.WordTrace]
  refine ⟨148087404579621661603065233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98724936386414441068710155 148087404579621661603065233)
  ·
    refine ⟨111065553434716246202298925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148087404579621661603065233 111065553434716246202298925)
    ·
      refine ⟨41649582538018592325862097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111065553434716246202298925 41649582538018592325862097)
      ·
        refine ⟨31237186903513944244396573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41649582538018592325862097 31237186903513944244396573)
        ·
          refine ⟨11713945088817729091648715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31237186903513944244396573 11713945088817729091648715)
          ·
            refine ⟨17570917633226593637473073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11713945088817729091648715 17570917633226593637473073)
            ·
              refine ⟨13178188224919945228104805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17570917633226593637473073 13178188224919945228104805)
              ·
                refine ⟨2470910292172489730269651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13178188224919945228104805 2470910292172489730269651)
                ·
                  refine ⟨3706365438258734595404477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2470910292172489730269651 3706365438258734595404477)
                  ·
                    refine ⟨1389887039347025473276679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3706365438258734595404477 1389887039347025473276679)
                    ·
                      rfl

theorem cell22_4060193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_4060193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060193 prefixEnd_4060193 := by exact prefixLift 4060193
  have htrace : WordTrace (prefixWord ++ tailWord_4060193) baseStart_4060193 baseEnd_4060193 := by
    simpa [prefixWord, tailWord_4060193, baseEnd_4060193] using wordTrace_append hprefix tailTrace_4060193
  have hstable : (prefixWord ++ tailWord_4060193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060193).length < 2 ^ (prefixWord ++ tailWord_4060193).sum := by decide
  have hdescent : baseEnd_4060193 < baseStart_4060193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060296 : List Nat := [2, 1, 3, 4, 3, 9]
def baseStart_4060296 : Nat := 118140960795 + 4060296 * 2 ^ 59
def prefixEnd_4060296 : Nat := 4983230072969 + 3 ^ 40 * 4060296 * 2
def baseEnd_4060296 : Nat := 17159534547555154789523

theorem tailTrace_4060296 : CollatzResearch.WordTrace tailWord_4060296 prefixEnd_4060296 17159534547555154789523 := by
  unfold tailWord_4060296
  simp only [CollatzResearch.WordTrace]
  refine ⟨74045580649124255097032371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98727440865499006796043161 74045580649124255097032371)
  ·
    refine ⟨111068370973686382645548557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74045580649124255097032371 111068370973686382645548557)
    ·
      refine ⟨41650639115132393492080709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111068370973686382645548557 41650639115132393492080709)
      ·
        refine ⟨7809494834087323779765133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41650639115132393492080709 7809494834087323779765133)
        ·
          refine ⟨2928560562782746417411925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7809494834087323779765133 2928560562782746417411925)
          ·
            refine ⟨17159534547555154789523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2928560562782746417411925 17159534547555154789523)
            ·
              rfl

theorem cell22_4060296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 9].length) (baseStart_4060296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060296 prefixEnd_4060296 := by exact prefixLift 4060296
  have htrace : WordTrace (prefixWord ++ tailWord_4060296) baseStart_4060296 baseEnd_4060296 := by
    simpa [prefixWord, tailWord_4060296, baseEnd_4060296] using wordTrace_append hprefix tailTrace_4060296
  have hstable : (prefixWord ++ tailWord_4060296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060296).length < 2 ^ (prefixWord ++ tailWord_4060296).sum := by decide
  have hdescent : baseEnd_4060296 < baseStart_4060296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060345 : List Nat := [1, 2, 1, 4, 1, 4, 2, 3, 1, 3]
def baseStart_4060345 : Nat := 118140960795 + 4060345 * 2 ^ 59
def prefixEnd_4060345 : Nat := 4983230072969 + 3 ^ 40 * 4060345 * 2
def baseEnd_4060345 : Nat := 1389939072053347743476213

theorem tailTrace_4060345 : CollatzResearch.WordTrace tailWord_4060345 prefixEnd_4060345 1389939072053347743476213 := by
  unfold tailWord_4060345
  simp only [CollatzResearch.WordTrace]
  refine ⟨148092948475070991562598489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98728632316713994375065659 148092948475070991562598489)
  ·
    refine ⟨111069711356303243671948867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148092948475070991562598489 111069711356303243671948867)
    ·
      refine ⟨166604567034454865507923301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111069711356303243671948867 166604567034454865507923301)
      ·
        refine ⟨31238356318960287282735619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166604567034454865507923301 31238356318960287282735619)
        ·
          refine ⟨46857534478440430924103429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31238356318960287282735619 46857534478440430924103429)
          ·
            refine ⟨8785787714707580798269393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46857534478440430924103429 8785787714707580798269393)
            ·
              refine ⟨6589340786030685598702045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8785787714707580798269393 6589340786030685598702045)
              ·
                refine ⟨2471002794761507099513267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6589340786030685598702045 2471002794761507099513267)
                ·
                  refine ⟨3706504192142260649269901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2471002794761507099513267 3706504192142260649269901)
                  ·
                    refine ⟨1389939072053347743476213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3706504192142260649269901 1389939072053347743476213)
                    ·
                      rfl

theorem cell22_4060345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 3, 1, 3].length) (baseStart_4060345 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060345 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060345 prefixEnd_4060345 := by exact prefixLift 4060345
  have htrace : WordTrace (prefixWord ++ tailWord_4060345) baseStart_4060345 baseEnd_4060345 := by
    simpa [prefixWord, tailWord_4060345, baseEnd_4060345] using wordTrace_append hprefix tailTrace_4060345
  have hstable : (prefixWord ++ tailWord_4060345).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060345).length < 2 ^ (prefixWord ++ tailWord_4060345).sum := by decide
  have hdescent : baseEnd_4060345 < baseStart_4060345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060403 : List Nat := [1, 1, 1, 2, 2, 5, 3, 3, 4]
def baseStart_4060403 : Nat := 118140960795 + 4060403 * 2 ^ 59
def prefixEnd_4060403 : Nat := 4983230072969 + 3 ^ 40 * 4060403 * 2
def baseEnd_4060403 : Nat := 463319642212884975175345

theorem tailTrace_4060403 : CollatzResearch.WordTrace tailWord_4060403 prefixEnd_4060403 463319642212884975175345 := by
  unfold tailWord_4060403
  simp only [CollatzResearch.WordTrace]
  refine ⟨148095063908860867468209863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98730042605907244978806575 148095063908860867468209863)
  ·
    refine ⟨222142595863291301202314795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148095063908860867468209863 222142595863291301202314795)
    ·
      refine ⟨333213893794936951803472193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222142595863291301202314795 333213893794936951803472193)
      ·
        refine ⟨249910420346202713852604145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333213893794936951803472193 249910420346202713852604145)
        ·
          refine ⟨187432815259652035389453109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249910420346202713852604145 187432815259652035389453109)
          ·
            refine ⟨17571826430592378317761229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 187432815259652035389453109 17571826430592378317761229)
            ·
              refine ⟨6589434911472141869160461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17571826430592378317761229 6589434911472141869160461)
              ·
                refine ⟨2471038091802053200935173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6589434911472141869160461 2471038091802053200935173)
                ·
                  refine ⟨463319642212884975175345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2471038091802053200935173 463319642212884975175345)
                  ·
                    rfl

theorem cell22_4060403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 4].length) (baseStart_4060403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060403 prefixEnd_4060403 := by exact prefixLift 4060403
  have htrace : WordTrace (prefixWord ++ tailWord_4060403) baseStart_4060403 baseEnd_4060403 := by
    simpa [prefixWord, tailWord_4060403, baseEnd_4060403] using wordTrace_append hprefix tailTrace_4060403
  have hstable : (prefixWord ++ tailWord_4060403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060403).length < 2 ^ (prefixWord ++ tailWord_4060403).sum := by decide
  have hdescent : baseEnd_4060403 < baseStart_4060403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060450 : List Nat := [3, 3, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_4060450 : Nat := 118140960795 + 4060450 * 2 ^ 59
def prefixEnd_4060450 : Nat := 4983230072969 + 3 ^ 40 * 4060450 * 2
def baseEnd_4060450 : Nat := 1389975015699162469600891

theorem tailTrace_4060450 : CollatzResearch.WordTrace tailWord_4060450 prefixEnd_4060450 1389975015699162469600891 := by
  unfold tailWord_4060450
  simp only [CollatzResearch.WordTrace]
  refine ⟨37024194534922648623792701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98731185426460396330113869 37024194534922648623792701)
  ·
    refine ⟨13884072950595993233922263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37024194534922648623792701 13884072950595993233922263)
    ·
      refine ⟨20826109425893989850883395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13884072950595993233922263 20826109425893989850883395)
      ·
        refine ⟨31239164138840984776325093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20826109425893989850883395 31239164138840984776325093)
        ·
          refine ⟨5857343276032684645560955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31239164138840984776325093 5857343276032684645560955)
          ·
            refine ⟨8786014914049026968341433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5857343276032684645560955 8786014914049026968341433)
            ·
              refine ⟨6589511185536770226256075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8786014914049026968341433 6589511185536770226256075)
              ·
                refine ⟨9884266778305155339384113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6589511185536770226256075 9884266778305155339384113)
                ·
                  refine ⟨7413200083728866504538085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9884266778305155339384113 7413200083728866504538085)
                  ·
                    refine ⟨1389975015699162469600891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7413200083728866504538085 1389975015699162469600891)
                    ·
                      rfl

theorem cell22_4060450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_4060450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060450 prefixEnd_4060450 := by exact prefixLift 4060450
  have htrace : WordTrace (prefixWord ++ tailWord_4060450) baseStart_4060450 baseEnd_4060450 := by
    simpa [prefixWord, tailWord_4060450, baseEnd_4060450] using wordTrace_append hprefix tailTrace_4060450
  have hstable : (prefixWord ++ tailWord_4060450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060450).length < 2 ^ (prefixWord ++ tailWord_4060450).sum := by decide
  have hdescent : baseEnd_4060450 < baseStart_4060450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060480 : List Nat := [2, 1, 1, 2, 2, 1, 5, 4, 1, 3]
def baseStart_4060480 : Nat := 118140960795 + 4060480 * 2 ^ 59
def prefixEnd_4060480 : Nat := 4983230072969 + 3 ^ 40 * 4060480 * 2
def baseEnd_4060480 : Nat := 1389985285312252391350799

theorem tailTrace_4060480 : CollatzResearch.WordTrace tailWord_4060480 prefixEnd_4060480 1389985285312252391350799 := by
  unfold tailWord_4060480
  simp only [CollatzResearch.WordTrace]
  refine ⟨74048936164790954809381447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98731914886387939745841929 74048936164790954809381447)
  ·
    refine ⟨111073404247186432214072171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74048936164790954809381447 111073404247186432214072171)
    ·
      refine ⟨166610106370779648321108257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111073404247186432214072171 166610106370779648321108257)
      ·
        refine ⟨124957579778084736240831193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166610106370779648321108257 124957579778084736240831193)
        ·
          refine ⟨93718184833563552180623395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124957579778084736240831193 93718184833563552180623395)
          ·
            refine ⟨140577277250345328270935093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93718184833563552180623395 140577277250345328270935093)
            ·
              refine ⟨13179119742219874525400165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140577277250345328270935093 13179119742219874525400165)
              ·
                refine ⟨2471084951666226473512531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13179119742219874525400165 2471084951666226473512531)
                ·
                  refine ⟨3706627427499339710268797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2471084951666226473512531 3706627427499339710268797)
                  ·
                    refine ⟨1389985285312252391350799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3706627427499339710268797 1389985285312252391350799)
                    ·
                      rfl

theorem cell22_4060480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 5, 4, 1, 3].length) (baseStart_4060480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060480 prefixEnd_4060480 := by exact prefixLift 4060480
  have htrace : WordTrace (prefixWord ++ tailWord_4060480) baseStart_4060480 baseEnd_4060480 := by
    simpa [prefixWord, tailWord_4060480, baseEnd_4060480] using wordTrace_append hprefix tailTrace_4060480
  have hstable : (prefixWord ++ tailWord_4060480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060480).length < 2 ^ (prefixWord ++ tailWord_4060480).sum := by decide
  have hdescent : baseEnd_4060480 < baseStart_4060480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060589 : List Nat := [1, 5, 2, 2, 1, 2, 3, 2, 4]
def baseStart_4060589 : Nat := 118140960795 + 4060589 * 2 ^ 59
def prefixEnd_4060589 : Nat := 4983230072969 + 3 ^ 40 * 4060589 * 2
def baseEnd_4060589 : Nat := 463340866079937480125155

theorem tailTrace_4060589 : CollatzResearch.WordTrace tailWord_4060589 prefixEnd_4060589 463340866079937480125155 := by
  unfold tailWord_4060589
  simp only [CollatzResearch.WordTrace]
  refine ⟨148101847886187021234480821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98734565257458014156320547 148101847886187021234480821)
  ·
    refine ⟨13884548239330033240732577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148101847886187021234480821 13884548239330033240732577)
    ·
      refine ⟨10413411179497524930549433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13884548239330033240732577 10413411179497524930549433)
      ·
        refine ⟨7810058384623143697912075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10413411179497524930549433 7810058384623143697912075)
        ·
          refine ⟨11715087576934715546868113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7810058384623143697912075 11715087576934715546868113)
          ·
            refine ⟨8786315682701036660151085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11715087576934715546868113 8786315682701036660151085)
            ·
              refine ⟨3294868381012888747556657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8786315682701036660151085 3294868381012888747556657)
              ·
                refine ⟨2471151285759666560667493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3294868381012888747556657 2471151285759666560667493)
                ·
                  refine ⟨463340866079937480125155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2471151285759666560667493 463340866079937480125155)
                  ·
                    rfl

theorem cell22_4060589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_4060589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060589 prefixEnd_4060589 := by exact prefixLift 4060589
  have htrace : WordTrace (prefixWord ++ tailWord_4060589) baseStart_4060589 baseEnd_4060589 := by
    simpa [prefixWord, tailWord_4060589, baseEnd_4060589] using wordTrace_append hprefix tailTrace_4060589
  have hstable : (prefixWord ++ tailWord_4060589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060589).length < 2 ^ (prefixWord ++ tailWord_4060589).sum := by decide
  have hdescent : baseEnd_4060589 < baseStart_4060589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060645 : List Nat := [1, 3, 1, 5, 1, 1, 1, 4, 5]
def baseStart_4060645 : Nat := 118140960795 + 4060645 * 2 ^ 59
def prefixEnd_4060645 : Nat := 4983230072969 + 3 ^ 40 * 4060645 * 2
def baseEnd_4060645 : Nat := 463347256061415653658431

theorem tailTrace_4060645 : CollatzResearch.WordTrace tailWord_4060645 prefixEnd_4060645 463347256061415653658431 := by
  unfold tailWord_4060645
  simp only [CollatzResearch.WordTrace]
  refine ⟨148103890373984142798519389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98735926915989428532346259 148103890373984142798519389)
  ·
    refine ⟨55538958890244053549444771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148103890373984142798519389 55538958890244053549444771)
    ·
      refine ⟨83308438335366080324167157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55538958890244053549444771 83308438335366080324167157)
      ·
        refine ⟨7810166093940570030390671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83308438335366080324167157 7810166093940570030390671)
        ·
          refine ⟨11715249140910855045586007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7810166093940570030390671 11715249140910855045586007)
          ·
            refine ⟨17572873711366282568379011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11715249140910855045586007 17572873711366282568379011)
            ·
              refine ⟨26359310567049423852568517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17572873711366282568379011 26359310567049423852568517)
              ·
                refine ⟨4942370731321766972356597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26359310567049423852568517 4942370731321766972356597)
                ·
                  refine ⟨463347256061415653658431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4942370731321766972356597 463347256061415653658431)
                  ·
                    rfl

theorem cell22_4060645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_4060645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060645 prefixEnd_4060645 := by exact prefixLift 4060645
  have htrace : WordTrace (prefixWord ++ tailWord_4060645) baseStart_4060645 baseEnd_4060645 := by
    simpa [prefixWord, tailWord_4060645, baseEnd_4060645] using wordTrace_append hprefix tailTrace_4060645
  have hstable : (prefixWord ++ tailWord_4060645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060645).length < 2 ^ (prefixWord ++ tailWord_4060645).sum := by decide
  have hdescent : baseEnd_4060645 < baseStart_4060645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060735 : List Nat := [1, 1, 2, 2, 3, 3, 4, 6]
def baseStart_4060735 : Nat := 118140960795 + 4060735 * 2 ^ 59
def prefixEnd_4060735 : Nat := 4983230072969 + 3 ^ 40 * 4060735 * 2
def baseEnd_4060735 : Nat := 154452508558168525136113

theorem tailTrace_4060735 : CollatzResearch.WordTrace tailWord_4060735 prefixEnd_4060735 154452508558168525136113 := by
  unfold tailWord_4060735
  simp only [CollatzResearch.WordTrace]
  refine ⟨148107172943658088169295659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98738115295772058779530439 148107172943658088169295659)
  ·
    refine ⟨222160759415487132253943489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148107172943658088169295659 222160759415487132253943489)
    ·
      refine ⟨166620569561615349190457617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222160759415487132253943489 166620569561615349190457617)
      ·
        refine ⟨124965427171211511892843213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166620569561615349190457617 124965427171211511892843213)
        ·
          refine ⟨46862035189204316959816205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124965427171211511892843213 46862035189204316959816205)
          ·
            refine ⟨17573263195951618859931077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46862035189204316959816205 17573263195951618859931077)
            ·
              refine ⟨3294986849240928536237077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17573263195951618859931077 3294986849240928536237077)
              ·
                refine ⟨154452508558168525136113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3294986849240928536237077 154452508558168525136113)
                ·
                  rfl

theorem cell22_4060735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 6].length) (baseStart_4060735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060735 prefixEnd_4060735 := by exact prefixLift 4060735
  have htrace : WordTrace (prefixWord ++ tailWord_4060735) baseStart_4060735 baseEnd_4060735 := by
    simpa [prefixWord, tailWord_4060735, baseEnd_4060735] using wordTrace_append hprefix tailTrace_4060735
  have hstable : (prefixWord ++ tailWord_4060735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060735).length < 2 ^ (prefixWord ++ tailWord_4060735).sum := by decide
  have hdescent : baseEnd_4060735 < baseStart_4060735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060758 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_4060758 : Nat := 118140960795 + 4060758 * 2 ^ 59
def prefixEnd_4060758 : Nat := 4983230072969 + 3 ^ 40 * 4060758 * 2
def baseEnd_4060758 : Nat := 463360150131184110966649

theorem tailTrace_4060758 : CollatzResearch.WordTrace tailWord_4060758 prefixEnd_4060758 463360150131184110966649 := by
  unfold tailWord_4060758
  simp only [CollatzResearch.WordTrace]
  refine ⟨9256750738910922693586433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98738674548383175398255285 9256750738910922693586433)
  ·
    refine ⟨6942563054183192020189825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9256750738910922693586433 6942563054183192020189825)
    ·
      refine ⟨5206922290637394015142369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6942563054183192020189825 5206922290637394015142369)
      ·
        refine ⟨3905191717978045511356777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5206922290637394015142369 3905191717978045511356777)
        ·
          refine ⟨2928893788483534133517583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3905191717978045511356777 2928893788483534133517583)
          ·
            refine ⟨4393340682725301200276375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2928893788483534133517583 4393340682725301200276375)
            ·
              refine ⟨6590011024087951800414563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4393340682725301200276375 6590011024087951800414563)
              ·
                refine ⟨9885016536131927700621845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6590011024087951800414563 9885016536131927700621845)
                ·
                  refine ⟨463360150131184110966649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9885016536131927700621845 463360150131184110966649)
                  ·
                    rfl

theorem cell22_4060758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_4060758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060758 prefixEnd_4060758 := by exact prefixLift 4060758
  have htrace : WordTrace (prefixWord ++ tailWord_4060758) baseStart_4060758 baseEnd_4060758 := by
    simpa [prefixWord, tailWord_4060758, baseEnd_4060758] using wordTrace_append hprefix tailTrace_4060758
  have hstable : (prefixWord ++ tailWord_4060758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060758).length < 2 ^ (prefixWord ++ tailWord_4060758).sum := by decide
  have hdescent : baseEnd_4060758 < baseStart_4060758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060874 : List Nat := [3, 1, 2, 1, 5, 1, 1, 1, 4, 3]
def baseStart_4060874 : Nat := 118140960795 + 4060874 * 2 ^ 59
def prefixEnd_4060874 : Nat := 4983230072969 + 3 ^ 40 * 4060874 * 2
def baseEnd_4060874 : Nat := 1390120159564166696999591

theorem tailTrace_4060874 : CollatzResearch.WordTrace tailWord_4060874 prefixEnd_4060874 1390120159564166696999591 := by
  unfold tailWord_4060874
  simp only [CollatzResearch.WordTrace]
  refine ⟨37028060672538628727151419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98741495126769676605737117 37028060672538628727151419)
  ·
    refine ⟨55542091008807943090727129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37028060672538628727151419 55542091008807943090727129)
    ·
      refine ⟨41656568256605957318045347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55542091008807943090727129 41656568256605957318045347)
      ·
        refine ⟨62484852384908935977068021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41656568256605957318045347 62484852384908935977068021)
        ·
          refine ⟨5857954911085212747850127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62484852384908935977068021 5857954911085212747850127)
          ·
            refine ⟨8786932366627819121775191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5857954911085212747850127 8786932366627819121775191)
            ·
              refine ⟨13180398549941728682662787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8786932366627819121775191 13180398549941728682662787)
              ·
                refine ⟨19770597824912593023994181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13180398549941728682662787 19770597824912593023994181)
                ·
                  refine ⟨3706987092171111191998909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19770597824912593023994181 3706987092171111191998909)
                  ·
                    refine ⟨1390120159564166696999591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3706987092171111191998909 1390120159564166696999591)
                    ·
                      rfl

theorem cell22_4060874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_4060874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060874 prefixEnd_4060874 := by exact prefixLift 4060874
  have htrace : WordTrace (prefixWord ++ tailWord_4060874) baseStart_4060874 baseEnd_4060874 := by
    simpa [prefixWord, tailWord_4060874, baseEnd_4060874] using wordTrace_append hprefix tailTrace_4060874
  have hstable : (prefixWord ++ tailWord_4060874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060874).length < 2 ^ (prefixWord ++ tailWord_4060874).sum := by decide
  have hdescent : baseEnd_4060874 < baseStart_4060874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060904 : List Nat := [2, 1, 4, 1, 3, 3, 2, 6]
def baseStart_4060904 : Nat := 118140960795 + 4060904 * 2 ^ 59
def prefixEnd_4060904 : Nat := 4983230072969 + 3 ^ 40 * 4060904 * 2
def baseEnd_4060904 : Nat := 154458936575250735416611

theorem tailTrace_4060904 : CollatzResearch.WordTrace tailWord_4060904 prefixEnd_4060904 154458936575250735416611 := by
  unfold tailWord_4060904
  simp only [CollatzResearch.WordTrace]
  refine ⟨74056668440022915016098883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98742224586697220021465177 74056668440022915016098883)
  ·
    refine ⟨111085002660034372524148325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74056668440022915016098883 111085002660034372524148325)
    ·
      refine ⟨20828437998756444848277811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111085002660034372524148325 20828437998756444848277811)
      ·
        refine ⟨31242656998134667272416717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20828437998756444848277811 31242656998134667272416717)
        ·
          refine ⟨11715996374300500227156269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31242656998134667272416717 11715996374300500227156269)
          ·
            refine ⟨4393498640362687585183601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11715996374300500227156269 4393498640362687585183601)
            ·
              refine ⟨3295123980272015688887701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4393498640362687585183601 3295123980272015688887701)
              ·
                refine ⟨154458936575250735416611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3295123980272015688887701 154458936575250735416611)
                ·
                  rfl

theorem cell22_4060904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 6].length) (baseStart_4060904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060904 prefixEnd_4060904 := by exact prefixLift 4060904
  have htrace : WordTrace (prefixWord ++ tailWord_4060904) baseStart_4060904 baseEnd_4060904 := by
    simpa [prefixWord, tailWord_4060904, baseEnd_4060904] using wordTrace_append hprefix tailTrace_4060904
  have hstable : (prefixWord ++ tailWord_4060904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060904).length < 2 ^ (prefixWord ++ tailWord_4060904).sum := by decide
  have hdescent : baseEnd_4060904 < baseStart_4060904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060915 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 7]
def baseStart_4060915 : Nat := 118140960795 + 4060915 * 2 ^ 59
def prefixEnd_4060915 : Nat := 4983230072969 + 3 ^ 40 * 4060915 * 2
def baseEnd_4060915 : Nat := 463378064900685418908155

theorem tailTrace_4060915 : CollatzResearch.WordTrace tailWord_4060915 prefixEnd_4060915 463378064900685418908155 := by
  unfold tailWord_4060915
  simp only [CollatzResearch.WordTrace]
  refine ⟨148113738083005978910848199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98742492055337319273898799 148113738083005978910848199)
  ·
    refine ⟨222170607124508968366272299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148113738083005978910848199 222170607124508968366272299)
    ·
      refine ⟨333255910686763452549408449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222170607124508968366272299 333255910686763452549408449)
      ·
        refine ⟨249941933015072589412056337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333255910686763452549408449 249941933015072589412056337)
        ·
          refine ⟨187456449761304442059042253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 249941933015072589412056337 187456449761304442059042253)
          ·
            refine ⟨70296168660489165772140845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187456449761304442059042253 70296168660489165772140845)
            ·
              refine ⟨26361063247683437164552817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70296168660489165772140845 26361063247683437164552817)
              ·
                refine ⟨19770797435762577873414613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26361063247683437164552817 19770797435762577873414613)
                ·
                  refine ⟨463378064900685418908155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19770797435762577873414613 463378064900685418908155)
                  ·
                    rfl

theorem cell22_4060915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 7].length) (baseStart_4060915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060915 prefixEnd_4060915 := by exact prefixLift 4060915
  have htrace : WordTrace (prefixWord ++ tailWord_4060915) baseStart_4060915 baseEnd_4060915 := by
    simpa [prefixWord, tailWord_4060915, baseEnd_4060915] using wordTrace_append hprefix tailTrace_4060915
  have hstable : (prefixWord ++ tailWord_4060915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060915).length < 2 ^ (prefixWord ++ tailWord_4060915).sum := by decide
  have hdescent : baseEnd_4060915 < baseStart_4060915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060932 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 7]
def baseStart_4060932 : Nat := 118140960795 + 4060932 * 2 ^ 59
def prefixEnd_4060932 : Nat := 4983230072969 + 3 ^ 40 * 4060932 * 2
def baseEnd_4060932 : Nat := 463380004716491293016471

theorem tailTrace_4060932 : CollatzResearch.WordTrace tailWord_4060932 prefixEnd_4060932 463380004716491293016471 := by
  unfold tailWord_4060932
  simp only [CollatzResearch.WordTrace]
  refine ⟨74057179061972195407108525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98742905415962927209478033 74057179061972195407108525)
  ·
    refine ⟨27771442148239573277665697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74057179061972195407108525 27771442148239573277665697)
    ·
      refine ⟨20828581611179679958249273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27771442148239573277665697 20828581611179679958249273)
      ·
        refine ⟨15621436208384759968686955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20828581611179679958249273 15621436208384759968686955)
        ·
          refine ⟨23432154312577139953030433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15621436208384759968686955 23432154312577139953030433)
          ·
            refine ⟨17574115734432854964772825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23432154312577139953030433 17574115734432854964772825)
            ·
              refine ⟨13180586800824641223579619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17574115734432854964772825 13180586800824641223579619)
              ·
                refine ⟨19770880201236961835369429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13180586800824641223579619 19770880201236961835369429)
                ·
                  refine ⟨463380004716491293016471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19770880201236961835369429 463380004716491293016471)
                  ·
                    rfl

theorem cell22_4060932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 7].length) (baseStart_4060932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060932 prefixEnd_4060932 := by exact prefixLift 4060932
  have htrace : WordTrace (prefixWord ++ tailWord_4060932) baseStart_4060932 baseEnd_4060932 := by
    simpa [prefixWord, tailWord_4060932, baseEnd_4060932] using wordTrace_append hprefix tailTrace_4060932
  have hstable : (prefixWord ++ tailWord_4060932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060932).length < 2 ^ (prefixWord ++ tailWord_4060932).sum := by decide
  have hdescent : baseEnd_4060932 < baseStart_4060932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060945 : List Nat := [1, 2, 2, 1, 1, 3, 1, 1, 2, 8]
def baseStart_4060945 : Nat := 118140960795 + 4060945 * 2 ^ 59
def prefixEnd_4060945 : Nat := 4983230072969 + 3 ^ 40 * 4060945 * 2
def baseEnd_4060945 : Nat := 1390144464315146178474373

theorem tailTrace_4060945 : CollatzResearch.WordTrace tailWord_4060945 prefixEnd_4060945 1390144464315146178474373 := by
  unfold tailWord_4060945
  simp only [CollatzResearch.WordTrace]
  refine ⟨148114832272897294034440289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98743221515264862689626859 148114832272897294034440289)
  ·
    refine ⟨111086124204672970525830217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148114832272897294034440289 111086124204672970525830217)
    ·
      refine ⟨83314593153504727894372663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111086124204672970525830217 83314593153504727894372663)
      ·
        refine ⟨124971889730257091841558995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83314593153504727894372663 124971889730257091841558995)
        ·
          refine ⟨187457834595385637762338493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124971889730257091841558995 187457834595385637762338493)
          ·
            refine ⟨70296687973269614160876935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187457834595385637762338493 70296687973269614160876935)
            ·
              refine ⟨105445031959904421241315403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70296687973269614160876935 105445031959904421241315403)
              ·
                refine ⟨158167547939856631861973105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105445031959904421241315403 158167547939856631861973105)
                ·
                  refine ⟨118625660954892473896479829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 158167547939856631861973105 118625660954892473896479829)
                  ·
                    refine ⟨1390144464315146178474373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118625660954892473896479829 1390144464315146178474373)
                    ·
                      rfl

theorem cell22_4060945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_4060945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060945 prefixEnd_4060945 := by exact prefixLift 4060945
  have htrace : WordTrace (prefixWord ++ tailWord_4060945) baseStart_4060945 baseEnd_4060945 := by
    simpa [prefixWord, tailWord_4060945, baseEnd_4060945] using wordTrace_append hprefix tailTrace_4060945
  have hstable : (prefixWord ++ tailWord_4060945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060945).length < 2 ^ (prefixWord ++ tailWord_4060945).sum := by decide
  have hdescent : baseEnd_4060945 < baseStart_4060945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4060949 : List Nat := [1, 3, 2, 1, 2, 3, 4, 1, 5]
def baseStart_4060949 : Nat := 118140960795 + 4060949 * 2 ^ 59
def prefixEnd_4060949 : Nat := 4983230072969 + 3 ^ 40 * 4060949 * 2
def baseEnd_4060949 : Nat := 463381944532297167124787

theorem tailTrace_4060949 : CollatzResearch.WordTrace tailWord_4060949 prefixEnd_4060949 463381944532297167124787 := by
  unfold tailWord_4060949
  simp only [CollatzResearch.WordTrace]
  refine ⟨148114978164882802717585901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98743318776588535145057267 148114978164882802717585901)
  ·
    refine ⟨55543116811831051019094713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148114978164882802717585901 55543116811831051019094713)
    ·
      refine ⟨41657337608873288264321035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55543116811831051019094713 41657337608873288264321035)
      ·
        refine ⟨62486006413309932396481553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41657337608873288264321035 62486006413309932396481553)
        ·
          refine ⟨46864504809982449297361165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62486006413309932396481553 46864504809982449297361165)
          ·
            refine ⟨17574189303743418486510437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46864504809982449297361165 17574189303743418486510437)
            ·
              refine ⟨3295160494451890966220707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17574189303743418486510437 3295160494451890966220707)
              ·
                refine ⟨4942740741677836449331061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3295160494451890966220707 4942740741677836449331061)
                ·
                  refine ⟨463381944532297167124787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4942740741677836449331061 463381944532297167124787)
                  ·
                    rfl

theorem cell22_4060949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_4060949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4060949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4060949 prefixEnd_4060949 := by exact prefixLift 4060949
  have htrace : WordTrace (prefixWord ++ tailWord_4060949) baseStart_4060949 baseEnd_4060949 := by
    simpa [prefixWord, tailWord_4060949, baseEnd_4060949] using wordTrace_append hprefix tailTrace_4060949
  have hstable : (prefixWord ++ tailWord_4060949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4060949).length < 2 ^ (prefixWord ++ tailWord_4060949).sum := by decide
  have hdescent : baseEnd_4060949 < baseStart_4060949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4060949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061009 : List Nat := [1, 2, 2, 1, 5, 2, 2, 1, 1, 5]
def baseStart_4061009 : Nat := 118140960795 + 4061009 * 2 ^ 59
def prefixEnd_4061009 : Nat := 4983230072969 + 3 ^ 40 * 4061009 * 2
def baseEnd_4061009 : Nat := 1390166372823071344874177

theorem tailTrace_4061009 : CollatzResearch.WordTrace tailWord_4061009 prefixEnd_4061009 1390166372823071344874177 := by
  unfold tailWord_4061009
  simp only [CollatzResearch.WordTrace]
  refine ⟨148117166544665432964770081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98744777696443621976513387 148117166544665432964770081)
  ·
    refine ⟨111087874908499074723577561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148117166544665432964770081 111087874908499074723577561)
    ·
      refine ⟨83315906181374306042683171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111087874908499074723577561 83315906181374306042683171)
      ·
        refine ⟨124973859272061459064024757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83315906181374306042683171 124973859272061459064024757)
        ·
          refine ⟨11716299306755761787252321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 124973859272061459064024757 11716299306755761787252321)
          ·
            refine ⟨8787224480066821340439241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11716299306755761787252321 8787224480066821340439241)
            ·
              refine ⟨6590418360050116005329431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8787224480066821340439241 6590418360050116005329431)
              ·
                refine ⟨9885627540075174007994147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6590418360050116005329431 9885627540075174007994147)
                ·
                  refine ⟨14828441310112761011991221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9885627540075174007994147 14828441310112761011991221)
                  ·
                    refine ⟨1390166372823071344874177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14828441310112761011991221 1390166372823071344874177)
                    ·
                      rfl

theorem cell22_4061009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 5].length) (baseStart_4061009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061009 prefixEnd_4061009 := by exact prefixLift 4061009
  have htrace : WordTrace (prefixWord ++ tailWord_4061009) baseStart_4061009 baseEnd_4061009 := by
    simpa [prefixWord, tailWord_4061009, baseEnd_4061009] using wordTrace_append hprefix tailTrace_4061009
  have hstable : (prefixWord ++ tailWord_4061009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061009).length < 2 ^ (prefixWord ++ tailWord_4061009).sum := by decide
  have hdescent : baseEnd_4061009 < baseStart_4061009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061024 : List Nat := [2, 1, 1, 3, 3, 2, 3, 1, 2, 4]
def baseStart_4061024 : Nat := 118140960795 + 4061024 * 2 ^ 59
def prefixEnd_4061024 : Nat := 4983230072969 + 3 ^ 40 * 4061024 * 2
def baseEnd_4061024 : Nat := 1390171507629616305749131

theorem tailTrace_4061024 : CollatzResearch.WordTrace tailWord_4061024 prefixEnd_4061024 1390171507629616305749131 := by
  unfold tailWord_4061024
  simp only [CollatzResearch.WordTrace]
  refine ⟨74058856819805545263283063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98745142426407393684377417 74058856819805545263283063)
  ·
    refine ⟨111088285229708317894924595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74058856819805545263283063 111088285229708317894924595)
    ·
      refine ⟨166632427844562476842386893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111088285229708317894924595 166632427844562476842386893)
      ·
        refine ⟨62487160441710928815895085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166632427844562476842386893 62487160441710928815895085)
        ·
          refine ⟨23432685165641598305960657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62487160441710928815895085 23432685165641598305960657)
          ·
            refine ⟨17574513874231198729470493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23432685165641598305960657 17574513874231198729470493)
            ·
              refine ⟨6590442702836699523551435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17574513874231198729470493 6590442702836699523551435)
              ·
                refine ⟨9885664054255049285327153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6590442702836699523551435 9885664054255049285327153)
                ·
                  refine ⟨7414248040691286963995365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9885664054255049285327153 7414248040691286963995365)
                  ·
                    refine ⟨1390171507629616305749131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7414248040691286963995365 1390171507629616305749131)
                    ·
                      rfl

theorem cell22_4061024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 3, 1, 2, 4].length) (baseStart_4061024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061024 prefixEnd_4061024 := by exact prefixLift 4061024
  have htrace : WordTrace (prefixWord ++ tailWord_4061024) baseStart_4061024 baseEnd_4061024 := by
    simpa [prefixWord, tailWord_4061024, baseEnd_4061024] using wordTrace_append hprefix tailTrace_4061024
  have hstable : (prefixWord ++ tailWord_4061024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061024).length < 2 ^ (prefixWord ++ tailWord_4061024).sum := by decide
  have hdescent : baseEnd_4061024 < baseStart_4061024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061084 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 7]
def baseStart_4061084 : Nat := 118140960795 + 4061084 * 2 ^ 59
def prefixEnd_4061084 : Nat := 4983230072969 + 3 ^ 40 * 4061084 * 2
def baseEnd_4061084 : Nat := 463397348951932049749649

theorem tailTrace_4061084 : CollatzResearch.WordTrace tailWord_4061084 prefixEnd_4061084 463397348951932049749649 := by
  unfold tailWord_4061084
  simp only [CollatzResearch.WordTrace]
  refine ⟨74059951009696860386875153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98746601346262480515833537 74059951009696860386875153)
  ·
    refine ⟨55544963257272645290156365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74059951009696860386875153 55544963257272645290156365)
    ·
      refine ⟨20829361221477241983808637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55544963257272645290156365 20829361221477241983808637)
      ·
        refine ⟨7811010458053965743928239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20829361221477241983808637 7811010458053965743928239)
        ·
          refine ⟨11716515687080948615892359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7811010458053965743928239 11716515687080948615892359)
          ·
            refine ⟨17574773530621422923838539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11716515687080948615892359 17574773530621422923838539)
            ·
              refine ⟨26362160295932134385757809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17574773530621422923838539 26362160295932134385757809)
              ·
                refine ⟨19771620221949100789318357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26362160295932134385757809 19771620221949100789318357)
                ·
                  refine ⟨463397348951932049749649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19771620221949100789318357 463397348951932049749649)
                  ·
                    rfl

theorem cell22_4061084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 7].length) (baseStart_4061084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061084 prefixEnd_4061084 := by exact prefixLift 4061084
  have htrace : WordTrace (prefixWord ++ tailWord_4061084) baseStart_4061084 baseEnd_4061084 := by
    simpa [prefixWord, tailWord_4061084, baseEnd_4061084] using wordTrace_append hprefix tailTrace_4061084
  have hstable : (prefixWord ++ tailWord_4061084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061084).length < 2 ^ (prefixWord ++ tailWord_4061084).sum := by decide
  have hdescent : baseEnd_4061084 < baseStart_4061084 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061105 : List Nat := [1, 2, 2, 4, 2, 2, 3, 2, 1, 3]
def baseStart_4061105 : Nat := 118140960795 + 4061105 * 2 ^ 59
def prefixEnd_4061105 : Nat := 4983230072969 + 3 ^ 40 * 4061105 * 2
def baseEnd_4061105 : Nat := 1390199235584959094473883

theorem tailTrace_4061105 : CollatzResearch.WordTrace tailWord_4061105 prefixEnd_4061105 1390199235584959094473883 := by
  unfold tailWord_4061105
  simp only [CollatzResearch.WordTrace]
  refine ⟨148120667952317641360264769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98747111968211760906843179 148120667952317641360264769)
  ·
    refine ⟨111090500964238231020198577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148120667952317641360264769 111090500964238231020198577)
    ·
      refine ⟨83317875723178673265148933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111090500964238231020198577 83317875723178673265148933)
      ·
        refine ⟨15622101698096001237215425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83317875723178673265148933 15622101698096001237215425)
        ·
          refine ⟨11716576273572000927911569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15622101698096001237215425 11716576273572000927911569)
          ·
            refine ⟨8787432205179000695933677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11716576273572000927911569 8787432205179000695933677)
            ·
              refine ⟨3295287076942125260975129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8787432205179000695933677 3295287076942125260975129)
              ·
                refine ⟨2471465307706593945731347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3295287076942125260975129 2471465307706593945731347)
                ·
                  refine ⟨3707197961559890918597021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2471465307706593945731347 3707197961559890918597021)
                  ·
                    refine ⟨1390199235584959094473883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3707197961559890918597021 1390199235584959094473883)
                    ·
                      rfl

theorem cell22_4061105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 3, 2, 1, 3].length) (baseStart_4061105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061105 prefixEnd_4061105 := by exact prefixLift 4061105
  have htrace : WordTrace (prefixWord ++ tailWord_4061105) baseStart_4061105 baseEnd_4061105 := by
    simpa [prefixWord, tailWord_4061105, baseEnd_4061105] using wordTrace_append hprefix tailTrace_4061105
  have hstable : (prefixWord ++ tailWord_4061105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061105).length < 2 ^ (prefixWord ++ tailWord_4061105).sum := by decide
  have hdescent : baseEnd_4061105 < baseStart_4061105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061118 : List Nat := [4, 2, 1, 1, 1, 5, 2, 1, 5]
def baseStart_4061118 : Nat := 118140960795 + 4061118 * 2 ^ 59
def prefixEnd_4061118 : Nat := 4983230072969 + 3 ^ 40 * 4061118 * 2
def baseEnd_4061118 : Nat := 463401228583543797966281

theorem tailTrace_4061118 : CollatzResearch.WordTrace tailWord_4061118 prefixEnd_4061118 463401228583543797966281 := by
  unfold tailWord_4061118
  simp only [CollatzResearch.WordTrace]
  refine ⟨18515142762658818072561001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98747428067513696386992005 18515142762658818072561001)
  ·
    refine ⟨13886357071994113554420751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18515142762658818072561001 13886357071994113554420751)
    ·
      refine ⟨20829535607991170331631127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13886357071994113554420751 20829535607991170331631127)
      ·
        refine ⟨31244303411986755497446691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20829535607991170331631127 31244303411986755497446691)
        ·
          refine ⟨46866455117980133246170037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31244303411986755497446691 46866455117980133246170037)
          ·
            refine ⟨4393730167310637491828441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46866455117980133246170037 4393730167310637491828441)
            ·
              refine ⟨3295297625482978118871331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4393730167310637491828441 3295297625482978118871331)
              ·
                refine ⟨4942946438224467178306997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3295297625482978118871331 4942946438224467178306997)
                ·
                  refine ⟨463401228583543797966281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4942946438224467178306997 463401228583543797966281)
                  ·
                    rfl

theorem cell22_4061118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_4061118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061118 prefixEnd_4061118 := by exact prefixLift 4061118
  have htrace : WordTrace (prefixWord ++ tailWord_4061118) baseStart_4061118 baseEnd_4061118 := by
    simpa [prefixWord, tailWord_4061118, baseEnd_4061118] using wordTrace_append hprefix tailTrace_4061118
  have hstable : (prefixWord ++ tailWord_4061118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061118).length < 2 ^ (prefixWord ++ tailWord_4061118).sum := by decide
  have hdescent : baseEnd_4061118 < baseStart_4061118 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061144 : List Nat := [2, 1, 2, 2, 2, 2, 3, 2, 1, 5]
def baseStart_4061144 : Nat := 118140960795 + 4061144 * 2 ^ 59
def prefixEnd_4061144 : Nat := 4983230072969 + 3 ^ 40 * 4061144 * 2
def baseEnd_4061144 : Nat := 1390212586081975992748763

theorem tailTrace_4061144 : CollatzResearch.WordTrace tailWord_4061144 prefixEnd_4061144 1390212586081975992748763 := by
  unfold tailWord_4061144
  simp only [CollatzResearch.WordTrace]
  refine ⟨74061045199588175510467243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98748060266117567347289657 74061045199588175510467243)
  ·
    refine ⟨111091567799382263265700865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74061045199588175510467243 111091567799382263265700865)
    ·
      refine ⟨83318675849536697449275649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111091567799382263265700865 83318675849536697449275649)
      ·
        refine ⟨62489006887152523086956737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83318675849536697449275649 62489006887152523086956737)
        ·
          refine ⟨46866755165364392315217553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62489006887152523086956737 46866755165364392315217553)
          ·
            refine ⟨35150066374023294236413165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46866755165364392315217553 35150066374023294236413165)
            ·
              refine ⟨13181274890258735338654937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35150066374023294236413165 13181274890258735338654937)
              ·
                refine ⟨9885956167694051503991203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13181274890258735338654937 9885956167694051503991203)
                ·
                  refine ⟨14828934251541077255986805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9885956167694051503991203 14828934251541077255986805)
                  ·
                    refine ⟨1390212586081975992748763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14828934251541077255986805 1390212586081975992748763)
                    ·
                      rfl

theorem cell22_4061144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 3, 2, 1, 5].length) (baseStart_4061144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061144 prefixEnd_4061144 := by exact prefixLift 4061144
  have htrace : WordTrace (prefixWord ++ tailWord_4061144) baseStart_4061144 baseEnd_4061144 := by
    simpa [prefixWord, tailWord_4061144, baseEnd_4061144] using wordTrace_append hprefix tailTrace_4061144
  have hstable : (prefixWord ++ tailWord_4061144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061144).length < 2 ^ (prefixWord ++ tailWord_4061144).sum := by decide
  have hdescent : baseEnd_4061144 < baseStart_4061144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061157 : List Nat := [1, 3, 1, 17]
def baseStart_4061157 : Nat := 118140960795 + 4061157 * 2 ^ 59
def prefixEnd_4061157 : Nat := 4983230072969 + 3 ^ 40 * 4061157 * 2
def baseEnd_4061157 : Nat := 1907019254112000400787

theorem tailTrace_4061157 : CollatzResearch.WordTrace tailWord_4061157 prefixEnd_4061157 1907019254112000400787 := by
  unfold tailWord_4061157
  simp only [CollatzResearch.WordTrace]
  refine ⟨148122564548129254241157725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98748376365419502827438483 148122564548129254241157725)
  ·
    refine ⟨55545961705548470340434147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148122564548129254241157725 55545961705548470340434147)
    ·
      refine ⟨83318942558322705510651221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55545961705548470340434147 83318942558322705510651221)
      ·
        refine ⟨1907019254112000400787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 17 83318942558322705510651221 1907019254112000400787)
        ·
          rfl

theorem cell22_4061157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 17].length) (baseStart_4061157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061157 prefixEnd_4061157 := by exact prefixLift 4061157
  have htrace : WordTrace (prefixWord ++ tailWord_4061157) baseStart_4061157 baseEnd_4061157 := by
    simpa [prefixWord, tailWord_4061157, baseEnd_4061157] using wordTrace_append hprefix tailTrace_4061157
  have hstable : (prefixWord ++ tailWord_4061157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061157).length < 2 ^ (prefixWord ++ tailWord_4061157).sum := by decide
  have hdescent : baseEnd_4061157 < baseStart_4061157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061191 : List Nat := [1, 1, 4, 3, 1, 3, 3, 6]
def baseStart_4061191 : Nat := 118140960795 + 4061191 * 2 ^ 59
def prefixEnd_4061191 : Nat := 4983230072969 + 3 ^ 40 * 4061191 * 2
def baseEnd_4061191 : Nat := 154469852793609281869291

theorem tailTrace_4061191 : CollatzResearch.WordTrace tailWord_4061191 prefixEnd_4061191 154469852793609281869291 := by
  unfold tailWord_4061191
  simp only [CollatzResearch.WordTrace]
  refine ⟨148123804630006078047895427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98749203086670718698596951 148123804630006078047895427)
  ·
    refine ⟨222185706945009117071843141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148123804630006078047895427 222185706945009117071843141)
    ·
      refine ⟨41659820052189209450970589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222185706945009117071843141 41659820052189209450970589)
      ·
        refine ⟨15622432519570953544113971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41659820052189209450970589 15622432519570953544113971)
        ·
          refine ⟨23433648779356430316170957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15622432519570953544113971 23433648779356430316170957)
          ·
            refine ⟨8787618292258661368564109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23433648779356430316170957 8787618292258661368564109)
            ·
              refine ⟨3295356859596998013211541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8787618292258661368564109 3295356859596998013211541)
              ·
                refine ⟨154469852793609281869291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3295356859596998013211541 154469852793609281869291)
                ·
                  rfl

theorem cell22_4061191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 6].length) (baseStart_4061191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061191 prefixEnd_4061191 := by exact prefixLift 4061191
  have htrace : WordTrace (prefixWord ++ tailWord_4061191) baseStart_4061191 baseEnd_4061191 := by
    simpa [prefixWord, tailWord_4061191, baseEnd_4061191] using wordTrace_append hprefix tailTrace_4061191
  have hstable : (prefixWord ++ tailWord_4061191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061191).length < 2 ^ (prefixWord ++ tailWord_4061191).sum := by decide
  have hdescent : baseEnd_4061191 < baseStart_4061191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061219 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 7]
def baseStart_4061219 : Nat := 118140960795 + 4061219 * 2 ^ 59
def prefixEnd_4061219 : Nat := 4983230072969 + 3 ^ 40 * 4061219 * 2
def baseEnd_4061219 : Nat := 463412753371566932374511

theorem tailTrace_4061219 : CollatzResearch.WordTrace tailWord_4061219 prefixEnd_4061219 463412753371566932374511 := by
  unfold tailWord_4061219
  simp only [CollatzResearch.WordTrace]
  refine ⟨148124825873904638829914711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98749883915936425886609807 148124825873904638829914711)
  ·
    refine ⟨222187238810856958244872067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148124825873904638829914711 222187238810856958244872067)
    ·
      refine ⟨333280858216285437367308101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222187238810856958244872067 333280858216285437367308101)
      ·
        refine ⟨62490160915553519506370269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333280858216285437367308101 62490160915553519506370269)
        ·
          refine ⟨23433810343332569814888851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62490160915553519506370269 23433810343332569814888851)
          ·
            refine ⟨35150715514998854722333277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23433810343332569814888851 35150715514998854722333277)
            ·
              refine ⟨13181518318124570520874979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35150715514998854722333277 13181518318124570520874979)
              ·
                refine ⟨19772277477186855781312469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13181518318124570520874979 19772277477186855781312469)
                ·
                  refine ⟨463412753371566932374511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19772277477186855781312469 463412753371566932374511)
                  ·
                    rfl

theorem cell22_4061219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 7].length) (baseStart_4061219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061219 prefixEnd_4061219 := by exact prefixLift 4061219
  have htrace : WordTrace (prefixWord ++ tailWord_4061219) baseStart_4061219 baseEnd_4061219 := by
    simpa [prefixWord, tailWord_4061219, baseEnd_4061219] using wordTrace_append hprefix tailTrace_4061219
  have hstable : (prefixWord ++ tailWord_4061219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061219).length < 2 ^ (prefixWord ++ tailWord_4061219).sum := by decide
  have hdescent : baseEnd_4061219 < baseStart_4061219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061279 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 5, 5]
def baseStart_4061279 : Nat := 118140960795 + 4061279 * 2 ^ 59
def prefixEnd_4061279 : Nat := 4983230072969 + 3 ^ 40 * 4061279 * 2
def baseEnd_4061279 : Nat := 1390258799340880640623349

theorem tailTrace_4061279 : CollatzResearch.WordTrace tailWord_4061279 prefixEnd_4061279 1390258799340880640623349 := by
  unfold tailWord_4061279
  simp only [CollatzResearch.WordTrace]
  refine ⟨148127014253687269077098891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98751342835791512718065927 148127014253687269077098891)
  ·
    refine ⟨222190521380530903615648337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148127014253687269077098891 222190521380530903615648337)
    ·
      refine ⟨166642891035398177711736253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222190521380530903615648337 166642891035398177711736253)
      ·
        refine ⟨62491084138274316641901095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166642891035398177711736253 62491084138274316641901095)
        ·
          refine ⟨93736626207411474962851643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62491084138274316641901095 93736626207411474962851643)
          ·
            refine ⟨140604939311117212444277465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93736626207411474962851643 140604939311117212444277465)
            ·
              refine ⟨105453704483337909333208099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140604939311117212444277465 105453704483337909333208099)
              ·
                refine ⟨158180556725006863999812149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105453704483337909333208099 158180556725006863999812149)
                ·
                  refine ⟨14829427192969393499982389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158180556725006863999812149 14829427192969393499982389)
                  ·
                    refine ⟨1390258799340880640623349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14829427192969393499982389 1390258799340880640623349)
                    ·
                      rfl

theorem cell22_4061279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_4061279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061279 prefixEnd_4061279 := by exact prefixLift 4061279
  have htrace : WordTrace (prefixWord ++ tailWord_4061279) baseStart_4061279 baseEnd_4061279 := by
    simpa [prefixWord, tailWord_4061279, baseEnd_4061279] using wordTrace_append hprefix tailTrace_4061279
  have hstable : (prefixWord ++ tailWord_4061279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061279).length < 2 ^ (prefixWord ++ tailWord_4061279).sum := by decide
  have hdescent : baseEnd_4061279 < baseStart_4061279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061313 : List Nat := [1, 2, 4, 2, 3, 1, 1, 2, 1, 5]
def baseStart_4061313 : Nat := 118140960795 + 4061313 * 2 ^ 59
def prefixEnd_4061313 : Nat := 4983230072969 + 3 ^ 40 * 4061313 * 2
def baseEnd_4061313 : Nat := 1390270438235715885273245

theorem tailTrace_4061313 : CollatzResearch.WordTrace tailWord_4061313 prefixEnd_4061313 1390270438235715885273245 := by
  unfold tailWord_4061313
  simp only [CollatzResearch.WordTrace]
  refine ⟨148128254335564092883836593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98752169557042728589224395 148128254335564092883836593)
  ·
    refine ⟨111096190751673069662877445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148128254335564092883836593 111096190751673069662877445)
    ·
      refine ⟨20830535765938700561789521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111096190751673069662877445 20830535765938700561789521)
      ·
        refine ⟨15622901824454025421342141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20830535765938700561789521 15622901824454025421342141)
        ·
          refine ⟨5858588184170259533003303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15622901824454025421342141 5858588184170259533003303)
          ·
            refine ⟨8787882276255389299504955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5858588184170259533003303 8787882276255389299504955)
            ·
              refine ⟨13181823414383083949257433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8787882276255389299504955 13181823414383083949257433)
              ·
                refine ⟨9886367560787312961943075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13181823414383083949257433 9886367560787312961943075)
                ·
                  refine ⟨14829551341180969442914613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9886367560787312961943075 14829551341180969442914613)
                  ·
                    refine ⟨1390270438235715885273245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14829551341180969442914613 1390270438235715885273245)
                    ·
                      rfl

theorem cell22_4061313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_4061313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061313 prefixEnd_4061313 := by exact prefixLift 4061313
  have htrace : WordTrace (prefixWord ++ tailWord_4061313) baseStart_4061313 baseEnd_4061313 := by
    simpa [prefixWord, tailWord_4061313, baseEnd_4061313] using wordTrace_append hprefix tailTrace_4061313
  have hstable : (prefixWord ++ tailWord_4061313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061313).length < 2 ^ (prefixWord ++ tailWord_4061313).sum := by decide
  have hdescent : baseEnd_4061313 < baseStart_4061313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061326 : List Nat := [4, 1, 1, 3, 3, 10]
def baseStart_4061326 : Nat := 118140960795 + 4061326 * 2 ^ 59
def prefixEnd_4061326 : Nat := 4983230072969 + 3 ^ 40 * 4061326 * 2
def baseEnd_4061326 : Nat := 17163887511128249193805

theorem tailTrace_4061326 : CollatzResearch.WordTrace tailWord_4061326 prefixEnd_4061326 17163887511128249193805 := by
  unfold tailWord_4061326
  simp only [CollatzResearch.WordTrace]
  refine ⟨18516091060564624513007479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98752485656344664069373221 18516091060564624513007479)
  ·
    refine ⟨27774136590846936769511219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18516091060564624513007479 27774136590846936769511219)
    ·
      refine ⟨41661204886270405154266829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27774136590846936769511219 41661204886270405154266829)
      ·
        refine ⟨15622951832351401932850061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41661204886270405154266829 15622951832351401932850061)
        ·
          refine ⟨5858606937131775724818773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15622951832351401932850061 5858606937131775724818773)
          ·
            refine ⟨17163887511128249193805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5858606937131775724818773 17163887511128249193805)
            ·
              rfl

theorem cell22_4061326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 10].length) (baseStart_4061326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061326 prefixEnd_4061326 := by exact prefixLift 4061326
  have htrace : WordTrace (prefixWord ++ tailWord_4061326) baseStart_4061326 baseEnd_4061326 := by
    simpa [prefixWord, tailWord_4061326, baseEnd_4061326] using wordTrace_append hprefix tailTrace_4061326
  have hstable : (prefixWord ++ tailWord_4061326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061326).length < 2 ^ (prefixWord ++ tailWord_4061326).sum := by decide
  have hdescent : baseEnd_4061326 < baseStart_4061326 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061330 : List Nat := [3, 2, 3, 1, 1, 1, 4, 2, 2, 3]
def baseStart_4061330 : Nat := 118140960795 + 4061330 * 2 ^ 59
def prefixEnd_4061330 : Nat := 4983230072969 + 3 ^ 40 * 4061330 * 2
def baseEnd_4061330 : Nat := 1390276257683133507598193

theorem tailTrace_4061330 : CollatzResearch.WordTrace tailWord_4061330 prefixEnd_4061330 1390276257683133507598193 := by
  unfold tailWord_4061330
  simp only [CollatzResearch.WordTrace]
  refine ⟨37032218594125626196801361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98752582917668336524803629 37032218594125626196801361)
  ·
    refine ⟨27774163945594219647601021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37032218594125626196801361 27774163945594219647601021)
    ·
      refine ⟨10415311479597832367850383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27774163945594219647601021 10415311479597832367850383)
      ·
        refine ⟨15622967219396748551775575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10415311479597832367850383 15622967219396748551775575)
        ·
          refine ⟨23434450829095122827663363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15622967219396748551775575 23434450829095122827663363)
          ·
            refine ⟨35151676243642684241495045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23434450829095122827663363 35151676243642684241495045)
            ·
              refine ⟨6590939295683003295280321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35151676243642684241495045 6590939295683003295280321)
              ·
                refine ⟨4943204471762252471460241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6590939295683003295280321 4943204471762252471460241)
                ·
                  refine ⟨3707403353821689353595181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4943204471762252471460241 3707403353821689353595181)
                  ·
                    refine ⟨1390276257683133507598193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3707403353821689353595181 1390276257683133507598193)
                    ·
                      rfl

theorem cell22_4061330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_4061330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061330 prefixEnd_4061330 := by exact prefixLift 4061330
  have htrace : WordTrace (prefixWord ++ tailWord_4061330) baseStart_4061330 baseEnd_4061330 := by
    simpa [prefixWord, tailWord_4061330, baseEnd_4061330] using wordTrace_append hprefix tailTrace_4061330
  have hstable : (prefixWord ++ tailWord_4061330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061330).length < 2 ^ (prefixWord ++ tailWord_4061330).sum := by decide
  have hdescent : baseEnd_4061330 < baseStart_4061330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061332 : List Nat := [2, 4, 2, 3, 1, 1, 1, 4, 4]
def baseStart_4061332 : Nat := 118140960795 + 4061332 * 2 ^ 59
def prefixEnd_4061332 : Nat := 4983230072969 + 3 ^ 40 * 4061332 * 2
def baseEnd_4061332 : Nat := 463425647441335389682729

theorem tailTrace_4061332 : CollatzResearch.WordTrace tailWord_4061332 prefixEnd_4061332 463425647441335389682729 := by
  unfold tailWord_4061332
  simp only [CollatzResearch.WordTrace]
  refine ⟨74064473661247629564389125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98752631548330172752518833 74064473661247629564389125)
  ·
    refine ⟨13887088811483930543322961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74064473661247629564389125 13887088811483930543322961)
    ·
      refine ⟨10415316608612947907492221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13887088811483930543322961 10415316608612947907492221)
      ·
        refine ⟨3905743728229855465309583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10415316608612947907492221 3905743728229855465309583)
        ·
          refine ⟨5858615592344783197964375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3905743728229855465309583 5858615592344783197964375)
          ·
            refine ⟨8787923388517174796946563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5858615592344783197964375 8787923388517174796946563)
            ·
              refine ⟨13181885082775762195419845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8787923388517174796946563 13181885082775762195419845)
              ·
                refine ⟨2471603453020455411641221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13181885082775762195419845 2471603453020455411641221)
                ·
                  refine ⟨463425647441335389682729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2471603453020455411641221 463425647441335389682729)
                  ·
                    rfl

theorem cell22_4061332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_4061332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061332 prefixEnd_4061332 := by exact prefixLift 4061332
  have htrace : WordTrace (prefixWord ++ tailWord_4061332) baseStart_4061332 baseEnd_4061332 := by
    simpa [prefixWord, tailWord_4061332, baseEnd_4061332] using wordTrace_append hprefix tailTrace_4061332
  have hstable : (prefixWord ++ tailWord_4061332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061332).length < 2 ^ (prefixWord ++ tailWord_4061332).sum := by decide
  have hdescent : baseEnd_4061332 < baseStart_4061332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061339 : List Nat := [1, 1, 1, 1, 1, 1, 2, 5, 1, 8]
def baseStart_4061339 : Nat := 118140960795 + 4061339 * 2 ^ 59
def prefixEnd_4061339 : Nat := 4983230072969 + 3 ^ 40 * 4061339 * 2
def baseEnd_4061339 : Nat := 1390279338567060484123165

theorem tailTrace_4061339 : CollatzResearch.WordTrace tailWord_4061339 prefixEnd_4061339 1390279338567060484123165 := by
  unfold tailWord_4061339
  simp only [CollatzResearch.WordTrace]
  refine ⟨148129202633469899324283071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98752801755646599549522047 148129202633469899324283071)
  ·
    refine ⟨222193803950204848986424607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148129202633469899324283071 222193803950204848986424607)
    ·
      refine ⟨333290705925307273479636911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222193803950204848986424607 333290705925307273479636911)
      ·
        refine ⟨499936058887960910219455367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333290705925307273479636911 499936058887960910219455367)
        ·
          refine ⟨749904088331941365329183051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499936058887960910219455367 749904088331941365329183051)
          ·
            refine ⟨1124856132497912047993774577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749904088331941365329183051 1124856132497912047993774577)
            ·
              refine ⟨843642099373434035995330933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1124856132497912047993774577 843642099373434035995330933)
              ·
                refine ⟨79091446816259440874562275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 843642099373434035995330933 79091446816259440874562275)
                ·
                  refine ⟨118637170224389161311843413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79091446816259440874562275 118637170224389161311843413)
                  ·
                    refine ⟨1390279338567060484123165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118637170224389161311843413 1390279338567060484123165)
                    ·
                      rfl

theorem cell22_4061339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 8].length) (baseStart_4061339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061339 prefixEnd_4061339 := by exact prefixLift 4061339
  have htrace : WordTrace (prefixWord ++ tailWord_4061339) baseStart_4061339 baseEnd_4061339 := by
    simpa [prefixWord, tailWord_4061339, baseEnd_4061339] using wordTrace_append hprefix tailTrace_4061339
  have hstable : (prefixWord ++ tailWord_4061339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061339).length < 2 ^ (prefixWord ++ tailWord_4061339).sum := by decide
  have hdescent : baseEnd_4061339 < baseStart_4061339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061343 : List Nat := [1, 1, 2, 6, 1, 3, 1, 7]
def baseStart_4061343 : Nat := 118140960795 + 4061343 * 2 ^ 59
def prefixEnd_4061343 : Nat := 4983230072969 + 3 ^ 40 * 4061343 * 2
def baseEnd_4061343 : Nat := 154475634205422867447017

theorem tailTrace_4061343 : CollatzResearch.WordTrace tailWord_4061343 prefixEnd_4061343 154475634205422867447017 := by
  unfold tailWord_4061343
  simp only [CollatzResearch.WordTrace]
  refine ⟨148129348525455408007428683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98752899016970272004952455 148129348525455408007428683)
  ·
    refine ⟨222194022788183112011143025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148129348525455408007428683 222194022788183112011143025)
    ·
      refine ⟨166645517091137334008357269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222194022788183112011143025 166645517091137334008357269)
      ·
        refine ⟨7811508613647062531641747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 166645517091137334008357269 7811508613647062531641747)
        ·
          refine ⟨11717262920470593797462621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7811508613647062531641747 11717262920470593797462621)
          ·
            refine ⟨4393973595176472674048483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11717262920470593797462621 4393973595176472674048483)
            ·
              refine ⟨6590960392764709011072725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4393973595176472674048483 6590960392764709011072725)
              ·
                refine ⟨154475634205422867447017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6590960392764709011072725 154475634205422867447017)
                ·
                  rfl

theorem cell22_4061343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 7].length) (baseStart_4061343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061343 prefixEnd_4061343 := by exact prefixLift 4061343
  have htrace : WordTrace (prefixWord ++ tailWord_4061343) baseStart_4061343 baseEnd_4061343 := by
    simpa [prefixWord, tailWord_4061343, baseEnd_4061343] using wordTrace_append hprefix tailTrace_4061343
  have hstable : (prefixWord ++ tailWord_4061343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061343).length < 2 ^ (prefixWord ++ tailWord_4061343).sum := by decide
  have hdescent : baseEnd_4061343 < baseStart_4061343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061386 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 4, 5]
def baseStart_4061386 : Nat := 118140960795 + 4061386 * 2 ^ 59
def prefixEnd_4061386 : Nat := 4983230072969 + 3 ^ 40 * 4061386 * 2
def baseEnd_4061386 : Nat := 1390295427627568028198021

theorem tailTrace_4061386 : CollatzResearch.WordTrace tailWord_4061386 prefixEnd_4061386 1390295427627568028198021 := by
  unfold tailWord_4061386
  simp only [CollatzResearch.WordTrace]
  refine ⟨37032729216074906587811003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98753944576199750900829341 37032729216074906587811003)
  ·
    refine ⟨55549093824112359881716505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37032729216074906587811003 55549093824112359881716505)
    ·
      refine ⟨41661820368084269911287379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55549093824112359881716505 41661820368084269911287379)
      ·
        refine ⟨62492730552126404866931069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41661820368084269911287379 62492730552126404866931069)
        ·
          refine ⟨23434773957047401825099151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62492730552126404866931069 23434773957047401825099151)
          ·
            refine ⟨35152160935571102737648727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23434773957047401825099151 35152160935571102737648727)
            ·
              refine ⟨52728241403356654106473091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35152160935571102737648727 52728241403356654106473091)
              ·
                refine ⟨79092362105034981159709637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52728241403356654106473091 79092362105034981159709637)
                ·
                  refine ⟨14829817894694058967445557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 79092362105034981159709637 14829817894694058967445557)
                  ·
                    refine ⟨1390295427627568028198021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14829817894694058967445557 1390295427627568028198021)
                    ·
                      rfl

theorem cell22_4061386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_4061386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061386 prefixEnd_4061386 := by exact prefixLift 4061386
  have htrace : WordTrace (prefixWord ++ tailWord_4061386) baseStart_4061386 baseEnd_4061386 := by
    simpa [prefixWord, tailWord_4061386, baseEnd_4061386] using wordTrace_append hprefix tailTrace_4061386
  have hstable : (prefixWord ++ tailWord_4061386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061386).length < 2 ^ (prefixWord ++ tailWord_4061386).sum := by decide
  have hdescent : baseEnd_4061386 < baseStart_4061386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061401 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 5, 4]
def baseStart_4061401 : Nat := 118140960795 + 4061401 * 2 ^ 59
def prefixEnd_4061401 : Nat := 4983230072969 + 3 ^ 40 * 4061401 * 2
def baseEnd_4061401 : Nat := 1390300562434112989072975

theorem tailTrace_4061401 : CollatzResearch.WordTrace tailWord_4061401 prefixEnd_4061401 1390300562434112989072975 := by
  unfold tailWord_4061401
  simp only [CollatzResearch.WordTrace]
  refine ⟨148131463959245283913040057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98754309306163522608693371 148131463959245283913040057)
  ·
    refine ⟨111098597969433962934780043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148131463959245283913040057 111098597969433962934780043)
    ·
      refine ⟨166647896954150944402170065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111098597969433962934780043 166647896954150944402170065)
      ·
        refine ⟨124985922715613208301627549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166647896954150944402170065 124985922715613208301627549)
        ·
          refine ⟨46869721018354953113110331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124985922715613208301627549 46869721018354953113110331)
          ·
            refine ⟨70304581527532429669665497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46869721018354953113110331 70304581527532429669665497)
            ·
              refine ⟨52728436145649322252249123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70304581527532429669665497 52728436145649322252249123)
              ·
                refine ⟨79092654218473983378373685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52728436145649322252249123 79092654218473983378373685)
                ·
                  refine ⟨7414936332981935941722533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 79092654218473983378373685 7414936332981935941722533)
                  ·
                    refine ⟨1390300562434112989072975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7414936332981935941722533 1390300562434112989072975)
                    ·
                      rfl

theorem cell22_4061401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 5, 4].length) (baseStart_4061401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061401 prefixEnd_4061401 := by exact prefixLift 4061401
  have htrace : WordTrace (prefixWord ++ tailWord_4061401) baseStart_4061401 baseEnd_4061401 := by
    simpa [prefixWord, tailWord_4061401, baseEnd_4061401] using wordTrace_append hprefix tailTrace_4061401
  have hstable : (prefixWord ++ tailWord_4061401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061401).length < 2 ^ (prefixWord ++ tailWord_4061401).sum := by decide
  have hdescent : baseEnd_4061401 < baseStart_4061401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061433 : List Nat := [1, 2, 1, 3, 1, 1, 2, 7, 4]
def baseStart_4061433 : Nat := 118140960795 + 4061433 * 2 ^ 59
def prefixEnd_4061433 : Nat := 4983230072969 + 3 ^ 40 * 4061433 * 2
def baseEnd_4061433 : Nat := 463437172229358524090959

theorem tailTrace_4061433 : CollatzResearch.WordTrace tailWord_4061433 prefixEnd_4061433 463437172229358524090959 := by
  unfold tailWord_4061433
  simp only [CollatzResearch.WordTrace]
  refine ⟨148132631095129353378204953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98755087396752902252136635 148132631095129353378204953)
  ·
    refine ⟨111099473321347015033653715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148132631095129353378204953 111099473321347015033653715)
    ·
      refine ⟨166649209982020522550480573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111099473321347015033653715 166649209982020522550480573)
      ·
        refine ⟨62493453743257695956430215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166649209982020522550480573 62493453743257695956430215)
        ·
          refine ⟨93740180614886543934645323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62493453743257695956430215 93740180614886543934645323)
          ·
            refine ⟨140610270922329815901967985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93740180614886543934645323 140610270922329815901967985)
            ·
              refine ⟨105457703191747361926475989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140610270922329815901967985 105457703191747361926475989)
              ·
                refine ⟨2471664918556578795151781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 105457703191747361926475989 2471664918556578795151781)
                ·
                  refine ⟨463437172229358524090959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2471664918556578795151781 463437172229358524090959)
                  ·
                    rfl

theorem cell22_4061433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 4].length) (baseStart_4061433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061433 prefixEnd_4061433 := by exact prefixLift 4061433
  have htrace : WordTrace (prefixWord ++ tailWord_4061433) baseStart_4061433 baseEnd_4061433 := by
    simpa [prefixWord, tailWord_4061433, baseEnd_4061433] using wordTrace_append hprefix tailTrace_4061433
  have hstable : (prefixWord ++ tailWord_4061433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061433).length < 2 ^ (prefixWord ++ tailWord_4061433).sum := by decide
  have hdescent : baseEnd_4061433 < baseStart_4061433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061461 : List Nat := [1, 3, 2, 1, 2, 1, 3, 9]
def baseStart_4061461 : Nat := 118140960795 + 4061461 * 2 ^ 59
def prefixEnd_4061461 : Nat := 4983230072969 + 3 ^ 40 * 4061461 * 2
def baseEnd_4061461 : Nat := 154480122406699203619199

theorem tailTrace_4061461 : CollatzResearch.WordTrace tailWord_4061461 prefixEnd_4061461 154480122406699203619199 := by
  unfold tailWord_4061461
  simp only [CollatzResearch.WordTrace]
  refine ⟨148133652339027914160224237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98755768226018609440149491 148133652339027914160224237)
  ·
    refine ⟨55550119627135467810084089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148133652339027914160224237 55550119627135467810084089)
    ·
      refine ⟨41662589720351600857563067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55550119627135467810084089 41662589720351600857563067)
      ·
        refine ⟨62493884580527401286344601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41662589720351600857563067 62493884580527401286344601)
        ·
          refine ⟨46870413435395550964758451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62493884580527401286344601 46870413435395550964758451)
          ·
            refine ⟨70305620153093326447137677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46870413435395550964758451 70305620153093326447137677)
            ·
              refine ⟨26364607557409997417676629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70305620153093326447137677 26364607557409997417676629)
              ·
                refine ⟨154480122406699203619199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26364607557409997417676629 154480122406699203619199)
                ·
                  rfl

theorem cell22_4061461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 9].length) (baseStart_4061461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061461 prefixEnd_4061461 := by exact prefixLift 4061461
  have htrace : WordTrace (prefixWord ++ tailWord_4061461) baseStart_4061461 baseEnd_4061461 := by
    simpa [prefixWord, tailWord_4061461, baseEnd_4061461] using wordTrace_append hprefix tailTrace_4061461
  have hstable : (prefixWord ++ tailWord_4061461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061461).length < 2 ^ (prefixWord ++ tailWord_4061461).sum := by decide
  have hdescent : baseEnd_4061461 < baseStart_4061461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061469 : List Nat := [1, 4, 2, 3, 3, 1, 1, 2, 1, 4]
def baseStart_4061469 : Nat := 118140960795 + 4061469 * 2 ^ 59
def prefixEnd_4061469 : Nat := 4983230072969 + 3 ^ 40 * 4061469 * 2
def baseEnd_4061469 : Nat := 1390323840223783478372767

theorem tailTrace_4061469 : CollatzResearch.WordTrace tailWord_4061469 prefixEnd_4061469 1390323840223783478372767 := by
  unfold tailWord_4061469
  simp only [CollatzResearch.WordTrace]
  refine ⟨148133944122998931526515461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98755962748665954351010307 148133944122998931526515461)
  ·
    refine ⟨27775114523062299661221649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148133944122998931526515461 27775114523062299661221649)
    ·
      refine ⟨20831335892296724745916237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27775114523062299661221649 20831335892296724745916237)
      ·
        refine ⟨7811750959611271779718589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20831335892296724745916237 7811750959611271779718589)
        ·
          refine ⟨2929406609854226917394471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7811750959611271779718589 2929406609854226917394471)
          ·
            refine ⟨4394109914781340376091707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2929406609854226917394471 4394109914781340376091707)
            ·
              refine ⟨6591164872172010564137561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4394109914781340376091707 6591164872172010564137561)
              ·
                refine ⟨4943373654129007923103171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6591164872172010564137561 4943373654129007923103171)
                ·
                  refine ⟨7415060481193511884654757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4943373654129007923103171 7415060481193511884654757)
                  ·
                    refine ⟨1390323840223783478372767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7415060481193511884654757 1390323840223783478372767)
                    ·
                      rfl

theorem cell22_4061469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 1, 4].length) (baseStart_4061469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061469 prefixEnd_4061469 := by exact prefixLift 4061469
  have htrace : WordTrace (prefixWord ++ tailWord_4061469) baseStart_4061469 baseEnd_4061469 := by
    simpa [prefixWord, tailWord_4061469, baseEnd_4061469] using wordTrace_append hprefix tailTrace_4061469
  have hstable : (prefixWord ++ tailWord_4061469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061469).length < 2 ^ (prefixWord ++ tailWord_4061469).sum := by decide
  have hdescent : baseEnd_4061469 < baseStart_4061469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061544 : List Nat := [2, 1, 4, 2, 2, 2, 2, 3, 1, 3]
def baseStart_4061544 : Nat := 118140960795 + 4061544 * 2 ^ 59
def prefixEnd_4061544 : Nat := 4983230072969 + 3 ^ 40 * 4061544 * 2
def baseEnd_4061544 : Nat := 1390349514256508282747537

theorem tailTrace_4061544 : CollatzResearch.WordTrace tailWord_4061544 prefixEnd_4061544 1390349514256508282747537 := by
  unfold tailWord_4061544
  simp only [CollatzResearch.WordTrace]
  refine ⟨74068339798863609667747843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98757786398484812890330457 74068339798863609667747843)
  ·
    refine ⟨111102509698295414501621765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74068339798863609667747843 111102509698295414501621765)
    ·
      refine ⟨20831720568430390219054081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111102509698295414501621765 20831720568430390219054081)
      ·
        refine ⟨15623790426322792664290561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20831720568430390219054081 15623790426322792664290561)
        ·
          refine ⟨11717842819742094498217921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15623790426322792664290561 11717842819742094498217921)
          ·
            refine ⟨8788382114806570873663441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11717842819742094498217921 8788382114806570873663441)
            ·
              refine ⟨6591286586104928155247581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8788382114806570873663441 6591286586104928155247581)
              ·
                refine ⟨2471732469789348058217843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6591286586104928155247581 2471732469789348058217843)
                ·
                  refine ⟨3707598704684022087326765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2471732469789348058217843 3707598704684022087326765)
                  ·
                    refine ⟨1390349514256508282747537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3707598704684022087326765 1390349514256508282747537)
                    ·
                      rfl

theorem cell22_4061544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_4061544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061544 prefixEnd_4061544 := by exact prefixLift 4061544
  have htrace : WordTrace (prefixWord ++ tailWord_4061544) baseStart_4061544 baseEnd_4061544 := by
    simpa [prefixWord, tailWord_4061544, baseEnd_4061544] using wordTrace_append hprefix tailTrace_4061544
  have hstable : (prefixWord ++ tailWord_4061544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061544).length < 2 ^ (prefixWord ++ tailWord_4061544).sum := by decide
  have hdescent : baseEnd_4061544 < baseStart_4061544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061557 : List Nat := [1, 3, 4, 1, 2, 3, 1, 2, 5]
def baseStart_4061557 : Nat := 118140960795 + 4061557 * 2 ^ 59
def prefixEnd_4061557 : Nat := 4983230072969 + 3 ^ 40 * 4061557 * 2
def baseEnd_4061557 : Nat := 463451321474060194057499

theorem tailTrace_4061557 : CollatzResearch.WordTrace tailWord_4061557 prefixEnd_4061557 463451321474060194057499 := by
  unfold tailWord_4061557
  simp only [CollatzResearch.WordTrace]
  refine ⟨148137153746680122555718925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98758102497786748370479283 148137153746680122555718925)
  ·
    refine ⟨55551432655005045958394597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148137153746680122555718925 55551432655005045958394597)
    ·
      refine ⟨10415893622813446117198987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55551432655005045958394597 10415893622813446117198987)
      ·
        refine ⟨15623840434220169175798481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10415893622813446117198987 15623840434220169175798481)
        ·
          refine ⟨11717880325665126881848861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15623840434220169175798481 11717880325665126881848861)
          ·
            refine ⟨4394205122124422580693323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11717880325665126881848861 4394205122124422580693323)
            ·
              refine ⟨6591307683186633871039985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4394205122124422580693323 6591307683186633871039985)
              ·
                refine ⟨4943480762389975403279989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6591307683186633871039985 4943480762389975403279989)
                ·
                  refine ⟨463451321474060194057499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4943480762389975403279989 463451321474060194057499)
                  ·
                    rfl

theorem cell22_4061557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 5].length) (baseStart_4061557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061557 prefixEnd_4061557 := by exact prefixLift 4061557
  have htrace : WordTrace (prefixWord ++ tailWord_4061557) baseStart_4061557 baseEnd_4061557 := by
    simpa [prefixWord, tailWord_4061557, baseEnd_4061557] using wordTrace_append hprefix tailTrace_4061557
  have hstable : (prefixWord ++ tailWord_4061557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061557).length < 2 ^ (prefixWord ++ tailWord_4061557).sum := by decide
  have hdescent : baseEnd_4061557 < baseStart_4061557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061600 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 4, 3]
def baseStart_4061600 : Nat := 118140960795 + 4061600 * 2 ^ 59
def prefixEnd_4061600 : Nat := 4983230072969 + 3 ^ 40 * 4061600 * 2
def baseEnd_4061600 : Nat := 1390368684200942803347365

theorem tailTrace_4061600 : CollatzResearch.WordTrace tailWord_4061600 prefixEnd_4061600 1390368684200942803347365 := by
  unfold tailWord_4061600
  simp only [CollatzResearch.WordTrace]
  refine ⟨74069361042762170449767127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98759148057016227266356169 74069361042762170449767127)
  ·
    refine ⟨111104041564143255674650691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74069361042762170449767127 111104041564143255674650691)
    ·
      refine ⟨166656062346214883511976037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111104041564143255674650691 166656062346214883511976037)
      ·
        refine ⟨31248011689915290658495507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166656062346214883511976037 31248011689915290658495507)
        ·
          refine ⟨46872017534872935987743261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31248011689915290658495507 46872017534872935987743261)
          ·
            refine ⟨17577006575577350995403723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46872017534872935987743261 17577006575577350995403723)
            ·
              refine ⟨26365509863366026493105585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17577006575577350995403723 26365509863366026493105585)
              ·
                refine ⟨19774132397524519869829189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26365509863366026493105585 19774132397524519869829189)
                ·
                  refine ⟨3707649824535847475592973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19774132397524519869829189 3707649824535847475592973)
                  ·
                    refine ⟨1390368684200942803347365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3707649824535847475592973 1390368684200942803347365)
                    ·
                      rfl

theorem cell22_4061600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 4, 3].length) (baseStart_4061600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061600 prefixEnd_4061600 := by exact prefixLift 4061600
  have htrace : WordTrace (prefixWord ++ tailWord_4061600) baseStart_4061600 baseEnd_4061600 := by
    simpa [prefixWord, tailWord_4061600, baseEnd_4061600] using wordTrace_append hprefix tailTrace_4061600
  have hstable : (prefixWord ++ tailWord_4061600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061600).length < 2 ^ (prefixWord ++ tailWord_4061600).sum := by decide
  have hdescent : baseEnd_4061600 < baseStart_4061600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061675 : List Nat := [1, 1, 1, 1, 2, 3, 6, 2, 5]
def baseStart_4061675 : Nat := 118140960795 + 4061675 * 2 ^ 59
def prefixEnd_4061675 : Nat := 4983230072969 + 3 ^ 40 * 4061675 * 2
def baseEnd_4061675 : Nat := 463464786077889202574045

theorem tailTrace_4061675 : CollatzResearch.WordTrace tailWord_4061675 prefixEnd_4061675 463464786077889202574045 := by
  unfold tailWord_4061675
  simp only [CollatzResearch.WordTrace]
  refine ⟨148141457560252628708514479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98760971706835085805676319 148141457560252628708514479)
  ·
    refine ⟨222212186340378943062771719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148141457560252628708514479 222212186340378943062771719)
    ·
      refine ⟨333318279510568414594157579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222212186340378943062771719 333318279510568414594157579)
      ·
        refine ⟨499977419265852621891236369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333318279510568414594157579 499977419265852621891236369)
        ·
          refine ⟨374983064449389466418427277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 499977419265852621891236369 374983064449389466418427277)
          ·
            refine ⟨140618649168521049906910229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 374983064449389466418427277 140618649168521049906910229)
            ·
              refine ⟨6591499179774424214386417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 140618649168521049906910229 6591499179774424214386417)
              ·
                refine ⟨4943624384830818160789813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6591499179774424214386417 4943624384830818160789813)
                ·
                  refine ⟨463464786077889202574045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4943624384830818160789813 463464786077889202574045)
                  ·
                    rfl

theorem cell22_4061675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 5].length) (baseStart_4061675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061675 prefixEnd_4061675 := by exact prefixLift 4061675
  have htrace : WordTrace (prefixWord ++ tailWord_4061675) baseStart_4061675 baseEnd_4061675 := by
    simpa [prefixWord, tailWord_4061675, baseEnd_4061675] using wordTrace_append hprefix tailTrace_4061675
  have hstable : (prefixWord ++ tailWord_4061675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061675).length < 2 ^ (prefixWord ++ tailWord_4061675).sum := by decide
  have hdescent : baseEnd_4061675 < baseStart_4061675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061765 : List Nat := [1, 3, 1, 1, 1, 6, 1, 8]
def baseStart_4061765 : Nat := 118140960795 + 4061765 * 2 ^ 59
def prefixEnd_4061765 : Nat := 4983230072969 + 3 ^ 40 * 4061765 * 2
def baseEnd_4061765 : Nat := 154491685230326374774651

theorem tailTrace_4061765 : CollatzResearch.WordTrace tailWord_4061765 prefixEnd_4061765 154491685230326374774651 := by
  unfold tailWord_4061765
  simp only [CollatzResearch.WordTrace]
  refine ⟨148144740129926574079290749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98763160086617716052860499 148144740129926574079290749)
  ·
    refine ⟨55554277548722465279734031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148144740129926574079290749 55554277548722465279734031)
    ·
      refine ⟨83331416323083697919601047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55554277548722465279734031 83331416323083697919601047)
      ·
        refine ⟨124997124484625546879401571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83331416323083697919601047 124997124484625546879401571)
        ·
          refine ⟨187495686726938320319102357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124997124484625546879401571 187495686726938320319102357)
          ·
            refine ⟨8788860315325233764957923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187495686726938320319102357 8788860315325233764957923)
            ·
              refine ⟨13183290472987850647436885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8788860315325233764957923 13183290472987850647436885)
              ·
                refine ⟨154491685230326374774651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13183290472987850647436885 154491685230326374774651)
                ·
                  rfl

theorem cell22_4061765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 8].length) (baseStart_4061765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061765 prefixEnd_4061765 := by exact prefixLift 4061765
  have htrace : WordTrace (prefixWord ++ tailWord_4061765) baseStart_4061765 baseEnd_4061765 := by
    simpa [prefixWord, tailWord_4061765, baseEnd_4061765] using wordTrace_append hprefix tailTrace_4061765
  have hstable : (prefixWord ++ tailWord_4061765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061765).length < 2 ^ (prefixWord ++ tailWord_4061765).sum := by decide
  have hdescent : baseEnd_4061765 < baseStart_4061765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061795 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 2, 6]
def baseStart_4061795 : Nat := 118140960795 + 4061795 * 2 ^ 59
def prefixEnd_4061795 : Nat := 4983230072969 + 3 ^ 40 * 4061795 * 2
def baseEnd_4061795 : Nat := 1390435436686027294721767

theorem tailTrace_4061795 : CollatzResearch.WordTrace tailWord_4061795 prefixEnd_4061795 1390435436686027294721767 := by
  unfold tailWord_4061795
  simp only [CollatzResearch.WordTrace]
  refine ⟨148145834319817889202882839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98763889546545259468588559 148145834319817889202882839)
  ·
    refine ⟨222218751479726833804324259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148145834319817889202882839 222218751479726833804324259)
    ·
      refine ⟨333328127219590250706486389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222218751479726833804324259 333328127219590250706486389)
      ·
        refine ⟨31249511926836586003733099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 333328127219590250706486389 31249511926836586003733099)
        ·
          refine ⟨46874267890254879005599649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31249511926836586003733099 46874267890254879005599649)
          ·
            refine ⟨35155700917691159254199737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46874267890254879005599649 35155700917691159254199737)
            ·
              refine ⟨26366775688268369440649803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35155700917691159254199737 26366775688268369440649803)
              ·
                refine ⟨39550163532402554160974705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26366775688268369440649803 39550163532402554160974705)
                ·
                  refine ⟨29662622649301915620731029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39550163532402554160974705 29662622649301915620731029)
                  ·
                    refine ⟨1390435436686027294721767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29662622649301915620731029 1390435436686027294721767)
                    ·
                      rfl

theorem cell22_4061795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 2, 6].length) (baseStart_4061795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061795 prefixEnd_4061795 := by exact prefixLift 4061795
  have htrace : WordTrace (prefixWord ++ tailWord_4061795) baseStart_4061795 baseEnd_4061795 := by
    simpa [prefixWord, tailWord_4061795, baseEnd_4061795] using wordTrace_append hprefix tailTrace_4061795
  have hstable : (prefixWord ++ tailWord_4061795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061795).length < 2 ^ (prefixWord ++ tailWord_4061795).sum := by decide
  have hdescent : baseEnd_4061795 < baseStart_4061795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061844 : List Nat := [2, 4, 2, 2, 1, 1, 1, 4, 5]
def baseStart_4061844 : Nat := 118140960795 + 4061844 * 2 ^ 59
def prefixEnd_4061844 : Nat := 4983230072969 + 3 ^ 40 * 4061844 * 2
def baseEnd_4061844 : Nat := 463484070129135833415539

theorem tailTrace_4061844 : CollatzResearch.WordTrace tailWord_4061844 prefixEnd_4061844 463484070129135833415539 := by
  unfold tailWord_4061844
  simp only [CollatzResearch.WordTrace]
  refine ⟨74073810748320185285708293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98765080997760247047611057 74073810748320185285708293)
  ·
    refine ⟨13888839515310034741070305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74073810748320185285708293 13888839515310034741070305)
    ·
      refine ⟨10416629636482526055802729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13888839515310034741070305 10416629636482526055802729)
      ·
        refine ⟨7812472227361894541852047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10416629636482526055802729 7812472227361894541852047)
        ·
          refine ⟨11718708341042841812778071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7812472227361894541852047 11718708341042841812778071)
          ·
            refine ⟨17578062511564262719167107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11718708341042841812778071 17578062511564262719167107)
            ·
              refine ⟨26367093767346394078750661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17578062511564262719167107 26367093767346394078750661)
              ·
                refine ⟨4943830081377448889765749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26367093767346394078750661 4943830081377448889765749)
                ·
                  refine ⟨463484070129135833415539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4943830081377448889765749 463484070129135833415539)
                  ·
                    rfl

theorem cell22_4061844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_4061844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061844 prefixEnd_4061844 := by exact prefixLift 4061844
  have htrace : WordTrace (prefixWord ++ tailWord_4061844) baseStart_4061844 baseEnd_4061844 := by
    simpa [prefixWord, tailWord_4061844, baseEnd_4061844] using wordTrace_append hprefix tailTrace_4061844
  have hstable : (prefixWord ++ tailWord_4061844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061844).length < 2 ^ (prefixWord ++ tailWord_4061844).sum := by decide
  have hdescent : baseEnd_4061844 < baseStart_4061844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061887 : List Nat := [1, 1, 2, 2, 2, 4, 2, 2, 1, 5]
def baseStart_4061887 : Nat := 118140960795 + 4061887 * 2 ^ 59
def prefixEnd_4061887 : Nat := 4983230072969 + 3 ^ 40 * 4061887 * 2
def baseEnd_4061887 : Nat := 1390466930166169721421485

theorem tailTrace_4061887 : CollatzResearch.WordTrace tailWord_4061887 prefixEnd_4061887 1390466930166169721421485 := by
  unfold tailWord_4061887
  simp only [CollatzResearch.WordTrace]
  refine ⟨148149189835484588915231915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98766126556989725943487943 148149189835484588915231915)
  ·
    refine ⟨222223784753226883372847873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148149189835484588915231915 222223784753226883372847873)
    ·
      refine ⟨166667838564920162529635905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222223784753226883372847873 166667838564920162529635905)
      ·
        refine ⟨125000878923690121897226929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166667838564920162529635905 125000878923690121897226929)
        ·
          refine ⟨93750659192767591422920197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125000878923690121897226929 93750659192767591422920197)
          ·
            refine ⟨17578248598643923391797537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93750659192767591422920197 17578248598643923391797537)
            ·
              refine ⟨13183686448982942543848153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17578248598643923391797537 13183686448982942543848153)
              ·
                refine ⟨9887764836737206907886115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13183686448982942543848153 9887764836737206907886115)
                ·
                  refine ⟨14831647255105810361829173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9887764836737206907886115 14831647255105810361829173)
                  ·
                    refine ⟨1390466930166169721421485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14831647255105810361829173 1390466930166169721421485)
                    ·
                      rfl

theorem cell22_4061887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 5].length) (baseStart_4061887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061887 prefixEnd_4061887 := by exact prefixLift 4061887
  have htrace : WordTrace (prefixWord ++ tailWord_4061887) baseStart_4061887 baseEnd_4061887 := by
    simpa [prefixWord, tailWord_4061887, baseEnd_4061887] using wordTrace_append hprefix tailTrace_4061887
  have hstable : (prefixWord ++ tailWord_4061887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061887).length < 2 ^ (prefixWord ++ tailWord_4061887).sum := by decide
  have hdescent : baseEnd_4061887 < baseStart_4061887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061934 : List Nat := [4, 1, 2, 1, 1, 3, 4, 6]
def baseStart_4061934 : Nat := 118140960795 + 4061934 * 2 ^ 59
def prefixEnd_4061934 : Nat := 4983230072969 + 3 ^ 40 * 4061934 * 2
def baseEnd_4061934 : Nat := 154498113247408585055149

theorem tailTrace_4061934 : CollatzResearch.WordTrace tailWord_4061934 prefixEnd_4061934 154498113247408585055149 := by
  unfold tailWord_4061934
  simp only [CollatzResearch.WordTrace]
  refine ⟨18518863008289289492774107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98767269377542877294795237 18518863008289289492774107)
  ·
    refine ⟨27778294512433934239161161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18518863008289289492774107 27778294512433934239161161)
    ·
      refine ⟨20833720884325450679370871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27778294512433934239161161 20833720884325450679370871)
      ·
        refine ⟨31250581326488176019056307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20833720884325450679370871 31250581326488176019056307)
        ·
          refine ⟨46875871989732264028584461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31250581326488176019056307 46875871989732264028584461)
          ·
            refine ⟨17578451996149599010719173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46875871989732264028584461 17578451996149599010719173)
            ·
              refine ⟨3295959749278049814509845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17578451996149599010719173 3295959749278049814509845)
              ·
                refine ⟨154498113247408585055149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3295959749278049814509845 154498113247408585055149)
                ·
                  rfl

theorem cell22_4061934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 6].length) (baseStart_4061934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061934 prefixEnd_4061934 := by exact prefixLift 4061934
  have htrace : WordTrace (prefixWord ++ tailWord_4061934) baseStart_4061934 baseEnd_4061934 := by
    simpa [prefixWord, tailWord_4061934, baseEnd_4061934] using wordTrace_append hprefix tailTrace_4061934
  have hstable : (prefixWord ++ tailWord_4061934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061934).length < 2 ^ (prefixWord ++ tailWord_4061934).sum := by decide
  have hdescent : baseEnd_4061934 < baseStart_4061934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4061962 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 7]
def baseStart_4061962 : Nat := 118140960795 + 4061962 * 2 ^ 59
def prefixEnd_4061962 : Nat := 4983230072969 + 3 ^ 40 * 4061962 * 2
def baseEnd_4061962 : Nat := 463497534732964841932085

theorem tailTrace_4061962 : CollatzResearch.WordTrace tailWord_4061962 prefixEnd_4061962 463497534732964841932085 := by
  unfold tailWord_4061962
  simp only [CollatzResearch.WordTrace]
  refine ⟨37037981327553219181053035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98767950206808584482808093 37037981327553219181053035)
  ·
    refine ⟨55556971991329828771579553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37037981327553219181053035 55556971991329828771579553)
    ·
      refine ⟨41667728993497371578684665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55556971991329828771579553 41667728993497371578684665)
      ·
        refine ⟨31250796745123028684013499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41667728993497371578684665 31250796745123028684013499)
        ·
          refine ⟨46876195117684543026020249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31250796745123028684013499 46876195117684543026020249)
          ·
            refine ⟨35157146338263407269515187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46876195117684543026020249 35157146338263407269515187)
            ·
              refine ⟨52735719507395110904272781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35157146338263407269515187 52735719507395110904272781)
              ·
                refine ⟨19775894815273166589102293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52735719507395110904272781 19775894815273166589102293)
                ·
                  refine ⟨463497534732964841932085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19775894815273166589102293 463497534732964841932085)
                  ·
                    rfl

theorem cell22_4061962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_4061962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4061962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4061962 prefixEnd_4061962 := by exact prefixLift 4061962
  have htrace : WordTrace (prefixWord ++ tailWord_4061962) baseStart_4061962 baseEnd_4061962 := by
    simpa [prefixWord, tailWord_4061962, baseEnd_4061962] using wordTrace_append hprefix tailTrace_4061962
  have hstable : (prefixWord ++ tailWord_4061962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4061962).length < 2 ^ (prefixWord ++ tailWord_4061962).sum := by decide
  have hdescent : baseEnd_4061962 < baseStart_4061962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4061962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062039 : List Nat := [1, 1, 3, 2, 4, 1, 1, 3, 1, 5]
def baseStart_4062039 : Nat := 118140960795 + 4062039 * 2 ^ 59
def prefixEnd_4062039 : Nat := 4983230072969 + 3 ^ 40 * 4062039 * 2
def baseEnd_4062039 : Nat := 1390518962872491991621019

theorem tailTrace_4062039 : CollatzResearch.WordTrace tailWord_4062039 prefixEnd_4062039 1390518962872491991621019 := by
  unfold tailWord_4062039
  simp only [CollatzResearch.WordTrace]
  refine ⟨148154733730933918874765171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98769822487289279249843447 148154733730933918874765171)
  ·
    refine ⟨222232100596400878312147757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148154733730933918874765171 222232100596400878312147757)
    ·
      refine ⟨83337037723650329367055409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222232100596400878312147757 83337037723650329367055409)
      ·
        refine ⟨62502778292737747025291557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83337037723650329367055409 62502778292737747025291557)
        ·
          refine ⟨11719270929888327567242167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62502778292737747025291557 11719270929888327567242167)
          ·
            refine ⟨17578906394832491350863251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11719270929888327567242167 17578906394832491350863251)
            ·
              refine ⟨26368359592248737026294877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17578906394832491350863251 26368359592248737026294877)
              ·
                refine ⟨9888134847093276384860579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26368359592248737026294877 9888134847093276384860579)
                ·
                  refine ⟨14832202270639914577290869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9888134847093276384860579 14832202270639914577290869)
                  ·
                    refine ⟨1390518962872491991621019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14832202270639914577290869 1390518962872491991621019)
                    ·
                      rfl

theorem cell22_4062039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 5].length) (baseStart_4062039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062039 prefixEnd_4062039 := by exact prefixLift 4062039
  have htrace : WordTrace (prefixWord ++ tailWord_4062039) baseStart_4062039 baseEnd_4062039 := by
    simpa [prefixWord, tailWord_4062039, baseEnd_4062039] using wordTrace_append hprefix tailTrace_4062039
  have hstable : (prefixWord ++ tailWord_4062039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062039).length < 2 ^ (prefixWord ++ tailWord_4062039).sum := by decide
  have hdescent : baseEnd_4062039 < baseStart_4062039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062069 : List Nat := [1, 3, 4, 1, 1, 3, 9]
def baseStart_4062069 : Nat := 118140960795 + 4062069 * 2 ^ 59
def prefixEnd_4062069 : Nat := 4983230072969 + 3 ^ 40 * 4062069 * 2
def baseEnd_4062069 : Nat := 51501082684651181976701

theorem tailTrace_4062069 : CollatzResearch.WordTrace tailWord_4062069 prefixEnd_4062069 51501082684651181976701 := by
  unfold tailWord_4062069
  simp only [CollatzResearch.WordTrace]
  refine ⟨148155827920825233998357261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98770551947216822665571507 148155827920825233998357261)
  ·
    refine ⟨55558435470309462749383973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148155827920825233998357261 55558435470309462749383973)
    ·
      refine ⟨10417206650683024265509495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55558435470309462749383973 10417206650683024265509495)
      ·
        refine ⟨15625809976024536398264243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10417206650683024265509495 15625809976024536398264243)
        ·
          refine ⟨23438714964036804597396365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15625809976024536398264243 23438714964036804597396365)
          ·
            refine ⟨8789518111513801724023637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23438714964036804597396365 8789518111513801724023637)
            ·
              refine ⟨51501082684651181976701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8789518111513801724023637 51501082684651181976701)
              ·
                rfl

theorem cell22_4062069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 9].length) (baseStart_4062069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062069 prefixEnd_4062069 := by exact prefixLift 4062069
  have htrace : WordTrace (prefixWord ++ tailWord_4062069) baseStart_4062069 baseEnd_4062069 := by
    simpa [prefixWord, tailWord_4062069, baseEnd_4062069] using wordTrace_append hprefix tailTrace_4062069
  have hstable : (prefixWord ++ tailWord_4062069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062069).length < 2 ^ (prefixWord ++ tailWord_4062069).sum := by decide
  have hdescent : baseEnd_4062069 < baseStart_4062069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062073 : List Nat := [1, 2, 1, 3, 2, 5, 1, 2, 2, 3]
def baseStart_4062073 : Nat := 118140960795 + 4062073 * 2 ^ 59
def prefixEnd_4062073 : Nat := 4983230072969 + 3 ^ 40 * 4062073 * 2
def baseEnd_4062073 : Nat := 1390530601767327236270915

theorem tailTrace_4062073 : CollatzResearch.WordTrace tailWord_4062073 prefixEnd_4062073 1390530601767327236270915 := by
  unfold tailWord_4062073
  simp only [CollatzResearch.WordTrace]
  refine ⟨148155973812810742681502873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98770649208540495121001915 148155973812810742681502873)
  ·
    refine ⟨111116980359608057011127155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148155973812810742681502873 111116980359608057011127155)
    ·
      refine ⟨166675470539412085516690733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111116980359608057011127155 166675470539412085516690733)
      ·
        refine ⟨62503301452279532068759025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166675470539412085516690733 62503301452279532068759025)
        ·
          refine ⟨46877476089209649051569269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62503301452279532068759025 46877476089209649051569269)
          ·
            refine ⟨4394763383363404598584619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 46877476089209649051569269 4394763383363404598584619)
            ·
              refine ⟨6592145075045106897876929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4394763383363404598584619 6592145075045106897876929)
              ·
                refine ⟨4944108806283830173407697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6592145075045106897876929 4944108806283830173407697)
                ·
                  refine ⟨3708081604712872630055773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4944108806283830173407697 3708081604712872630055773)
                  ·
                    refine ⟨1390530601767327236270915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3708081604712872630055773 1390530601767327236270915)
                    ·
                      rfl

theorem cell22_4062073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 2, 3].length) (baseStart_4062073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062073 prefixEnd_4062073 := by exact prefixLift 4062073
  have htrace : WordTrace (prefixWord ++ tailWord_4062073) baseStart_4062073 baseEnd_4062073 := by
    simpa [prefixWord, tailWord_4062073, baseEnd_4062073] using wordTrace_append hprefix tailTrace_4062073
  have hstable : (prefixWord ++ tailWord_4062073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062073).length < 2 ^ (prefixWord ++ tailWord_4062073).sum := by decide
  have hdescent : baseEnd_4062073 < baseStart_4062073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062090 : List Nat := [3, 1, 2, 4, 1, 2, 3, 1, 2, 3]
def baseStart_4062090 : Nat := 118140960795 + 4062090 * 2 ^ 59
def prefixEnd_4062090 : Nat := 4983230072969 + 3 ^ 40 * 4062090 * 2
def baseEnd_4062090 : Nat := 1390536421214744858595863

theorem tailTrace_4062090 : CollatzResearch.WordTrace tailWord_4062090 prefixEnd_4062090 1390536421214744858595863 := by
  unfold tailWord_4062090
  simp only [CollatzResearch.WordTrace]
  refine ⟨37039148463437288646217931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98771062569166103056581149 37039148463437288646217931)
  ·
    refine ⟨55558722695155932969326897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37039148463437288646217931 55558722695155932969326897)
    ·
      refine ⟨41669042021366949726995173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55558722695155932969326897 41669042021366949726995173)
      ·
        refine ⟨7812945379006303073811595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41669042021366949726995173 7812945379006303073811595)
        ·
          refine ⟨11719418068509454610717393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7812945379006303073811595 11719418068509454610717393)
          ·
            refine ⟨8789563551382090958038045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11719418068509454610717393 8789563551382090958038045)
            ·
              refine ⟨3296086331768284109264267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8789563551382090958038045 3296086331768284109264267)
              ·
                refine ⟨4944129497652426163896401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3296086331768284109264267 4944129497652426163896401)
                ·
                  refine ⟨3708097123239319622922301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4944129497652426163896401 3708097123239319622922301)
                  ·
                    refine ⟨1390536421214744858595863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3708097123239319622922301 1390536421214744858595863)
                    ·
                      rfl

theorem cell22_4062090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_4062090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062090 prefixEnd_4062090 := by exact prefixLift 4062090
  have htrace : WordTrace (prefixWord ++ tailWord_4062090) baseStart_4062090 baseEnd_4062090 := by
    simpa [prefixWord, tailWord_4062090, baseEnd_4062090] using wordTrace_append hprefix tailTrace_4062090
  have hstable : (prefixWord ++ tailWord_4062090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062090).length < 2 ^ (prefixWord ++ tailWord_4062090).sum := by decide
  have hdescent : baseEnd_4062090 < baseStart_4062090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062101 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 3, 3]
def baseStart_4062101 : Nat := 118140960795 + 4062101 * 2 ^ 59
def prefixEnd_4062101 : Nat := 4983230072969 + 3 ^ 40 * 4062101 * 2
def baseEnd_4062101 : Nat := 1390540186739544496570829

theorem tailTrace_4062101 : CollatzResearch.WordTrace tailWord_4062101 prefixEnd_4062101 1390540186739544496570829 := by
  unfold tailWord_4062101
  simp only [CollatzResearch.WordTrace]
  refine ⟨148156995056709303463522157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98771330037806202309014771 148156995056709303463522157)
  ·
    refine ⟨55558873146265988798820809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148156995056709303463522157 55558873146265988798820809)
    ·
      refine ⟨41669154859699491599115607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55558873146265988798820809 41669154859699491599115607)
      ·
        refine ⟨62503732289549237398673411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41669154859699491599115607 62503732289549237398673411)
        ·
          refine ⟨93755598434323856098010117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62503732289549237398673411 93755598434323856098010117)
          ·
            refine ⟨17579174706435723018376897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93755598434323856098010117 17579174706435723018376897)
            ·
              refine ⟨13184381029826792263782673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17579174706435723018376897 13184381029826792263782673)
              ·
                refine ⟨9888285772370094197837005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13184381029826792263782673 9888285772370094197837005)
                ·
                  refine ⟨3708107164638785324188877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9888285772370094197837005 3708107164638785324188877)
                  ·
                    refine ⟨1390540186739544496570829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3708107164638785324188877 1390540186739544496570829)
                    ·
                      rfl

theorem cell22_4062101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_4062101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062101 prefixEnd_4062101 := by exact prefixLift 4062101
  have htrace : WordTrace (prefixWord ++ tailWord_4062101) baseStart_4062101 baseEnd_4062101 := by
    simpa [prefixWord, tailWord_4062101, baseEnd_4062101] using wordTrace_append hprefix tailTrace_4062101
  have hstable : (prefixWord ++ tailWord_4062101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062101).length < 2 ^ (prefixWord ++ tailWord_4062101).sum := by decide
  have hdescent : baseEnd_4062101 < baseStart_4062101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062193 : List Nat := [1, 2, 2, 2, 4, 2, 1, 4, 4]
def baseStart_4062193 : Nat := 118140960795 + 4062193 * 2 ^ 59
def prefixEnd_4062193 : Nat := 4983230072969 + 3 ^ 40 * 4062193 * 2
def baseEnd_4062193 : Nat := 463523893406562307756849

theorem tailTrace_4062193 : CollatzResearch.WordTrace tailWord_4062193 prefixEnd_4062193 463523893406562307756849 := by
  unfold tailWord_4062193
  simp only [CollatzResearch.WordTrace]
  refine ⟨148160350572376003175871233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98773567048250668783914155 148160350572376003175871233)
  ·
    refine ⟨111120262929282002381903425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148160350572376003175871233 111120262929282002381903425)
    ·
      refine ⟨83340197196961501786427569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111120262929282002381903425 83340197196961501786427569)
      ·
        refine ⟨62505147897721126339820677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83340197196961501786427569 62505147897721126339820677)
        ·
          refine ⟨11719715230822711188716377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62505147897721126339820677 11719715230822711188716377)
          ·
            refine ⟨8789786423117033391537283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11719715230822711188716377 8789786423117033391537283)
            ·
              refine ⟨13184679634675550087305925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8789786423117033391537283 13184679634675550087305925)
              ·
                refine ⟨2472127431501665641369861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13184679634675550087305925 2472127431501665641369861)
                ·
                  refine ⟨463523893406562307756849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2472127431501665641369861 463523893406562307756849)
                  ·
                    rfl

theorem cell22_4062193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 4].length) (baseStart_4062193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062193 prefixEnd_4062193 := by exact prefixLift 4062193
  have htrace : WordTrace (prefixWord ++ tailWord_4062193) baseStart_4062193 baseEnd_4062193 := by
    simpa [prefixWord, tailWord_4062193, baseEnd_4062193] using wordTrace_append hprefix tailTrace_4062193
  have hstable : (prefixWord ++ tailWord_4062193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062193).length < 2 ^ (prefixWord ++ tailWord_4062193).sum := by decide
  have hdescent : baseEnd_4062193 < baseStart_4062193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062210 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 6]
def baseStart_4062210 : Nat := 118140960795 + 4062210 * 2 ^ 59
def prefixEnd_4062210 : Nat := 4983230072969 + 3 ^ 40 * 4062210 * 2
def baseEnd_4062210 : Nat := 463525833222368181865165

theorem tailTrace_4062210 : CollatzResearch.WordTrace tailWord_4062210 prefixEnd_4062210 463525833222368181865165 := by
  unfold tailWord_4062210
  simp only [CollatzResearch.WordTrace]
  refine ⟨37040242653328603769810021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98773980408876276719493389 37040242653328603769810021)
  ·
    refine ⟨6945045497499113206839379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 37040242653328603769810021 6945045497499113206839379)
    ·
      refine ⟨10417568246248669810259069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6945045497499113206839379 10417568246248669810259069)
      ·
        refine ⟨3906588092343251178847151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10417568246248669810259069 3906588092343251178847151)
        ·
          refine ⟨5859882138514876768270727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3906588092343251178847151 5859882138514876768270727)
          ·
            refine ⟨8789823207772315152406091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5859882138514876768270727 8789823207772315152406091)
            ·
              refine ⟨13184734811658472728609137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8789823207772315152406091 13184734811658472728609137)
              ·
                refine ⟨9888551108743854546456853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13184734811658472728609137 9888551108743854546456853)
                ·
                  refine ⟨463525833222368181865165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9888551108743854546456853 463525833222368181865165)
                  ·
                    rfl

theorem cell22_4062210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_4062210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062210 prefixEnd_4062210 := by exact prefixLift 4062210
  have htrace : WordTrace (prefixWord ++ tailWord_4062210) baseStart_4062210 baseEnd_4062210 := by
    simpa [prefixWord, tailWord_4062210, baseEnd_4062210] using wordTrace_append hprefix tailTrace_4062210
  have hstable : (prefixWord ++ tailWord_4062210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062210).length < 2 ^ (prefixWord ++ tailWord_4062210).sum := by decide
  have hdescent : baseEnd_4062210 < baseStart_4062210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062266 : List Nat := [3, 1, 1, 1, 3, 1, 2, 5, 5]
def baseStart_4062266 : Nat := 118140960795 + 4062266 * 2 ^ 59
def prefixEnd_4062266 : Nat := 4983230072969 + 3 ^ 40 * 4062266 * 2
def baseEnd_4062266 : Nat := 463532223203846355398441

theorem tailTrace_4062266 : CollatzResearch.WordTrace tailWord_4062266 prefixEnd_4062266 463532223203846355398441 := by
  unfold tailWord_4062266
  simp only [CollatzResearch.WordTrace]
  refine ⟨37040753275277884160819663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98775342067407691095519101 37040753275277884160819663)
  ·
    refine ⟨55561129912916826241229495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37040753275277884160819663 55561129912916826241229495)
    ·
      refine ⟨83341694869375239361844243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55561129912916826241229495 83341694869375239361844243)
      ·
        refine ⟨125012542304062859042766365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83341694869375239361844243 125012542304062859042766365)
        ·
          refine ⟨46879703364023572141037387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125012542304062859042766365 46879703364023572141037387)
          ·
            refine ⟨70319555046035358211556081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46879703364023572141037387 70319555046035358211556081)
            ·
              refine ⟨52739666284526518658667061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70319555046035358211556081 52739666284526518658667061)
              ·
                refine ⟨4944343714174361124250037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52739666284526518658667061 4944343714174361124250037)
                ·
                  refine ⟨463532223203846355398441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4944343714174361124250037 463532223203846355398441)
                  ·
                    rfl

theorem cell22_4062266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 5].length) (baseStart_4062266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062266 prefixEnd_4062266 := by exact prefixLift 4062266
  have htrace : WordTrace (prefixWord ++ tailWord_4062266) baseStart_4062266 baseEnd_4062266 := by
    simpa [prefixWord, tailWord_4062266, baseEnd_4062266] using wordTrace_append hprefix tailTrace_4062266
  have hstable : (prefixWord ++ tailWord_4062266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062266).length < 2 ^ (prefixWord ++ tailWord_4062266).sum := by decide
  have hdescent : baseEnd_4062266 < baseStart_4062266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062270 : List Nat := [4, 2, 1, 3, 1, 1, 2, 2, 3, 3]
def baseStart_4062270 : Nat := 118140960795 + 4062270 * 2 ^ 59
def prefixEnd_4062270 : Nat := 4983230072969 + 3 ^ 40 * 4062270 * 2
def baseEnd_4062270 : Nat := 1390598038893284389095311

theorem tailTrace_4062270 : CollatzResearch.WordTrace tailWord_4062270 prefixEnd_4062270 1390598038893284389095311 := by
  unfold tailWord_4062270
  simp only [CollatzResearch.WordTrace]
  refine ⟨18520394874137130665803033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98775439328731363550949509 18520394874137130665803033)
  ·
    refine ⟨13890296155602847999352275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18520394874137130665803033 13890296155602847999352275)
    ·
      refine ⟨20835444233404271999028413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13890296155602847999352275 20835444233404271999028413)
      ·
        refine ⟨7813291587526601999635655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20835444233404271999028413 7813291587526601999635655)
        ·
          refine ⟨11719937381289902999453483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7813291587526601999635655 11719937381289902999453483)
          ·
            refine ⟨17579906071934854499180225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11719937381289902999453483 17579906071934854499180225)
            ·
              refine ⟨13184929553951140874385169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17579906071934854499180225 13184929553951140874385169)
              ·
                refine ⟨9888697165463355655788877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13184929553951140874385169 9888697165463355655788877)
                ·
                  refine ⟨3708261437048758370920829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9888697165463355655788877 3708261437048758370920829)
                  ·
                    refine ⟨1390598038893284389095311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3708261437048758370920829 1390598038893284389095311)
                    ·
                      rfl

theorem cell22_4062270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_4062270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062270 prefixEnd_4062270 := by exact prefixLift 4062270
  have htrace : WordTrace (prefixWord ++ tailWord_4062270) baseStart_4062270 baseEnd_4062270 := by
    simpa [prefixWord, tailWord_4062270, baseEnd_4062270] using wordTrace_append hprefix tailTrace_4062270
  have hstable : (prefixWord ++ tailWord_4062270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062270).length < 2 ^ (prefixWord ++ tailWord_4062270).sum := by decide
  have hdescent : baseEnd_4062270 < baseStart_4062270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062356 : List Nat := [2, 4, 2, 14]
def baseStart_4062356 : Nat := 118140960795 + 4062356 * 2 ^ 59
def prefixEnd_4062356 : Nat := 4983230072969 + 3 ^ 40 * 4062356 * 2
def baseEnd_4062356 : Nat := 1907582274966815955343

theorem tailTrace_4062356 : CollatzResearch.WordTrace tailWord_4062356 prefixEnd_4062356 1907582274966815955343 := by
  unfold tailWord_4062356
  simp only [CollatzResearch.WordTrace]
  refine ⟨74083147835392741007027461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98777530447190321342703281 74083147835392741007027461)
  ·
    refine ⟨13890590219136138938817649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74083147835392741007027461 13890590219136138938817649)
    ·
      refine ⟨10417942664352104204113237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13890590219136138938817649 10417942664352104204113237)
      ·
        refine ⟨1907582274966815955343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 10417942664352104204113237 1907582274966815955343)
        ·
          rfl

theorem cell22_4062356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 14].length) (baseStart_4062356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062356 prefixEnd_4062356 := by exact prefixLift 4062356
  have htrace : WordTrace (prefixWord ++ tailWord_4062356) baseStart_4062356 baseEnd_4062356 := by
    simpa [prefixWord, tailWord_4062356, baseEnd_4062356] using wordTrace_append hprefix tailTrace_4062356
  have hstable : (prefixWord ++ tailWord_4062356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062356).length < 2 ^ (prefixWord ++ tailWord_4062356).sum := by decide
  have hdescent : baseEnd_4062356 < baseStart_4062356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062360 : List Nat := [2, 1, 2, 4, 2, 1, 1, 4, 2, 3]
def baseStart_4062360 : Nat := 118140960795 + 4062360 * 2 ^ 59
def prefixEnd_4062360 : Nat := 4983230072969 + 3 ^ 40 * 4062360 * 2
def baseEnd_4062360 : Nat := 1390628847732554154345035

theorem tailTrace_4062360 : CollatzResearch.WordTrace tailWord_4062360 prefixEnd_4062360 1390628847732554154345035 := by
  unfold tailWord_4062360
  simp only [CollatzResearch.WordTrace]
  refine ⟨74083220781385495348600267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98777627708513993798133689 74083220781385495348600267)
  ·
    refine ⟨111124831172078243022900401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74083220781385495348600267 111124831172078243022900401)
    ·
      refine ⟨83343623379058682267175301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111124831172078243022900401 83343623379058682267175301)
      ·
        refine ⟨15626929383573502925095369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83343623379058682267175301 15626929383573502925095369)
        ·
          refine ⟨11720197037680127193821527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15626929383573502925095369 11720197037680127193821527)
          ·
            refine ⟨17580295556520190790732291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11720197037680127193821527 17580295556520190790732291)
            ·
              refine ⟨26370443334780286186098437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17580295556520190790732291 26370443334780286186098437)
              ·
                refine ⟨4944458125271303659893457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26370443334780286186098437 4944458125271303659893457)
                ·
                  refine ⟨3708343593953477744920093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4944458125271303659893457 3708343593953477744920093)
                  ·
                    refine ⟨1390628847732554154345035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3708343593953477744920093 1390628847732554154345035)
                    ·
                      rfl

theorem cell22_4062360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 4, 2, 3].length) (baseStart_4062360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062360 prefixEnd_4062360 := by exact prefixLift 4062360
  have htrace : WordTrace (prefixWord ++ tailWord_4062360) baseStart_4062360 baseEnd_4062360 := by
    simpa [prefixWord, tailWord_4062360, baseEnd_4062360] using wordTrace_append hprefix tailTrace_4062360
  have hstable : (prefixWord ++ tailWord_4062360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062360).length < 2 ^ (prefixWord ++ tailWord_4062360).sum := by decide
  have hdescent : baseEnd_4062360 < baseStart_4062360 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062362 : List Nat := [3, 1, 1, 5, 1, 1, 4, 2, 4]
def baseStart_4062362 : Nat := 118140960795 + 4062362 * 2 ^ 59
def prefixEnd_4062362 : Nat := 4983230072969 + 3 ^ 40 * 4062362 * 2
def baseEnd_4062362 : Nat := 463543177457808938598343

theorem tailTrace_4062362 : CollatzResearch.WordTrace tailWord_4062362 prefixEnd_4062362 463543177457808938598343 := by
  unfold tailWord_4062362
  simp only [CollatzResearch.WordTrace]
  refine ⟨37041628627190936259693335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98777676339175830025848893 37041628627190936259693335)
  ·
    refine ⟨55562442940786404389540003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37041628627190936259693335 55562442940786404389540003)
    ·
      refine ⟨83343664411179606584310005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55562442940786404389540003 83343664411179606584310005)
      ·
        refine ⟨7813468538548088117279063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83343664411179606584310005 7813468538548088117279063)
        ·
          refine ⟨11720202807822132175918595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7813468538548088117279063 11720202807822132175918595)
          ·
            refine ⟨17580304211733198263877893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11720202807822132175918595 17580304211733198263877893)
            ·
              refine ⟨3296307039699974674477105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17580304211733198263877893 3296307039699974674477105)
              ·
                refine ⟨2472230279774981005857829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3296307039699974674477105 2472230279774981005857829)
                ·
                  refine ⟨463543177457808938598343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2472230279774981005857829 463543177457808938598343)
                  ·
                    rfl

theorem cell22_4062362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 4].length) (baseStart_4062362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062362 prefixEnd_4062362 := by exact prefixLift 4062362
  have htrace : WordTrace (prefixWord ++ tailWord_4062362) baseStart_4062362 baseEnd_4062362 := by
    simpa [prefixWord, tailWord_4062362, baseEnd_4062362] using wordTrace_append hprefix tailTrace_4062362
  have hstable : (prefixWord ++ tailWord_4062362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062362).length < 2 ^ (prefixWord ++ tailWord_4062362).sum := by decide
  have hdescent : baseEnd_4062362 < baseStart_4062362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062373 : List Nat := [1, 3, 1, 2, 1, 6, 1, 7]
def baseStart_4062373 : Nat := 118140960795 + 4062373 * 2 ^ 59
def prefixEnd_4062373 : Nat := 4983230072969 + 3 ^ 40 * 4062373 * 2
def baseEnd_4062373 : Nat := 154514810877580717085555

theorem tailTrace_4062373 : CollatzResearch.WordTrace tailWord_4062373 prefixEnd_4062373 154514810877580717085555 := by
  unfold tailWord_4062373
  simp only [CollatzResearch.WordTrace]
  refine ⟨148166915711723893917423773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98777943807815929278282515 148166915711723893917423773)
  ·
    refine ⟨55562593391896460219033915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148166915711723893917423773 55562593391896460219033915)
    ·
      refine ⟨83343890087844690328550873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55562593391896460219033915 83343890087844690328550873)
      ·
        refine ⟨62507917565883517746413155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83343890087844690328550873 62507917565883517746413155)
        ·
          refine ⟨93761876348825276619619733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62507917565883517746413155 93761876348825276619619733)
          ·
            refine ⟨4395087953851184841544675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 93761876348825276619619733 4395087953851184841544675)
            ·
              refine ⟨6592631930776777262317013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4395087953851184841544675 6592631930776777262317013)
              ·
                refine ⟨154514810877580717085555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6592631930776777262317013 154514810877580717085555)
                ·
                  rfl

theorem cell22_4062373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 7].length) (baseStart_4062373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062373 prefixEnd_4062373 := by exact prefixLift 4062373
  have htrace : WordTrace (prefixWord ++ tailWord_4062373) baseStart_4062373 baseEnd_4062373 := by
    simpa [prefixWord, tailWord_4062373, baseEnd_4062373] using wordTrace_append hprefix tailTrace_4062373
  have hstable : (prefixWord ++ tailWord_4062373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062373).length < 2 ^ (prefixWord ++ tailWord_4062373).sum := by decide
  have hdescent : baseEnd_4062373 < baseStart_4062373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062418 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 7]
def baseStart_4062418 : Nat := 118140960795 + 4062418 * 2 ^ 59
def prefixEnd_4062418 : Nat := 4983230072969 + 3 ^ 40 * 4062418 * 2
def baseEnd_4062418 : Nat := 463549567439287112131619

theorem tailTrace_4062418 : CollatzResearch.WordTrace tailWord_4062418 prefixEnd_4062418 463549567439287112131619 := by
  unfold tailWord_4062418
  simp only [CollatzResearch.WordTrace]
  refine ⟨37042139249140216650702977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98779037997707244401874605 37042139249140216650702977)
  ·
    refine ⟨27781604436855162488027233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37042139249140216650702977 27781604436855162488027233)
    ·
      refine ⟨20836203327641371866020425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27781604436855162488027233 20836203327641371866020425)
      ·
        refine ⟨15627152495731028899515319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20836203327641371866020425 15627152495731028899515319)
        ·
          refine ⟨23440728743596543349272979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15627152495731028899515319 23440728743596543349272979)
          ·
            refine ⟨35161093115394815023909469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23440728743596543349272979 35161093115394815023909469)
            ·
              refine ⟨13185409918273055633966051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35161093115394815023909469 13185409918273055633966051)
              ·
                refine ⟨19778114877409583450949077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13185409918273055633966051 19778114877409583450949077)
                ·
                  refine ⟨463549567439287112131619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19778114877409583450949077 463549567439287112131619)
                  ·
                    rfl

theorem cell22_4062418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_4062418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062418 prefixEnd_4062418 := by exact prefixLift 4062418
  have htrace : WordTrace (prefixWord ++ tailWord_4062418) baseStart_4062418 baseEnd_4062418 := by
    simpa [prefixWord, tailWord_4062418, baseEnd_4062418] using wordTrace_append hprefix tailTrace_4062418
  have hstable : (prefixWord ++ tailWord_4062418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062418).length < 2 ^ (prefixWord ++ tailWord_4062418).sum := by decide
  have hdescent : baseEnd_4062418 < baseStart_4062418 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062433 : List Nat := [1, 2, 3, 1, 3, 2, 2, 1, 2, 5]
def baseStart_4062433 : Nat := 118140960795 + 4062433 * 2 ^ 59
def prefixEnd_4062433 : Nat := 4983230072969 + 3 ^ 40 * 4062433 * 2
def baseEnd_4062433 : Nat := 1390653837124406297269811

theorem tailTrace_4062433 : CollatzResearch.WordTrace tailWord_4062433 prefixEnd_4062433 1390653837124406297269811 := by
  unfold tailWord_4062433
  simp only [CollatzResearch.WordTrace]
  refine ⟨148169104091506524164607953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98779402727671016109738635 148169104091506524164607953)
  ·
    refine ⟨111126828068629893123455965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148169104091506524164607953 111126828068629893123455965)
    ·
      refine ⟨41672560525736209921295987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111126828068629893123455965 41672560525736209921295987)
      ·
        refine ⟨62508840788604314881943981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41672560525736209921295987 62508840788604314881943981)
        ·
          refine ⟨23440815295726618080728993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62508840788604314881943981 23440815295726618080728993)
          ·
            refine ⟨17580611471794963560546745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23440815295726618080728993 17580611471794963560546745)
            ·
              refine ⟨13185458603846222670410059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17580611471794963560546745 13185458603846222670410059)
              ·
                refine ⟨19778187905769334005615089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13185458603846222670410059 19778187905769334005615089)
                ·
                  refine ⟨14833640929327000504211317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19778187905769334005615089 14833640929327000504211317)
                  ·
                    refine ⟨1390653837124406297269811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14833640929327000504211317 1390653837124406297269811)
                    ·
                      rfl

theorem cell22_4062433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_4062433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062433 prefixEnd_4062433 := by exact prefixLift 4062433
  have htrace : WordTrace (prefixWord ++ tailWord_4062433) baseStart_4062433 baseEnd_4062433 := by
    simpa [prefixWord, tailWord_4062433, baseEnd_4062433] using wordTrace_append hprefix tailTrace_4062433
  have hstable : (prefixWord ++ tailWord_4062433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062433).length < 2 ^ (prefixWord ++ tailWord_4062433).sum := by decide
  have hdescent : baseEnd_4062433 < baseStart_4062433 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062465 : List Nat := [1, 2, 4, 1, 1, 3, 2, 3, 1, 4]
def baseStart_4062465 : Nat := 118140960795 + 4062465 * 2 ^ 59
def prefixEnd_4062465 : Nat := 4983230072969 + 3 ^ 40 * 4062465 * 2
def baseEnd_4062465 : Nat := 1390664791378368880469713

theorem tailTrace_4062465 : CollatzResearch.WordTrace tailWord_4062465 prefixEnd_4062465 1390664791378368880469713 := by
  unfold tailWord_4062465
  simp only [CollatzResearch.WordTrace]
  refine ⟨148170271227390593629772849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98780180818260395753181899 148170271227390593629772849)
  ·
    refine ⟨111127703420542945222329637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148170271227390593629772849 111127703420542945222329637)
    ·
      refine ⟨20836444391351802229186807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111127703420542945222329637 20836444391351802229186807)
      ·
        refine ⟨31254666587027703343780211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20836444391351802229186807 31254666587027703343780211)
        ·
          refine ⟨46881999880541555015670317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31254666587027703343780211 46881999880541555015670317)
          ·
            refine ⟨17580749955203083130876369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46881999880541555015670317 17580749955203083130876369)
            ·
              refine ⟨13185562466402312348157277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17580749955203083130876369 13185562466402312348157277)
              ·
                refine ⟨4944585924900867130558979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13185562466402312348157277 4944585924900867130558979)
                ·
                  refine ⟨7416878887351300695838469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4944585924900867130558979 7416878887351300695838469)
                  ·
                    refine ⟨1390664791378368880469713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7416878887351300695838469 1390664791378368880469713)
                    ·
                      rfl

theorem cell22_4062465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_4062465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062465 prefixEnd_4062465 := by exact prefixLift 4062465
  have htrace : WordTrace (prefixWord ++ tailWord_4062465) baseStart_4062465 baseEnd_4062465 := by
    simpa [prefixWord, tailWord_4062465, baseEnd_4062465] using wordTrace_append hprefix tailTrace_4062465
  have hstable : (prefixWord ++ tailWord_4062465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062465).length < 2 ^ (prefixWord ++ tailWord_4062465).sum := by decide
  have hdescent : baseEnd_4062465 < baseStart_4062465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062525 : List Nat := [1, 4, 1, 5, 1, 10]
def baseStart_4062525 : Nat := 118140960795 + 4062525 * 2 ^ 59
def prefixEnd_4062525 : Nat := 4983230072969 + 3 ^ 40 * 4062525 * 2
def baseEnd_4062525 : Nat := 17168954698821589184809

theorem tailTrace_4062525 : CollatzResearch.WordTrace tailWord_4062525 prefixEnd_4062525 17168954698821589184809 := by
  unfold tailWord_4062525
  simp only [CollatzResearch.WordTrace]
  refine ⟨148172459607173223876957029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98781639738115482584638019 148172459607173223876957029)
  ·
    refine ⟨27782336176344979476929443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148172459607173223876957029 27782336176344979476929443)
    ·
      refine ⟨41673504264517469215394165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27782336176344979476929443 41673504264517469215394165)
      ·
        refine ⟨3906891024798512738943203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41673504264517469215394165 3906891024798512738943203)
        ·
          refine ⟨5860336537197769108414805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3906891024798512738943203 5860336537197769108414805)
          ·
            refine ⟨17168954698821589184809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5860336537197769108414805 17168954698821589184809)
            ·
              rfl

theorem cell22_4062525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 10].length) (baseStart_4062525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062525 prefixEnd_4062525 := by exact prefixLift 4062525
  have htrace : WordTrace (prefixWord ++ tailWord_4062525) baseStart_4062525 baseEnd_4062525 := by
    simpa [prefixWord, tailWord_4062525, baseEnd_4062525] using wordTrace_append hprefix tailTrace_4062525
  have hstable : (prefixWord ++ tailWord_4062525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062525).length < 2 ^ (prefixWord ++ tailWord_4062525).sum := by decide
  have hdescent : baseEnd_4062525 < baseStart_4062525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062529 : List Nat := [1, 2, 5, 2, 1, 2, 2, 2, 2, 3]
def baseStart_4062529 : Nat := 118140960795 + 4062529 * 2 ^ 59
def prefixEnd_4062529 : Nat := 4983230072969 + 3 ^ 40 * 4062529 * 2
def baseEnd_4062529 : Nat := 1390686699886294046869517

theorem tailTrace_4062529 : CollatzResearch.WordTrace tailWord_4062529 prefixEnd_4062529 1390686699886294046869517 := by
  unfold tailWord_4062529
  simp only [CollatzResearch.WordTrace]
  refine ⟨148172605499158732560102641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98781736999439155040068427 148172605499158732560102641)
  ·
    refine ⟨111129454124369049420076981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148172605499158732560102641 111129454124369049420076981)
    ·
      refine ⟨10418386324159598383132217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111129454124369049420076981 10418386324159598383132217)
      ·
        refine ⟨7813789743119698787349163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10418386324159598383132217 7813789743119698787349163)
        ·
          refine ⟨11720684614679548181023745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7813789743119698787349163 11720684614679548181023745)
          ·
            refine ⟨8790513461009661135767809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11720684614679548181023745 8790513461009661135767809)
            ·
              refine ⟨6592885095757245851825857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8790513461009661135767809 6592885095757245851825857)
              ·
                refine ⟨4944663821817934388869393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6592885095757245851825857 4944663821817934388869393)
                ·
                  refine ⟨3708497866363450791652045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4944663821817934388869393 3708497866363450791652045)
                  ·
                    refine ⟨1390686699886294046869517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3708497866363450791652045 1390686699886294046869517)
                    ·
                      rfl

theorem cell22_4062529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 2, 3].length) (baseStart_4062529 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062529 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062529 prefixEnd_4062529 := by exact prefixLift 4062529
  have htrace : WordTrace (prefixWord ++ tailWord_4062529) baseStart_4062529 baseEnd_4062529 := by
    simpa [prefixWord, tailWord_4062529, baseEnd_4062529] using wordTrace_append hprefix tailTrace_4062529
  have hstable : (prefixWord ++ tailWord_4062529).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062529).length < 2 ^ (prefixWord ++ tailWord_4062529).sum := by decide
  have hdescent : baseEnd_4062529 < baseStart_4062529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062617 : List Nat := [1, 2, 1, 2, 1, 6, 2, 2, 1, 4]
def baseStart_4062617 : Nat := 118140960795 + 4062617 * 2 ^ 59
def prefixEnd_4062617 : Nat := 4983230072969 + 3 ^ 40 * 4062617 * 2
def baseEnd_4062617 : Nat := 1390716824084691150669247

theorem tailTrace_4062617 : CollatzResearch.WordTrace tailWord_4062617 prefixEnd_4062617 1390716824084691150669247 := by
  unfold tailWord_4062617
  simp only [CollatzResearch.WordTrace]
  refine ⟨148175815122839923589306105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98783876748559949059537403 148175815122839923589306105)
  ·
    refine ⟨111131861342129942691979579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148175815122839923589306105 111131861342129942691979579)
    ·
      refine ⟨166697792013194914037969369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111131861342129942691979579 166697792013194914037969369)
      ·
        refine ⟨125023344009896185528477027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166697792013194914037969369 125023344009896185528477027)
        ·
          refine ⟨187535016014844278292715541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125023344009896185528477027 187535016014844278292715541)
          ·
            refine ⟨8790703875695825544971041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187535016014844278292715541 8790703875695825544971041)
            ·
              refine ⟨6593027906771869158728281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8790703875695825544971041 6593027906771869158728281)
              ·
                refine ⟨4944770930078901869046211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6593027906771869158728281 4944770930078901869046211)
                ·
                  refine ⟨7417156395118352803569317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4944770930078901869046211 7417156395118352803569317)
                  ·
                    refine ⟨1390716824084691150669247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7417156395118352803569317 1390716824084691150669247)
                    ·
                      rfl

theorem cell22_4062617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 2, 1, 4].length) (baseStart_4062617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062617 prefixEnd_4062617 := by exact prefixLift 4062617
  have htrace : WordTrace (prefixWord ++ tailWord_4062617) baseStart_4062617 baseEnd_4062617 := by
    simpa [prefixWord, tailWord_4062617, baseEnd_4062617] using wordTrace_append hprefix tailTrace_4062617
  have hstable : (prefixWord ++ tailWord_4062617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062617).length < 2 ^ (prefixWord ++ tailWord_4062617).sum := by decide
  have hdescent : baseEnd_4062617 < baseStart_4062617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062647 : List Nat := [1, 1, 3, 1, 3, 2, 2, 4, 2, 3]
def baseStart_4062647 : Nat := 118140960795 + 4062647 * 2 ^ 59
def prefixEnd_4062647 : Nat := 4983230072969 + 3 ^ 40 * 4062647 * 2
def baseEnd_4062647 : Nat := 1390727093697781072419155

theorem tailTrace_4062647 : CollatzResearch.WordTrace tailWord_4062647 prefixEnd_4062647 1390727093697781072419155 := by
  unfold tailWord_4062647
  simp only [CollatzResearch.WordTrace]
  refine ⟨148176909312731238712898195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98784606208487492475265463 148176909312731238712898195)
  ·
    refine ⟨222265363969096858069347293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148176909312731238712898195 222265363969096858069347293)
    ·
      refine ⟨83349511488411321776005235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222265363969096858069347293 83349511488411321776005235)
      ·
        refine ⟨125024267232616982664007853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83349511488411321776005235 125024267232616982664007853)
        ·
          refine ⟨46884100212231368499002945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125024267232616982664007853 46884100212231368499002945)
          ·
            refine ⟨35163075159173526374252209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46884100212231368499002945 35163075159173526374252209)
            ·
              refine ⟨26372306369380144780689157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35163075159173526374252209 26372306369380144780689157)
              ·
                refine ⟨4944807444258777146379217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26372306369380144780689157 4944807444258777146379217)
                ·
                  refine ⟨3708605583194082859784413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4944807444258777146379217 3708605583194082859784413)
                  ·
                    refine ⟨1390727093697781072419155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3708605583194082859784413 1390727093697781072419155)
                    ·
                      rfl

theorem cell22_4062647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_4062647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062647 prefixEnd_4062647 := by exact prefixLift 4062647
  have htrace : WordTrace (prefixWord ++ tailWord_4062647) baseStart_4062647 baseEnd_4062647 := by
    simpa [prefixWord, tailWord_4062647, baseEnd_4062647] using wordTrace_append hprefix tailTrace_4062647
  have hstable : (prefixWord ++ tailWord_4062647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062647).length < 2 ^ (prefixWord ++ tailWord_4062647).sum := by decide
  have hdescent : baseEnd_4062647 < baseStart_4062647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062649 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 6]
def baseStart_4062649 : Nat := 118140960795 + 4062649 * 2 ^ 59
def prefixEnd_4062649 : Nat := 4983230072969 + 3 ^ 40 * 4062649 * 2
def baseEnd_4062649 : Nat := 463575926112884577956383

theorem tailTrace_4062649 : CollatzResearch.WordTrace tailWord_4062649 prefixEnd_4062649 463575926112884577956383 := by
  unfold tailWord_4062649
  simp only [CollatzResearch.WordTrace]
  refine ⟨148176982258723993054471001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98784654839149328702980667 148176982258723993054471001)
  ·
    refine ⟨111132736694042994790853251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148176982258723993054471001 111132736694042994790853251)
    ·
      refine ⟨166699105041064492186279877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111132736694042994790853251 166699105041064492186279877)
      ·
        refine ⟨31256082195199592284927477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166699105041064492186279877 31256082195199592284927477)
        ·
          refine ⟨2930257705799961776711951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 31256082195199592284927477 2930257705799961776711951)
          ·
            refine ⟨4395386558699942665067927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2930257705799961776711951 4395386558699942665067927)
            ·
              refine ⟨6593079838049913997601891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4395386558699942665067927 6593079838049913997601891)
              ·
                refine ⟨9889619757074870996402837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593079838049913997601891 9889619757074870996402837)
                ·
                  refine ⟨463575926112884577956383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9889619757074870996402837 463575926112884577956383)
                  ·
                    rfl

theorem cell22_4062649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 6].length) (baseStart_4062649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062649 prefixEnd_4062649 := by exact prefixLift 4062649
  have htrace : WordTrace (prefixWord ++ tailWord_4062649) baseStart_4062649 baseEnd_4062649 := by
    simpa [prefixWord, tailWord_4062649, baseEnd_4062649] using wordTrace_append hprefix tailTrace_4062649
  have hstable : (prefixWord ++ tailWord_4062649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062649).length < 2 ^ (prefixWord ++ tailWord_4062649).sum := by decide
  have hdescent : baseEnd_4062649 < baseStart_4062649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062735 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 7, 4]
def baseStart_4062735 : Nat := 118140960795 + 4062735 * 2 ^ 59
def prefixEnd_4062735 : Nat := 4983230072969 + 3 ^ 40 * 4062735 * 2
def baseEnd_4062735 : Nat := 1390757217896178176218885

theorem tailTrace_4062735 : CollatzResearch.WordTrace tailWord_4062735 prefixEnd_4062735 1390757217896178176218885 := by
  unfold tailWord_4062735
  simp only [CollatzResearch.WordTrace]
  refine ⟨148180118936412429742101659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98786745957608286494734439 148180118936412429742101659)
  ·
    refine ⟨222270178404618644613152489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148180118936412429742101659 222270178404618644613152489)
    ·
      refine ⟨166702633803463983459864367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222270178404618644613152489 166702633803463983459864367)
      ·
        refine ⟨250053950705195975189796551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166702633803463983459864367 250053950705195975189796551)
        ·
          refine ⟨375080926057793962784694827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250053950705195975189796551 375080926057793962784694827)
          ·
            refine ⟨562621389086690944177042241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 375080926057793962784694827 562621389086690944177042241)
            ·
              refine ⟨421966041815018208132781681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 562621389086690944177042241 421966041815018208132781681)
              ·
                refine ⟨316474531361263656099586261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 421966041815018208132781681 316474531361263656099586261)
                ·
                  refine ⟨7417371828779616939834053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 316474531361263656099586261 7417371828779616939834053)
                  ·
                    refine ⟨1390757217896178176218885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7417371828779616939834053 1390757217896178176218885)
                    ·
                      rfl

theorem cell22_4062735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 4].length) (baseStart_4062735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062735 prefixEnd_4062735 := by exact prefixLift 4062735
  have htrace : WordTrace (prefixWord ++ tailWord_4062735) baseStart_4062735 baseEnd_4062735 := by
    simpa [prefixWord, tailWord_4062735, baseEnd_4062735] using wordTrace_append hprefix tailTrace_4062735
  have hstable : (prefixWord ++ tailWord_4062735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062735).length < 2 ^ (prefixWord ++ tailWord_4062735).sum := by decide
  have hdescent : baseEnd_4062735 < baseStart_4062735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062812 : List Nat := [2, 2, 4, 1, 2, 1, 10]
def baseStart_4062812 : Nat := 118140960795 + 4062812 * 2 ^ 59
def prefixEnd_4062812 : Nat := 4983230072969 + 3 ^ 40 * 4062812 * 2
def baseEnd_4062812 : Nat := 51510502835917616371987

theorem tailTrace_4062812 : CollatzResearch.WordTrace tailWord_4062812 prefixEnd_4062812 51510502835917616371987 := by
  unfold tailWord_4062812
  simp only [CollatzResearch.WordTrace]
  refine ⟨74091463678566735946327345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98788618238088981261769793 74091463678566735946327345)
  ·
    refine ⟨55568597758925051959745509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74091463678566735946327345 55568597758925051959745509)
    ·
      refine ⟨10419112079798447242452283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55568597758925051959745509 10419112079798447242452283)
      ·
        refine ⟨15628668119697670863678425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10419112079798447242452283 15628668119697670863678425)
        ·
          refine ⟨11721501089773253147758819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15628668119697670863678425 11721501089773253147758819)
          ·
            refine ⟨17582251634659879721638229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11721501089773253147758819 17582251634659879721638229)
            ·
              refine ⟨51510502835917616371987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17582251634659879721638229 51510502835917616371987)
              ·
                rfl

theorem cell22_4062812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 10].length) (baseStart_4062812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062812 prefixEnd_4062812 := by exact prefixLift 4062812
  have htrace : WordTrace (prefixWord ++ tailWord_4062812) baseStart_4062812 baseEnd_4062812 := by
    simpa [prefixWord, tailWord_4062812, baseEnd_4062812] using wordTrace_append hprefix tailTrace_4062812
  have hstable : (prefixWord ++ tailWord_4062812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062812).length < 2 ^ (prefixWord ++ tailWord_4062812).sum := by decide
  have hdescent : baseEnd_4062812 < baseStart_4062812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062829 : List Nat := [1, 5, 1, 1, 4, 1, 2, 7]
def baseStart_4062829 : Nat := 118140960795 + 4062829 * 2 ^ 59
def prefixEnd_4062829 : Nat := 4983230072969 + 3 ^ 40 * 4062829 * 2
def baseEnd_4062829 : Nat := 154532155113021473818733

theorem tailTrace_4062829 : CollatzResearch.WordTrace tailWord_4062829 prefixEnd_4062829 154532155113021473818733 := by
  unfold tailWord_4062829
  simp only [CollatzResearch.WordTrace]
  refine ⟨148183547398071883796023541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98789031598714589197349027 148183547398071883796023541)
  ·
    refine ⟨13892207568569239105877207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148183547398071883796023541 13892207568569239105877207)
    ·
      refine ⟨20838311352853858658815811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13892207568569239105877207 20838311352853858658815811)
      ·
        refine ⟨31257467029280787988223717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20838311352853858658815811 31257467029280787988223717)
        ·
          refine ⟨5860775067990147747791947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31257467029280787988223717 5860775067990147747791947)
          ·
            refine ⟨8791162601985221621687921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5860775067990147747791947 8791162601985221621687921)
            ·
              refine ⟨6593371951488916216265941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8791162601985221621687921 6593371951488916216265941)
              ·
                refine ⟨154532155113021473818733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6593371951488916216265941 154532155113021473818733)
                ·
                  rfl

theorem cell22_4062829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 7].length) (baseStart_4062829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062829 prefixEnd_4062829 := by exact prefixLift 4062829
  have htrace : WordTrace (prefixWord ++ tailWord_4062829) baseStart_4062829 baseEnd_4062829 := by
    simpa [prefixWord, tailWord_4062829, baseEnd_4062829] using wordTrace_append hprefix tailTrace_4062829
  have hstable : (prefixWord ++ tailWord_4062829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062829).length < 2 ^ (prefixWord ++ tailWord_4062829).sum := by decide
  have hdescent : baseEnd_4062829 < baseStart_4062829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4062979 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 5, 3]
def baseStart_4062979 : Nat := 118140960795 + 4062979 * 2 ^ 59
def prefixEnd_4062979 : Nat := 4983230072969 + 3 ^ 40 * 4062979 * 2
def baseEnd_4062979 : Nat := 1390840744082642873118137

theorem tailTrace_4062979 : CollatzResearch.WordTrace tailWord_4062979 prefixEnd_4062979 1390840744082642873118137 := by
  unfold tailWord_4062979
  simp only [CollatzResearch.WordTrace]
  refine ⟨148189018347528459413983991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98792678898352306275989327 148189018347528459413983991)
  ·
    refine ⟨222283527521292689120975987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148189018347528459413983991 222283527521292689120975987)
    ·
      refine ⟨333425291281939033681463981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222283527521292689120975987 333425291281939033681463981)
      ·
        refine ⟨125034484230727137630548993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333425291281939033681463981 125034484230727137630548993)
        ·
          refine ⟨93775863173045353222911745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125034484230727137630548993 93775863173045353222911745)
          ·
            refine ⟨70331897379784014917183809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93775863173045353222911745 70331897379784014917183809)
            ·
              refine ⟨52748923034838011187887857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70331897379784014917183809 52748923034838011187887857)
              ·
                refine ⟨39561692276128508390915893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52748923034838011187887857 39561692276128508390915893)
                ·
                  refine ⟨3708908650887047661648365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 39561692276128508390915893 3708908650887047661648365)
                  ·
                    refine ⟨1390840744082642873118137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3708908650887047661648365 1390840744082642873118137)
                    ·
                      rfl

theorem cell22_4062979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 5, 3].length) (baseStart_4062979 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4062979 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4062979 prefixEnd_4062979 := by exact prefixLift 4062979
  have htrace : WordTrace (prefixWord ++ tailWord_4062979) baseStart_4062979 baseEnd_4062979 := by
    simpa [prefixWord, tailWord_4062979, baseEnd_4062979] using wordTrace_append hprefix tailTrace_4062979
  have hstable : (prefixWord ++ tailWord_4062979).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4062979).length < 2 ^ (prefixWord ++ tailWord_4062979).sum := by decide
  have hdescent : baseEnd_4062979 < baseStart_4062979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4062979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063129 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 2, 6]
def baseStart_4063129 : Nat := 118140960795 + 4063129 * 2 ^ 59
def prefixEnd_4063129 : Nat := 4983230072969 + 3 ^ 40 * 4063129 * 2
def baseEnd_4063129 : Nat := 1390892092148092481867677

theorem tailTrace_4063129 : CollatzResearch.WordTrace tailWord_4063129 prefixEnd_4063129 1390892092148092481867677 := by
  unfold tailWord_4063129
  simp only [CollatzResearch.WordTrace]
  refine ⟨148194489296985035031944441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98796326197990023354629627 148194489296985035031944441)
  ·
    refine ⟨111145866972738776273958331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148194489296985035031944441 111145866972738776273958331)
    ·
      refine ⟨166718800459108164410937497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111145866972738776273958331 166718800459108164410937497)
      ·
        refine ⟨125039100344331123308203123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166718800459108164410937497 125039100344331123308203123)
        ·
          refine ⟨187558650516496684962304685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125039100344331123308203123 187558650516496684962304685)
          ·
            refine ⟨70334493943686256860864257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187558650516496684962304685 70334493943686256860864257)
            ·
              refine ⟨52750870457764692645648193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 70334493943686256860864257 52750870457764692645648193)
              ·
                refine ⟨39563152843323519484236145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52750870457764692645648193 39563152843323519484236145)
                ·
                  refine ⟨29672364632492639613177109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39563152843323519484236145 29672364632492639613177109)
                  ·
                    refine ⟨1390892092148092481867677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29672364632492639613177109 1390892092148092481867677)
                    ·
                      rfl

theorem cell22_4063129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 6].length) (baseStart_4063129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063129 prefixEnd_4063129 := by exact prefixLift 4063129
  have htrace : WordTrace (prefixWord ++ tailWord_4063129) baseStart_4063129 baseEnd_4063129 := by
    simpa [prefixWord, tailWord_4063129, baseEnd_4063129] using wordTrace_append hprefix tailTrace_4063129
  have hstable : (prefixWord ++ tailWord_4063129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063129).length < 2 ^ (prefixWord ++ tailWord_4063129).sum := by decide
  have hdescent : baseEnd_4063129 < baseStart_4063129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063133 : List Nat := [1, 4, 2, 1, 2, 4, 2, 6]
def baseStart_4063133 : Nat := 118140960795 + 4063133 * 2 ^ 59
def prefixEnd_4063133 : Nat := 4983230072969 + 3 ^ 40 * 4063133 * 2
def baseEnd_4063133 : Nat := 154543717936648644974185

theorem tailTrace_4063133 : CollatzResearch.WordTrace tailWord_4063133 prefixEnd_4063133 154543717936648644974185 := by
  unfold tailWord_4063133
  simp only [CollatzResearch.WordTrace]
  refine ⟨148194635188970543715090053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98796423459313695810060035 148194635188970543715090053)
  ·
    refine ⟨27786494097931976946579385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148194635188970543715090053 27786494097931976946579385)
    ·
      refine ⟨20839870573448982709934539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27786494097931976946579385 20839870573448982709934539)
      ·
        refine ⟨31259805860173474064901809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20839870573448982709934539 31259805860173474064901809)
        ·
          refine ⟨23444854395130105548676357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31259805860173474064901809 23444854395130105548676357)
          ·
            refine ⟨4395910199086894790376817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23444854395130105548676357 4395910199086894790376817)
            ·
              refine ⟨3296932649315171092782613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4395910199086894790376817 3296932649315171092782613)
              ·
                refine ⟨154543717936648644974185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3296932649315171092782613 154543717936648644974185)
                ·
                  rfl

theorem cell22_4063133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 6].length) (baseStart_4063133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063133 prefixEnd_4063133 := by exact prefixLift 4063133
  have htrace : WordTrace (prefixWord ++ tailWord_4063133) baseStart_4063133 baseEnd_4063133 := by
    simpa [prefixWord, tailWord_4063133, baseEnd_4063133] using wordTrace_append hprefix tailTrace_4063133
  have hstable : (prefixWord ++ tailWord_4063133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063133).length < 2 ^ (prefixWord ++ tailWord_4063133).sum := by decide
  have hdescent : baseEnd_4063133 < baseStart_4063133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063161 : List Nat := [1, 2, 1, 4, 2, 1, 2, 4, 5]
def baseStart_4063161 : Nat := 118140960795 + 4063161 * 2 ^ 59
def prefixEnd_4063161 : Nat := 4983230072969 + 3 ^ 40 * 4063161 * 2
def baseEnd_4063161 : Nat := 463634348800685021689193

theorem tailTrace_4063161 : CollatzResearch.WordTrace tailWord_4063161 prefixEnd_4063161 463634348800685021689193 := by
  unfold tailWord_4063161
  simp only [CollatzResearch.WordTrace]
  refine ⟨148195656432869104497109337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98797104288579402998072891 148195656432869104497109337)
  ·
    refine ⟨111146742324651828372832003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148195656432869104497109337 111146742324651828372832003)
    ·
      refine ⟨166720113486977742559248005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111146742324651828372832003 166720113486977742559248005)
      ·
        refine ⟨31260021278808326729859001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166720113486977742559248005 31260021278808326729859001)
        ·
          refine ⟨23445015959106245047394251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31260021278808326729859001 23445015959106245047394251)
          ·
            refine ⟨35167523938659367571091377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23445015959106245047394251 35167523938659367571091377)
            ·
              refine ⟨26375642953994525678318533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35167523938659367571091377 26375642953994525678318533)
              ·
                refine ⟨4945433053873973564684725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26375642953994525678318533 4945433053873973564684725)
                ·
                  refine ⟨463634348800685021689193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4945433053873973564684725 463634348800685021689193)
                  ·
                    rfl

theorem cell22_4063161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 5].length) (baseStart_4063161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063161 prefixEnd_4063161 := by exact prefixLift 4063161
  have htrace : WordTrace (prefixWord ++ tailWord_4063161) baseStart_4063161 baseEnd_4063161 := by
    simpa [prefixWord, tailWord_4063161, baseEnd_4063161] using wordTrace_append hprefix tailTrace_4063161
  have hstable : (prefixWord ++ tailWord_4063161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063161).length < 2 ^ (prefixWord ++ tailWord_4063161).sum := by decide
  have hdescent : baseEnd_4063161 < baseStart_4063161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063165 : List Nat := [1, 4, 1, 2, 3, 3, 1, 1, 3, 3]
def baseStart_4063165 : Nat := 118140960795 + 4063165 * 2 ^ 59
def prefixEnd_4063165 : Nat := 4983230072969 + 3 ^ 40 * 4063165 * 2
def baseEnd_4063165 : Nat := 1390904415683800387967567

theorem tailTrace_4063165 : CollatzResearch.WordTrace tailWord_4063165 prefixEnd_4063165 1390904415683800387967567 := by
  unfold tailWord_4063165
  simp only [CollatzResearch.WordTrace]
  refine ⟨148195802324854613180254949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98797201549903075453503299 148195802324854613180254949)
  ·
    refine ⟨27786712935910239971297803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148195802324854613180254949 27786712935910239971297803)
    ·
      refine ⟨41680069403865359956946705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27786712935910239971297803 41680069403865359956946705)
      ·
        refine ⟨31260052052899019967710029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41680069403865359956946705 31260052052899019967710029)
        ·
          refine ⟨11722519519837132487891261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31260052052899019967710029 11722519519837132487891261)
          ·
            refine ⟨4395944819938924682959223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11722519519837132487891261 4395944819938924682959223)
            ·
              refine ⟨6593917229908387024438835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4395944819938924682959223 6593917229908387024438835)
              ·
                refine ⟨9890875844862580536658253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6593917229908387024438835 9890875844862580536658253)
                ·
                  refine ⟨3709078441823467701246845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9890875844862580536658253 3709078441823467701246845)
                  ·
                    refine ⟨1390904415683800387967567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3709078441823467701246845 1390904415683800387967567)
                    ·
                      rfl

theorem cell22_4063165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 3, 3].length) (baseStart_4063165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063165 prefixEnd_4063165 := by exact prefixLift 4063165
  have htrace : WordTrace (prefixWord ++ tailWord_4063165) baseStart_4063165 baseEnd_4063165 := by
    simpa [prefixWord, tailWord_4063165, baseEnd_4063165] using wordTrace_append hprefix tailTrace_4063165
  have hstable : (prefixWord ++ tailWord_4063165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063165).length < 2 ^ (prefixWord ++ tailWord_4063165).sum := by decide
  have hdescent : baseEnd_4063165 < baseStart_4063165 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063178 : List Nat := [3, 1, 2, 1, 2, 1, 6, 1, 5]
def baseStart_4063178 : Nat := 118140960795 + 4063178 * 2 ^ 59
def prefixEnd_4063178 : Nat := 4983230072969 + 3 ^ 40 * 4063178 * 2
def baseEnd_4063178 : Nat := 463636288616490895797509

theorem tailTrace_4063178 : CollatzResearch.WordTrace tailWord_4063178 prefixEnd_4063178 463636288616490895797509 := by
  unfold tailWord_4063178
  simp only [CollatzResearch.WordTrace]
  refine ⟨37049069118451879100119547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98797517649205010933652125 37049069118451879100119547)
  ·
    refine ⟨55573603677677818650179321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37049069118451879100119547 55573603677677818650179321)
    ·
      refine ⟨41680202758258363987634491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55573603677677818650179321 41680202758258363987634491)
      ·
        refine ⟨62520304137387545981451737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41680202758258363987634491 62520304137387545981451737)
        ·
          refine ⟨46890228103040659486088803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62520304137387545981451737 46890228103040659486088803)
          ·
            refine ⟨70335342154560989229133205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46890228103040659486088803 70335342154560989229133205)
            ·
              refine ⟨3296969163495046370115619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 70335342154560989229133205 3296969163495046370115619)
              ·
                refine ⟨4945453745242569555173429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3296969163495046370115619 4945453745242569555173429)
                ·
                  refine ⟨463636288616490895797509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4945453745242569555173429 463636288616490895797509)
                  ·
                    rfl

theorem cell22_4063178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 5].length) (baseStart_4063178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063178 prefixEnd_4063178 := by exact prefixLift 4063178
  have htrace : WordTrace (prefixWord ++ tailWord_4063178) baseStart_4063178 baseEnd_4063178 := by
    simpa [prefixWord, tailWord_4063178, baseEnd_4063178] using wordTrace_append hprefix tailTrace_4063178
  have hstable : (prefixWord ++ tailWord_4063178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063178).length < 2 ^ (prefixWord ++ tailWord_4063178).sum := by decide
  have hdescent : baseEnd_4063178 < baseStart_4063178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063191 : List Nat := [1, 1, 3, 2, 1, 1, 5, 1, 3, 4]
def baseStart_4063191 : Nat := 118140960795 + 4063191 * 2 ^ 59
def prefixEnd_4063191 : Nat := 4983230072969 + 3 ^ 40 * 4063191 * 2
def baseEnd_4063191 : Nat := 1390913316015144986817487

theorem tailTrace_4063191 : CollatzResearch.WordTrace tailWord_4063191 prefixEnd_4063191 1390913316015144986817487 := by
  unfold tailWord_4063191
  simp only [CollatzResearch.WordTrace]
  refine ⟨148196750622760419620701427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98797833748506946413800951 148196750622760419620701427)
  ·
    refine ⟨222295125934140629431052141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148196750622760419620701427 222295125934140629431052141)
    ·
      refine ⟨83360672225302736036644553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222295125934140629431052141 83360672225302736036644553)
      ·
        refine ⟨62520504168977052027483415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83360672225302736036644553 62520504168977052027483415)
        ·
          refine ⟨93780756253465578041225123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62520504168977052027483415 93780756253465578041225123)
          ·
            refine ⟨140671134380198367061837685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93780756253465578041225123 140671134380198367061837685)
            ·
              refine ⟨13187918848143596912047283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 140671134380198367061837685 13187918848143596912047283)
              ·
                refine ⟨19781878272215395368070925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13187918848143596912047283 19781878272215395368070925)
                ·
                  refine ⟨7418204352080773263026597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19781878272215395368070925 7418204352080773263026597)
                  ·
                    refine ⟨1390913316015144986817487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7418204352080773263026597 1390913316015144986817487)
                    ·
                      rfl

theorem cell22_4063191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_4063191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063191 prefixEnd_4063191 := by exact prefixLift 4063191
  have htrace : WordTrace (prefixWord ++ tailWord_4063191) baseStart_4063191 baseEnd_4063191 := by
    simpa [prefixWord, tailWord_4063191, baseEnd_4063191] using wordTrace_append hprefix tailTrace_4063191
  have hstable : (prefixWord ++ tailWord_4063191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063191).length < 2 ^ (prefixWord ++ tailWord_4063191).sum := by decide
  have hdescent : baseEnd_4063191 < baseStart_4063191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063253 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 1, 6]
def baseStart_4063253 : Nat := 118140960795 + 4063253 * 2 ^ 59
def prefixEnd_4063253 : Nat := 4983230072969 + 3 ^ 40 * 4063253 * 2
def baseEnd_4063253 : Nat := 1390934539882197491767297

theorem tailTrace_4063253 : CollatzResearch.WordTrace tailWord_4063253 prefixEnd_4063253 1390934539882197491767297 := by
  unfold tailWord_4063253
  simp only [CollatzResearch.WordTrace]
  refine ⟨148199011948535804209458413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98799341299023869472972275 148199011948535804209458413)
  ·
    refine ⟨55574629480700926578546905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148199011948535804209458413 55574629480700926578546905)
    ·
      refine ⟨41680972110525694933910179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55574629480700926578546905 41680972110525694933910179)
      ·
        refine ⟨62521458165788542400865269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41680972110525694933910179 62521458165788542400865269)
        ·
          refine ⟨5861386703042675850081119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 62521458165788542400865269 5861386703042675850081119)
          ·
            refine ⟨8792080054564013775121679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5861386703042675850081119 8792080054564013775121679)
            ·
              refine ⟨13188120081846020662682519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8792080054564013775121679 13188120081846020662682519)
              ·
                refine ⟨19782180122769030994023779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13188120081846020662682519 19782180122769030994023779)
                ·
                  refine ⟨29673270184153546491035669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19782180122769030994023779 29673270184153546491035669)
                  ·
                    refine ⟨1390934539882197491767297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29673270184153546491035669 1390934539882197491767297)
                    ·
                      rfl

theorem cell22_4063253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_4063253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063253 prefixEnd_4063253 := by exact prefixLift 4063253
  have htrace : WordTrace (prefixWord ++ tailWord_4063253) baseStart_4063253 baseEnd_4063253 := by
    simpa [prefixWord, tailWord_4063253, baseEnd_4063253] using wordTrace_append hprefix tailTrace_4063253
  have hstable : (prefixWord ++ tailWord_4063253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063253).length < 2 ^ (prefixWord ++ tailWord_4063253).sum := by decide
  have hdescent : baseEnd_4063253 < baseStart_4063253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063268 : List Nat := [2, 3, 1, 4, 2, 1, 9]
def baseStart_4063268 : Nat := 118140960795 + 4063268 * 2 ^ 59
def prefixEnd_4063268 : Nat := 4983230072969 + 3 ^ 40 * 4063268 * 2
def baseEnd_4063268 : Nat := 51516284247731201949713

theorem tailTrace_4063268 : CollatzResearch.WordTrace tailWord_4063268 prefixEnd_4063268 51516284247731201949713 := by
  unfold tailWord_4063268
  simp only [CollatzResearch.WordTrace]
  refine ⟨74099779521740730885627229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98799706028987641180836305 74099779521740730885627229)
  ·
    refine ⟨27787417320652774082110211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74099779521740730885627229 27787417320652774082110211)
    ·
      refine ⟨41681125980979161123165317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27787417320652774082110211 41681125980979161123165317)
      ·
        refine ⟨7815211121433592710593497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41681125980979161123165317 7815211121433592710593497)
        ·
          refine ⟨5861408341075194532945123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7815211121433592710593497 5861408341075194532945123)
          ·
            refine ⟨8792112511612791799417685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5861408341075194532945123 8792112511612791799417685)
            ·
              refine ⟨51516284247731201949713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8792112511612791799417685 51516284247731201949713)
              ·
                rfl

theorem cell22_4063268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 9].length) (baseStart_4063268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063268 prefixEnd_4063268 := by exact prefixLift 4063268
  have htrace : WordTrace (prefixWord ++ tailWord_4063268) baseStart_4063268 baseEnd_4063268 := by
    simpa [prefixWord, tailWord_4063268, baseEnd_4063268] using wordTrace_append hprefix tailTrace_4063268
  have hstable : (prefixWord ++ tailWord_4063268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063268).length < 2 ^ (prefixWord ++ tailWord_4063268).sum := by decide
  have hdescent : baseEnd_4063268 < baseStart_4063268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063272 : List Nat := [2, 1, 5, 3, 1, 1, 1, 1, 4, 3]
def baseStart_4063272 : Nat := 118140960795 + 4063272 * 2 ^ 59
def prefixEnd_4063272 : Nat := 4983230072969 + 3 ^ 40 * 4063272 * 2
def baseEnd_4063272 : Nat := 1390941043970487775542239

theorem tailTrace_4063272 : CollatzResearch.WordTrace tailWord_4063272 prefixEnd_4063272 1390941043970487775542239 := by
  unfold tailWord_4063272
  simp only [CollatzResearch.WordTrace]
  refine ⟨74099852467733485227200035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98799803290311313636266713 74099852467733485227200035)
  ·
    refine ⟨111149778701600227840800053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74099852467733485227200035 111149778701600227840800053)
    ·
      refine ⟨10420291753275021360075005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111149778701600227840800053 10420291753275021360075005)
      ·
        refine ⟨3907609407478133010028127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10420291753275021360075005 3907609407478133010028127)
        ·
          refine ⟨5861414111217199515042191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3907609407478133010028127 5861414111217199515042191)
          ·
            refine ⟨8792121166825799272563287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5861414111217199515042191 8792121166825799272563287)
            ·
              refine ⟨13188181750238698908844931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8792121166825799272563287 13188181750238698908844931)
              ·
                refine ⟨19782272625358048363267397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13188181750238698908844931 19782272625358048363267397)
                ·
                  refine ⟨3709176117254634068112637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19782272625358048363267397 3709176117254634068112637)
                  ·
                    refine ⟨1390941043970487775542239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3709176117254634068112637 1390941043970487775542239)
                    ·
                      rfl

theorem cell22_4063272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_4063272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063272 prefixEnd_4063272 := by exact prefixLift 4063272
  have htrace : WordTrace (prefixWord ++ tailWord_4063272) baseStart_4063272 baseEnd_4063272 := by
    simpa [prefixWord, tailWord_4063272, baseEnd_4063272] using wordTrace_append hprefix tailTrace_4063272
  have hstable : (prefixWord ++ tailWord_4063272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063272).length < 2 ^ (prefixWord ++ tailWord_4063272).sum := by decide
  have hdescent : baseEnd_4063272 < baseStart_4063272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063283 : List Nat := [1, 1, 1, 2, 4, 1, 3, 3, 3, 3]
def baseStart_4063283 : Nat := 118140960795 + 4063283 * 2 ^ 59
def prefixEnd_4063283 : Nat := 4983230072969 + 3 ^ 40 * 4063283 * 2
def baseEnd_4063283 : Nat := 1390944809495287413517205

theorem tailTrace_4063283 : CollatzResearch.WordTrace tailWord_4063283 prefixEnd_4063283 1390944809495287413517205 := by
  unfold tailWord_4063283
  simp only [CollatzResearch.WordTrace]
  refine ⟨148200106138427119333050503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98800070758951412888700335 148200106138427119333050503)
  ·
    refine ⟨222300159207640678999575755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148200106138427119333050503 222300159207640678999575755)
    ·
      refine ⟨333450238811461018499363633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222300159207640678999575755 333450238811461018499363633)
      ·
        refine ⟨250087679108595763874522725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333450238811461018499363633 250087679108595763874522725)
        ·
          refine ⟨46891439832861705726473011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 250087679108595763874522725 46891439832861705726473011)
          ·
            refine ⟨70337159749292558589709517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46891439832861705726473011 70337159749292558589709517)
            ·
              refine ⟨26376434905984709471141069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70337159749292558589709517 26376434905984709471141069)
              ·
                refine ⟨9891163089744266051677901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26376434905984709471141069 9891163089744266051677901)
                ·
                  refine ⟨3709186158654099769379213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9891163089744266051677901 3709186158654099769379213)
                  ·
                    refine ⟨1390944809495287413517205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3709186158654099769379213 1390944809495287413517205)
                    ·
                      rfl

theorem cell22_4063283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 3, 3, 3].length) (baseStart_4063283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063283 prefixEnd_4063283 := by exact prefixLift 4063283
  have htrace : WordTrace (prefixWord ++ tailWord_4063283) baseStart_4063283 baseEnd_4063283 := by
    simpa [prefixWord, tailWord_4063283, baseEnd_4063283] using wordTrace_append hprefix tailTrace_4063283
  have hstable : (prefixWord ++ tailWord_4063283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063283).length < 2 ^ (prefixWord ++ tailWord_4063283).sum := by decide
  have hdescent : baseEnd_4063283 < baseStart_4063283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063317 : List Nat := [1, 3, 2, 2, 1, 3, 3, 3, 1, 3]
def baseStart_4063317 : Nat := 118140960795 + 4063317 * 2 ^ 59
def prefixEnd_4063317 : Nat := 4983230072969 + 3 ^ 40 * 4063317 * 2
def baseEnd_4063317 : Nat := 1390956448390122658167101

theorem tailTrace_4063317 : CollatzResearch.WordTrace tailWord_4063317 prefixEnd_4063317 1390956448390122658167101 := by
  unfold tailWord_4063317
  simp only [CollatzResearch.WordTrace]
  refine ⟨148201346220303943139788205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98800897480202628759858803 148201346220303943139788205)
  ·
    refine ⟨55575504832613978677420577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148201346220303943139788205 55575504832613978677420577)
    ·
      refine ⟨41681628624460484008065433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55575504832613978677420577 41681628624460484008065433)
      ·
        refine ⟨31261221468345363006049075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41681628624460484008065433 31261221468345363006049075)
        ·
          refine ⟨46891832202518044509073613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31261221468345363006049075 46891832202518044509073613)
          ·
            refine ⟨17584437075944266690902605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46891832202518044509073613 17584437075944266690902605)
            ·
              refine ⟨6594163903479100009088477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17584437075944266690902605 6594163903479100009088477)
              ·
                refine ⟨2472811463804662503408179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6594163903479100009088477 2472811463804662503408179)
                ·
                  refine ⟨3709217195706993755112269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2472811463804662503408179 3709217195706993755112269)
                  ·
                    refine ⟨1390956448390122658167101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3709217195706993755112269 1390956448390122658167101)
                    ·
                      rfl

theorem cell22_4063317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_4063317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063317 prefixEnd_4063317 := by exact prefixLift 4063317
  have htrace : WordTrace (prefixWord ++ tailWord_4063317) baseStart_4063317 baseEnd_4063317 := by
    simpa [prefixWord, tailWord_4063317, baseEnd_4063317] using wordTrace_append hprefix tailTrace_4063317
  have hstable : (prefixWord ++ tailWord_4063317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063317).length < 2 ^ (prefixWord ++ tailWord_4063317).sum := by decide
  have hdescent : baseEnd_4063317 < baseStart_4063317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063392 : List Nat := [2, 1, 1, 4, 2, 2, 4, 2, 4]
def baseStart_4063392 : Nat := 118140960795 + 4063392 * 2 ^ 59
def prefixEnd_4063392 : Nat := 4983230072969 + 3 ^ 40 * 4063392 * 2
def baseEnd_4063392 : Nat := 463660707474282487513957

theorem tailTrace_4063392 : CollatzResearch.WordTrace tailWord_4063392 prefixEnd_4063392 463660707474282487513957 := by
  unfold tailWord_4063392
  simp only [CollatzResearch.WordTrace]
  refine ⟨74102040847516115474384215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98802721130021487299178953 74102040847516115474384215)
  ·
    refine ⟨111153061271274173211576323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74102040847516115474384215 111153061271274173211576323)
    ·
      refine ⟨166729591906911259817364485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111153061271274173211576323 166729591906911259817364485)
      ·
        refine ⟨31261798482545861215755841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166729591906911259817364485 31261798482545861215755841)
        ·
          refine ⟨23446348861909395911816881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31261798482545861215755841 23446348861909395911816881)
          ·
            refine ⟨17584761646432046933862661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23446348861909395911816881 17584761646432046933862661)
            ·
              refine ⟨3297142808706008800099249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17584761646432046933862661 3297142808706008800099249)
              ·
                refine ⟨2472857106529506600074437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3297142808706008800099249 2472857106529506600074437)
                ·
                  refine ⟨463660707474282487513957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2472857106529506600074437 463660707474282487513957)
                  ·
                    rfl

theorem cell22_4063392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 4].length) (baseStart_4063392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063392 prefixEnd_4063392 := by exact prefixLift 4063392
  have htrace : WordTrace (prefixWord ++ tailWord_4063392) baseStart_4063392 baseEnd_4063392 := by
    simpa [prefixWord, tailWord_4063392, baseEnd_4063392] using wordTrace_append hprefix tailTrace_4063392
  have hstable : (prefixWord ++ tailWord_4063392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063392).length < 2 ^ (prefixWord ++ tailWord_4063392).sum := by decide
  have hdescent : baseEnd_4063392 < baseStart_4063392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063426 : List Nat := [3, 5, 1, 1, 1, 2, 2, 3, 4]
def baseStart_4063426 : Nat := 118140960795 + 4063426 * 2 ^ 59
def prefixEnd_4063426 : Nat := 4983230072969 + 3 ^ 40 * 4063426 * 2
def baseEnd_4063426 : Nat := 463664587105894235730589

theorem tailTrace_4063426 : CollatzResearch.WordTrace tailWord_4063426 prefixEnd_4063426 463664587105894235730589 := by
  unfold tailWord_4063426
  simp only [CollatzResearch.WordTrace]
  refine ⟨37051330444227263688876533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98803547851272703170337421 37051330444227263688876533)
  ·
    refine ⟨3473562229146305970832175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 37051330444227263688876533 3473562229146305970832175)
    ·
      refine ⟨5210343343719458956248263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3473562229146305970832175 5210343343719458956248263)
      ·
        refine ⟨7815515015579188434372395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5210343343719458956248263 7815515015579188434372395)
        ·
          refine ⟨11723272523368782651558593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7815515015579188434372395 11723272523368782651558593)
          ·
            refine ⟨8792454392526586988668945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11723272523368782651558593 8792454392526586988668945)
            ·
              refine ⟨6594340794394940241501709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8792454392526586988668945 6594340794394940241501709)
              ·
                refine ⟨2472877797898102590563141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6594340794394940241501709 2472877797898102590563141)
                ·
                  refine ⟨463664587105894235730589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2472877797898102590563141 463664587105894235730589)
                  ·
                    rfl

theorem cell22_4063426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_4063426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063426 prefixEnd_4063426 := by exact prefixLift 4063426
  have htrace : WordTrace (prefixWord ++ tailWord_4063426) baseStart_4063426 baseEnd_4063426 := by
    simpa [prefixWord, tailWord_4063426, baseEnd_4063426] using wordTrace_append hprefix tailTrace_4063426
  have hstable : (prefixWord ++ tailWord_4063426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063426).length < 2 ^ (prefixWord ++ tailWord_4063426).sum := by decide
  have hdescent : baseEnd_4063426 < baseStart_4063426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063458 : List Nat := [3, 3, 4, 1, 2, 1, 1, 1, 1, 5]
def baseStart_4063458 : Nat := 118140960795 + 4063458 * 2 ^ 59
def prefixEnd_4063458 : Nat := 4983230072969 + 3 ^ 40 * 4063458 * 2
def baseEnd_4063458 : Nat := 1391004715571645290391669

theorem tailTrace_4063458 : CollatzResearch.WordTrace tailWord_4063458 prefixEnd_4063458 1391004715571645290391669 := by
  unfold tailWord_4063458
  simp only [CollatzResearch.WordTrace]
  refine ⟨37051622228198281055167757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98804325941862082813780685 37051622228198281055167757)
  ·
    refine ⟨13894358335574355395687909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37051622228198281055167757 13894358335574355395687909)
    ·
      refine ⟨2605192187920191636691483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13894358335574355395687909 2605192187920191636691483)
      ·
        refine ⟨3907788281880287455037225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2605192187920191636691483 3907788281880287455037225)
        ·
          refine ⟨2930841211410215591277919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3907788281880287455037225 2930841211410215591277919)
          ·
            refine ⟨4396261817115323386916879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2930841211410215591277919 4396261817115323386916879)
            ·
              refine ⟨6594392725672985080375319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4396261817115323386916879 6594392725672985080375319)
              ·
                refine ⟨9891589088509477620562979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6594392725672985080375319 9891589088509477620562979)
                ·
                  refine ⟨14837383632764216430844469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9891589088509477620562979 14837383632764216430844469)
                  ·
                    refine ⟨1391004715571645290391669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14837383632764216430844469 1391004715571645290391669)
                    ·
                      rfl

theorem cell22_4063458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_4063458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063458 prefixEnd_4063458 := by exact prefixLift 4063458
  have htrace : WordTrace (prefixWord ++ tailWord_4063458) baseStart_4063458 baseEnd_4063458 := by
    simpa [prefixWord, tailWord_4063458, baseEnd_4063458] using wordTrace_append hprefix tailTrace_4063458
  have hstable : (prefixWord ++ tailWord_4063458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063458).length < 2 ^ (prefixWord ++ tailWord_4063458).sum := by decide
  have hdescent : baseEnd_4063458 < baseStart_4063458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063572 : List Nat := [2, 4, 1, 1, 2, 4, 1, 7]
def baseStart_4063572 : Nat := 118140960795 + 4063572 * 2 ^ 59
def prefixEnd_4063572 : Nat := 4983230072969 + 3 ^ 40 * 4063572 * 2
def baseEnd_4063572 : Nat := 154560415566820777004591

theorem tailTrace_4063572 : CollatzResearch.WordTrace tailWord_4063572 prefixEnd_4063572 154560415566820777004591 := by
  unfold tailWord_4063572
  simp only [CollatzResearch.WordTrace]
  refine ⟨74105323417190060845160485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98807097889586747793547313 74105323417190060845160485)
  ·
    refine ⟨13894748140723136408467591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74105323417190060845160485 13894748140723136408467591)
    ·
      refine ⟨20842122211084704612701387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13894748140723136408467591 20842122211084704612701387)
      ·
        refine ⟨31263183316627056919052081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20842122211084704612701387 31263183316627056919052081)
        ·
          refine ⟨23447387487470292689289061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31263183316627056919052081 23447387487470292689289061)
          ·
            refine ⟨4396385153900679879241699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23447387487470292689289061 4396385153900679879241699)
            ·
              refine ⟨6594577730851019818862549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4396385153900679879241699 6594577730851019818862549)
              ·
                refine ⟨154560415566820777004591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6594577730851019818862549 154560415566820777004591)
                ·
                  rfl

theorem cell22_4063572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 7].length) (baseStart_4063572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063572 prefixEnd_4063572 := by exact prefixLift 4063572
  have htrace : WordTrace (prefixWord ++ tailWord_4063572) baseStart_4063572 baseEnd_4063572 := by
    simpa [prefixWord, tailWord_4063572, baseEnd_4063572] using wordTrace_append hprefix tailTrace_4063572
  have hstable : (prefixWord ++ tailWord_4063572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063572).length < 2 ^ (prefixWord ++ tailWord_4063572).sum := by decide
  have hdescent : baseEnd_4063572 < baseStart_4063572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063587 : List Nat := [1, 1, 1, 5, 2, 1, 3, 2, 3, 3]
def baseStart_4063587 : Nat := 118140960795 + 4063587 * 2 ^ 59
def prefixEnd_4063587 : Nat := 4983230072969 + 3 ^ 40 * 4063587 * 2
def baseEnd_4063587 : Nat := 1391048874907931953916273

theorem tailTrace_4063587 : CollatzResearch.WordTrace tailWord_4063587 prefixEnd_4063587 1391048874907931953916273 := by
  unfold tailWord_4063587
  simp only [CollatzResearch.WordTrace]
  refine ⟨148211193929325779252117015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98807462619550519501411343 148211193929325779252117015)
  ·
    refine ⟨222316790893988668878175523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148211193929325779252117015 222316790893988668878175523)
    ·
      refine ⟨333475186340983003317263285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222316790893988668878175523 333475186340983003317263285)
      ·
        refine ⟨31263298719467156560993433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 333475186340983003317263285 31263298719467156560993433)
        ·
          refine ⟨23447474039600367420745075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31263298719467156560993433 23447474039600367420745075)
          ·
            refine ⟨35171211059400551131117613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23447474039600367420745075 35171211059400551131117613)
            ·
              refine ⟨13189204147275206674169105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35171211059400551131117613 13189204147275206674169105)
              ·
                refine ⟨9891903110456405005626829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13189204147275206674169105 9891903110456405005626829)
                ·
                  refine ⟨3709463666421151877110061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9891903110456405005626829 3709463666421151877110061)
                  ·
                    refine ⟨1391048874907931953916273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3709463666421151877110061 1391048874907931953916273)
                    ·
                      rfl

theorem cell22_4063587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 2, 3, 3].length) (baseStart_4063587 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063587 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063587 prefixEnd_4063587 := by exact prefixLift 4063587
  have htrace : WordTrace (prefixWord ++ tailWord_4063587) baseStart_4063587 baseEnd_4063587 := by
    simpa [prefixWord, tailWord_4063587, baseEnd_4063587] using wordTrace_append hprefix tailTrace_4063587
  have hstable : (prefixWord ++ tailWord_4063587).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063587).length < 2 ^ (prefixWord ++ tailWord_4063587).sum := by decide
  have hdescent : baseEnd_4063587 < baseStart_4063587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063617 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 7]
def baseStart_4063617 : Nat := 118140960795 + 4063617 * 2 ^ 59
def prefixEnd_4063617 : Nat := 4983230072969 + 3 ^ 40 * 4063617 * 2
def baseEnd_4063617 : Nat := 463686381507007291888727

theorem tailTrace_4063617 : CollatzResearch.WordTrace tailWord_4063617 prefixEnd_4063617 463686381507007291888727 := by
  unfold tailWord_4063617
  simp only [CollatzResearch.WordTrace]
  refine ⟨148212288119217094375709105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98808192079478062917139403 148212288119217094375709105)
  ·
    refine ⟨111159216089412820781781829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148212288119217094375709105 111159216089412820781781829)
    ·
      refine ⟨20842353016764903896584093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111159216089412820781781829 20842353016764903896584093)
      ·
        refine ⟨7815882381286838961219035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20842353016764903896584093 7815882381286838961219035)
        ·
          refine ⟨11723823571930258441828553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7815882381286838961219035 11723823571930258441828553)
          ·
            refine ⟨8792867678947693831371415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11723823571930258441828553 8792867678947693831371415)
            ·
              refine ⟨13189301518421540747057123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8792867678947693831371415 13189301518421540747057123)
              ·
                refine ⟨19783952277632311120585685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13189301518421540747057123 19783952277632311120585685)
                ·
                  refine ⟨463686381507007291888727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19783952277632311120585685 463686381507007291888727)
                  ·
                    rfl

theorem cell22_4063617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 7].length) (baseStart_4063617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063617 prefixEnd_4063617 := by exact prefixLift 4063617
  have htrace : WordTrace (prefixWord ++ tailWord_4063617) baseStart_4063617 baseEnd_4063617 := by
    simpa [prefixWord, tailWord_4063617, baseEnd_4063617] using wordTrace_append hprefix tailTrace_4063617
  have hstable : (prefixWord ++ tailWord_4063617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063617).length < 2 ^ (prefixWord ++ tailWord_4063617).sum := by decide
  have hdescent : baseEnd_4063617 < baseStart_4063617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063660 : List Nat := [2, 2, 1, 1, 1, 1, 3, 3, 3, 5]
def baseStart_4063660 : Nat := 118140960795 + 4063660 * 2 ^ 59
def prefixEnd_4063660 : Nat := 4983230072969 + 3 ^ 40 * 4063660 * 2
def baseEnd_4063660 : Nat := 1391073864299784096841049

theorem tailTrace_4063660 : CollatzResearch.WordTrace tailWord_4063660 prefixEnd_4063660 1391073864299784096841049 := by
  unfold tailWord_4063660
  simp only [CollatzResearch.WordTrace]
  refine ⟨74106928229030656359762217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98809237638707541813016289 74106928229030656359762217)
  ·
    refine ⟨55580196171772992269821663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74106928229030656359762217 55580196171772992269821663)
    ·
      refine ⟨83370294257659488404732495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55580196171772992269821663 83370294257659488404732495)
      ·
        refine ⟨125055441386489232607098743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83370294257659488404732495 125055441386489232607098743)
        ·
          refine ⟨187583162079733848910648115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125055441386489232607098743 187583162079733848910648115)
          ·
            refine ⟨281374743119600773365972173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187583162079733848910648115 281374743119600773365972173)
            ·
              refine ⟨105515528669850290012239565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281374743119600773365972173 105515528669850290012239565)
              ·
                refine ⟨39568323251193858754589837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105515528669850290012239565 39568323251193858754589837)
                ·
                  refine ⟨14838121219197697032971189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39568323251193858754589837 14838121219197697032971189)
                  ·
                    refine ⟨1391073864299784096841049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14838121219197697032971189 1391073864299784096841049)
                    ·
                      rfl

theorem cell22_4063660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_4063660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063660 prefixEnd_4063660 := by exact prefixLift 4063660
  have htrace : WordTrace (prefixWord ++ tailWord_4063660) baseStart_4063660 baseEnd_4063660 := by
    simpa [prefixWord, tailWord_4063660, baseEnd_4063660] using wordTrace_append hprefix tailTrace_4063660
  have hstable : (prefixWord ++ tailWord_4063660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063660).length < 2 ^ (prefixWord ++ tailWord_4063660).sum := by decide
  have hdescent : baseEnd_4063660 < baseStart_4063660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063698 : List Nat := [3, 2, 2, 4, 1, 2, 1, 2, 1, 4]
def baseStart_4063698 : Nat := 118140960795 + 4063698 * 2 ^ 59
def prefixEnd_4063698 : Nat := 4983230072969 + 3 ^ 40 * 4063698 * 2
def baseEnd_4063698 : Nat := 1391086872476364664390933

theorem tailTrace_4063698 : CollatzResearch.WordTrace tailWord_4063698 prefixEnd_4063698 1391086872476364664390933 := by
  unfold tailWord_4063698
  simp only [CollatzResearch.WordTrace]
  refine ⟨37053810607980911302351937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98810161621282430139605165 37053810607980911302351937)
  ·
    refine ⟨27790357955985683476763953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37053810607980911302351937 27790357955985683476763953)
    ·
      refine ⟨20842768466989262607572965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27790357955985683476763953 20842768466989262607572965)
      ·
        refine ⟨3908019087560486738919931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20842768466989262607572965 3908019087560486738919931)
        ·
          refine ⟨5862028631340730108379897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3908019087560486738919931 5862028631340730108379897)
          ·
            refine ⟨4396521473505547581284923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5862028631340730108379897 4396521473505547581284923)
            ·
              refine ⟨6594782210258321371927385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4396521473505547581284923 6594782210258321371927385)
              ·
                refine ⟨4946086657693741028945539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6594782210258321371927385 4946086657693741028945539)
                ·
                  refine ⟨7419129986540611543418309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4946086657693741028945539 7419129986540611543418309)
                  ·
                    refine ⟨1391086872476364664390933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7419129986540611543418309 1391086872476364664390933)
                    ·
                      rfl

theorem cell22_4063698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_4063698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063698 prefixEnd_4063698 := by exact prefixLift 4063698
  have htrace : WordTrace (prefixWord ++ tailWord_4063698) baseStart_4063698 baseEnd_4063698 := by
    simpa [prefixWord, tailWord_4063698, baseEnd_4063698] using wordTrace_append hprefix tailTrace_4063698
  have hstable : (prefixWord ++ tailWord_4063698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063698).length < 2 ^ (prefixWord ++ tailWord_4063698).sum := by decide
  have hdescent : baseEnd_4063698 < baseStart_4063698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063709 : List Nat := [1, 4, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_4063709 : Nat := 118140960795 + 4063709 * 2 ^ 59
def prefixEnd_4063709 : Nat := 4983230072969 + 3 ^ 40 * 4063709 * 2
def baseEnd_4063709 : Nat := 1391090638001164302365899

theorem tailTrace_4063709 : CollatzResearch.WordTrace tailWord_4063709 prefixEnd_4063709 1391090638001164302365899 := by
  unfold tailWord_4063709
  simp only [CollatzResearch.WordTrace]
  refine ⟨148215643634883794088058181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98810429089922529392038787 148215643634883794088058181)
  ·
    refine ⟨27790433181540711391510909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148215643634883794088058181 27790433181540711391510909)
    ·
      refine ⟨10421412443077766771816591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27790433181540711391510909 10421412443077766771816591)
      ·
        refine ⟨15632118664616650157724887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10421412443077766771816591 15632118664616650157724887)
        ·
          refine ⟨23448177996924975236587331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15632118664616650157724887 23448177996924975236587331)
          ·
            refine ⟨35172266995387462854880997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23448177996924975236587331 35172266995387462854880997)
            ·
              refine ⟨6594800061635149285290187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35172266995387462854880997 6594800061635149285290187)
              ·
                refine ⟨9892200092452723927935281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6594800061635149285290187 9892200092452723927935281)
                ·
                  refine ⟨7419150069339542945951461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9892200092452723927935281 7419150069339542945951461)
                  ·
                    refine ⟨1391090638001164302365899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7419150069339542945951461 1391090638001164302365899)
                    ·
                      rfl

theorem cell22_4063709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_4063709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063709 prefixEnd_4063709 := by exact prefixLift 4063709
  have htrace : WordTrace (prefixWord ++ tailWord_4063709) baseStart_4063709 baseEnd_4063709 := by
    simpa [prefixWord, tailWord_4063709, baseEnd_4063709] using wordTrace_append hprefix tailTrace_4063709
  have hstable : (prefixWord ++ tailWord_4063709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063709).length < 2 ^ (prefixWord ++ tailWord_4063709).sum := by decide
  have hdescent : baseEnd_4063709 < baseStart_4063709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063730 : List Nat := [3, 2, 1, 4, 3, 1, 2, 2, 4]
def baseStart_4063730 : Nat := 118140960795 + 4063730 * 2 ^ 59
def prefixEnd_4063730 : Nat := 4983230072969 + 3 ^ 40 * 4063730 * 2
def baseEnd_4063730 : Nat := 463699275576775749196945

theorem tailTrace_4063730 : CollatzResearch.WordTrace tailWord_4063730 prefixEnd_4063730 463699275576775749196945 := by
  unfold tailWord_4063730
  simp only [CollatzResearch.WordTrace]
  refine ⟨37054102391951928668643161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98810939711871809783048429 37054102391951928668643161)
  ·
    refine ⟨27790576793963946501482371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37054102391951928668643161 27790576793963946501482371)
    ·
      refine ⟨41685865190945919752223557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27790576793963946501482371 41685865190945919752223557)
      ·
        refine ⟨7816099723302359953541917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41685865190945919752223557 7816099723302359953541917)
        ·
          refine ⟨2931037396238384982578219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7816099723302359953541917 2931037396238384982578219)
          ·
            refine ⟨4396556094357577473867329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931037396238384982578219 4396556094357577473867329)
            ·
              refine ⟨3297417070768183105400497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4396556094357577473867329 3297417070768183105400497)
              ·
                refine ⟨2473062803076137329050373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3297417070768183105400497 2473062803076137329050373)
                ·
                  refine ⟨463699275576775749196945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2473062803076137329050373 463699275576775749196945)
                  ·
                    rfl

theorem cell22_4063730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 4].length) (baseStart_4063730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063730 prefixEnd_4063730 := by exact prefixLift 4063730
  have htrace : WordTrace (prefixWord ++ tailWord_4063730) baseStart_4063730 baseEnd_4063730 := by
    simpa [prefixWord, tailWord_4063730, baseEnd_4063730] using wordTrace_append hprefix tailTrace_4063730
  have hstable : (prefixWord ++ tailWord_4063730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063730).length < 2 ^ (prefixWord ++ tailWord_4063730).sum := by decide
  have hdescent : baseEnd_4063730 < baseStart_4063730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063735 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 11]
def baseStart_4063735 : Nat := 118140960795 + 4063735 * 2 ^ 59
def prefixEnd_4063735 : Nat := 4983230072969 + 3 ^ 40 * 4063735 * 2
def baseEnd_4063735 : Nat := 463699846110836300405273

theorem tailTrace_4063735 : CollatzResearch.WordTrace tailWord_4063735 prefixEnd_4063735 463699846110836300405273 := by
  unfold tailWord_4063735
  simp only [CollatzResearch.WordTrace]
  refine ⟨148216591932789600528504659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98811061288526400352336439 148216591932789600528504659)
  ·
    refine ⟨222324887899184400792756989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148216591932789600528504659 222324887899184400792756989)
    ·
      refine ⟨83371832962194150297283871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222324887899184400792756989 83371832962194150297283871)
      ·
        refine ⟨125057749443291225445925807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83371832962194150297283871 125057749443291225445925807)
        ·
          refine ⟨187586624164936838168888711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125057749443291225445925807 187586624164936838168888711)
          ·
            refine ⟨281379936247405257253333067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187586624164936838168888711 281379936247405257253333067)
            ·
              refine ⟨422069904371107885879999601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 281379936247405257253333067 422069904371107885879999601)
              ·
                refine ⟨316552428278330914409999701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 422069904371107885879999601 316552428278330914409999701)
                ·
                  refine ⟨463699846110836300405273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 316552428278330914409999701 463699846110836300405273)
                  ·
                    rfl

theorem cell22_4063735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 11].length) (baseStart_4063735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063735 prefixEnd_4063735 := by exact prefixLift 4063735
  have htrace : WordTrace (prefixWord ++ tailWord_4063735) baseStart_4063735 baseEnd_4063735 := by
    simpa [prefixWord, tailWord_4063735, baseEnd_4063735] using wordTrace_append hprefix tailTrace_4063735
  have hstable : (prefixWord ++ tailWord_4063735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063735).length < 2 ^ (prefixWord ++ tailWord_4063735).sum := by decide
  have hdescent : baseEnd_4063735 < baseStart_4063735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063773 : List Nat := [1, 4, 2, 2, 1, 3, 2, 3, 1, 3]
def baseStart_4063773 : Nat := 118140960795 + 4063773 * 2 ^ 59
def prefixEnd_4063773 : Nat := 4983230072969 + 3 ^ 40 * 4063773 * 2
def baseEnd_4063773 : Nat := 1391112546509089468765703

theorem tailTrace_4063773 : CollatzResearch.WordTrace tailWord_4063773 prefixEnd_4063773 1391112546509089468765703 := by
  unfold tailWord_4063773
  simp only [CollatzResearch.WordTrace]
  refine ⟨148217977906651933018387973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98811985271101288678925315 148217977906651933018387973)
  ·
    refine ⟨27790870857497237440947745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148217977906651933018387973 27790870857497237440947745)
    ·
      refine ⟨20843153143122928080710809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27790870857497237440947745 20843153143122928080710809)
      ·
        refine ⟨15632364857342196060533107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20843153143122928080710809 15632364857342196060533107)
        ·
          refine ⟨23448547286013294090799661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15632364857342196060533107 23448547286013294090799661)
          ·
            refine ⟨8793205232254985284049873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23448547286013294090799661 8793205232254985284049873)
            ·
              refine ⟨6594903924191238963037405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8793205232254985284049873 6594903924191238963037405)
              ·
                refine ⟨2473088971571714611139027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6594903924191238963037405 2473088971571714611139027)
                ·
                  refine ⟨3709633457357571916708541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473088971571714611139027 3709633457357571916708541)
                  ·
                    refine ⟨1391112546509089468765703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3709633457357571916708541 1391112546509089468765703)
                    ·
                      rfl

theorem cell22_4063773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_4063773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063773 prefixEnd_4063773 := by exact prefixLift 4063773
  have htrace : WordTrace (prefixWord ++ tailWord_4063773) baseStart_4063773 baseEnd_4063773 := by
    simpa [prefixWord, tailWord_4063773, baseEnd_4063773] using wordTrace_append hprefix tailTrace_4063773
  have hstable : (prefixWord ++ tailWord_4063773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063773).length < 2 ^ (prefixWord ++ tailWord_4063773).sum := by decide
  have hdescent : baseEnd_4063773 < baseStart_4063773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063784 : List Nat := [2, 1, 5, 2, 1, 1, 1, 2, 2, 5]
def baseStart_4063784 : Nat := 118140960795 + 4063784 * 2 ^ 59
def prefixEnd_4063784 : Nat := 4983230072969 + 3 ^ 40 * 4063784 * 2
def baseEnd_4063784 : Nat := 1391116312033889106740669

theorem tailTrace_4063784 : CollatzResearch.WordTrace tailWord_4063784 prefixEnd_4063784 1391116312033889106740669 := by
  unfold tailWord_4063784
  simp only [CollatzResearch.WordTrace]
  refine ⟨74109189554806040948519203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98812252739741387931358937 74109189554806040948519203)
  ·
    refine ⟨111163784332209061422778805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74109189554806040948519203 111163784332209061422778805)
    ·
      refine ⟨10421604781144599508385513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 111163784332209061422778805 10421604781144599508385513)
      ·
        refine ⟨7816203585858449631289135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10421604781144599508385513 7816203585858449631289135)
        ·
          refine ⟨11724305378787674446933703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7816203585858449631289135 11724305378787674446933703)
          ·
            refine ⟨17586458068181511670400555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11724305378787674446933703 17586458068181511670400555)
            ·
              refine ⟨26379687102272267505600833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17586458068181511670400555 26379687102272267505600833)
              ·
                refine ⟨19784765326704200629200625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26379687102272267505600833 19784765326704200629200625)
                ·
                  refine ⟨14838573995028150471900469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19784765326704200629200625 14838573995028150471900469)
                  ·
                    refine ⟨1391116312033889106740669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14838573995028150471900469 1391116312033889106740669)
                    ·
                      rfl

theorem cell22_4063784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_4063784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063784 prefixEnd_4063784 := by exact prefixLift 4063784
  have htrace : WordTrace (prefixWord ++ tailWord_4063784) baseStart_4063784 baseEnd_4063784 := by
    simpa [prefixWord, tailWord_4063784, baseEnd_4063784] using wordTrace_append hprefix tailTrace_4063784
  have hstable : (prefixWord ++ tailWord_4063784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063784).length < 2 ^ (prefixWord ++ tailWord_4063784).sum := by decide
  have hdescent : baseEnd_4063784 < baseStart_4063784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063786 : List Nat := [3, 1, 4, 1, 1, 4, 1, 2, 5]
def baseStart_4063786 : Nat := 118140960795 + 4063786 * 2 ^ 59
def prefixEnd_4063786 : Nat := 4983230072969 + 3 ^ 40 * 4063786 * 2
def baseEnd_4063786 : Nat := 463705665558253922730221

theorem tailTrace_4063786 : CollatzResearch.WordTrace tailWord_4063786 prefixEnd_4063786 463705665558253922730221 := by
  unfold tailWord_4063786
  simp only [CollatzResearch.WordTrace]
  refine ⟨37054613013901209059652803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98812301370403224159074141 37054613013901209059652803)
  ·
    refine ⟨55581919520851813589479205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37054613013901209059652803 55581919520851813589479205)
    ·
      refine ⟨10421609910159715048027351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55581919520851813589479205 10421609910159715048027351)
      ·
        refine ⟨15632414865239572572041027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10421609910159715048027351 15632414865239572572041027)
        ·
          refine ⟨23448622297859358858061541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15632414865239572572041027 23448622297859358858061541)
          ·
            refine ⟨4396616680848629785886539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23448622297859358858061541 4396616680848629785886539)
            ·
              refine ⟨6594925021272944678829809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4396616680848629785886539 6594925021272944678829809)
              ·
                refine ⟨4946193765954708509122357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6594925021272944678829809 4946193765954708509122357)
                ·
                  refine ⟨463705665558253922730221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4946193765954708509122357 463705665558253922730221)
                  ·
                    rfl

theorem cell22_4063786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_4063786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063786 prefixEnd_4063786 := by exact prefixLift 4063786
  have htrace : WordTrace (prefixWord ++ tailWord_4063786) baseStart_4063786 baseEnd_4063786 := by
    simpa [prefixWord, tailWord_4063786, baseEnd_4063786] using wordTrace_append hprefix tailTrace_4063786
  have hstable : (prefixWord ++ tailWord_4063786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063786).length < 2 ^ (prefixWord ++ tailWord_4063786).sum := by decide
  have hdescent : baseEnd_4063786 < baseStart_4063786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063829 : List Nat := [1, 3, 2, 2, 1, 1, 3, 2, 4, 3]
def baseStart_4063829 : Nat := 118140960795 + 4063829 * 2 ^ 59
def prefixEnd_4063829 : Nat := 4983230072969 + 3 ^ 40 * 4063829 * 2
def baseEnd_4063829 : Nat := 1391131716453523989365531

theorem tailTrace_4063829 : CollatzResearch.WordTrace tailWord_4063829 prefixEnd_4063829 1391131716453523989365531 := by
  unfold tailWord_4063829
  simp only [CollatzResearch.WordTrace]
  refine ⟨148220020394449054582426541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98813346929632703054951027 148220020394449054582426541)
  ·
    refine ⟨55582507647918395468409953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148220020394449054582426541 55582507647918395468409953)
    ·
      refine ⟨41686880735938796601307465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55582507647918395468409953 41686880735938796601307465)
      ·
        refine ⟨31265160551954097450980599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41686880735938796601307465 31265160551954097450980599)
        ·
          refine ⟨46897740827931146176470899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31265160551954097450980599 46897740827931146176470899)
          ·
            refine ⟨70346611241896719264706349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46897740827931146176470899 70346611241896719264706349)
            ·
              refine ⟨26379979215711269724264881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 70346611241896719264706349 26379979215711269724264881)
              ·
                refine ⟨19784984411783452293198661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26379979215711269724264881 19784984411783452293198661)
                ·
                  refine ⟨3709684577209397304974749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19784984411783452293198661 3709684577209397304974749)
                  ·
                    refine ⟨1391131716453523989365531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3709684577209397304974749 1391131716453523989365531)
                    ·
                      rfl

theorem cell22_4063829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_4063829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063829 prefixEnd_4063829 := by exact prefixLift 4063829
  have htrace : WordTrace (prefixWord ++ tailWord_4063829) baseStart_4063829 baseEnd_4063829 := by
    simpa [prefixWord, tailWord_4063829, baseEnd_4063829] using wordTrace_append hprefix tailTrace_4063829
  have hstable : (prefixWord ++ tailWord_4063829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063829).length < 2 ^ (prefixWord ++ tailWord_4063829).sum := by decide
  have hdescent : baseEnd_4063829 < baseStart_4063829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063844 : List Nat := [2, 3, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_4063844 : Nat := 118140960795 + 4063844 * 2 ^ 59
def prefixEnd_4063844 : Nat := 4983230072969 + 3 ^ 40 * 4063844 * 2
def baseEnd_4063844 : Nat := 1391136851260068950240485

theorem tailTrace_4063844 : CollatzResearch.WordTrace tailWord_4063844 prefixEnd_4063844 1391136851260068950240485 := by
  unfold tailWord_4063844
  simp only [CollatzResearch.WordTrace]
  refine ⟨74110283744697356072111293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98813711659596474762815057 74110283744697356072111293)
  ·
    refine ⟨27791356404261508527041735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74110283744697356072111293 27791356404261508527041735)
    ·
      refine ⟨41687034606392262790562603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27791356404261508527041735 41687034606392262790562603)
      ·
        refine ⟨62530551909588394185843905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41687034606392262790562603 62530551909588394185843905)
        ·
          refine ⟨46897913932191295639382929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62530551909588394185843905 46897913932191295639382929)
          ·
            refine ⟨35173435449143471729537197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46897913932191295639382929 35173435449143471729537197)
            ·
              refine ⟨13190038293428801898576449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35173435449143471729537197 13190038293428801898576449)
              ·
                refine ⟨9892528720071601423932337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13190038293428801898576449 9892528720071601423932337)
                ·
                  refine ⟨7419396540053701067949253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9892528720071601423932337 7419396540053701067949253)
                  ·
                    refine ⟨1391136851260068950240485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7419396540053701067949253 1391136851260068950240485)
                    ·
                      rfl

theorem cell22_4063844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_4063844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063844 prefixEnd_4063844 := by exact prefixLift 4063844
  have htrace : WordTrace (prefixWord ++ tailWord_4063844) baseStart_4063844 baseEnd_4063844 := by
    simpa [prefixWord, tailWord_4063844, baseEnd_4063844] using wordTrace_append hprefix tailTrace_4063844
  have hstable : (prefixWord ++ tailWord_4063844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063844).length < 2 ^ (prefixWord ++ tailWord_4063844).sum := by decide
  have hdescent : baseEnd_4063844 < baseStart_4063844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063848 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 6]
def baseStart_4063848 : Nat := 118140960795 + 4063848 * 2 ^ 59
def prefixEnd_4063848 : Nat := 4983230072969 + 3 ^ 40 * 4063848 * 2
def baseEnd_4063848 : Nat := 463712740180604757713491

theorem tailTrace_4063848 : CollatzResearch.WordTrace tailWord_4063848 prefixEnd_4063848 463712740180604757713491 := by
  unfold tailWord_4063848
  simp only [CollatzResearch.WordTrace]
  refine ⟨74110356690690110413684099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98813808920920147218245465 74110356690690110413684099)
  ·
    refine ⟨111165535036035165620526149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74110356690690110413684099 111165535036035165620526149)
    ·
      refine ⟨20843537819256593553848653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 111165535036035165620526149 20843537819256593553848653)
      ·
        refine ⟨7816326682221222582693245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20843537819256593553848653 7816326682221222582693245)
        ·
          refine ⟨2931122505832958468509967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7816326682221222582693245 2931122505832958468509967)
          ·
            refine ⟨4396683758749437702764951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2931122505832958468509967 4396683758749437702764951)
            ·
              refine ⟨6595025638124156554147427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4396683758749437702764951 6595025638124156554147427)
              ·
                refine ⟨9892538457186234831221141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6595025638124156554147427 9892538457186234831221141)
                ·
                  refine ⟨463712740180604757713491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9892538457186234831221141 463712740180604757713491)
                  ·
                    rfl

theorem cell22_4063848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 6].length) (baseStart_4063848 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063848 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063848 prefixEnd_4063848 := by exact prefixLift 4063848
  have htrace : WordTrace (prefixWord ++ tailWord_4063848) baseStart_4063848 baseEnd_4063848 := by
    simpa [prefixWord, tailWord_4063848, baseEnd_4063848] using wordTrace_append hprefix tailTrace_4063848
  have hstable : (prefixWord ++ tailWord_4063848).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063848).length < 2 ^ (prefixWord ++ tailWord_4063848).sum := by decide
  have hdescent : baseEnd_4063848 < baseStart_4063848 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063908 : List Nat := [2, 3, 1, 2, 2, 1, 3, 4, 1, 3]
def baseStart_4063908 : Nat := 118140960795 + 4063908 * 2 ^ 59
def prefixEnd_4063908 : Nat := 4983230072969 + 3 ^ 40 * 4063908 * 2
def baseEnd_4063908 : Nat := 1391158759767994116640289

theorem tailTrace_4063908 : CollatzResearch.WordTrace tailWord_4063908 prefixEnd_4063908 1391158759767994116640289 := by
  unfold tailWord_4063908
  simp only [CollatzResearch.WordTrace]
  refine ⟨74111450880581425537276189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98815267840775234049701585 74111450880581425537276189)
  ·
    refine ⟨27791794080218034576478571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74111450880581425537276189 27791794080218034576478571)
    ·
      refine ⟨41687691120327051864717857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27791794080218034576478571 41687691120327051864717857)
      ·
        refine ⟨31265768340245288898538393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41687691120327051864717857 31265768340245288898538393)
        ·
          refine ⟨23449326255183966673903795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31265768340245288898538393 23449326255183966673903795)
          ·
            refine ⟨35173989382775950010855693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23449326255183966673903795 35173989382775950010855693)
            ·
              refine ⟨13190246018540981254070885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35173989382775950010855693 13190246018540981254070885)
              ·
                refine ⟨2473171128476433985138291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13190246018540981254070885 2473171128476433985138291)
                ·
                  refine ⟨3709756692714650977707437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473171128476433985138291 3709756692714650977707437)
                  ·
                    refine ⟨1391158759767994116640289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3709756692714650977707437 1391158759767994116640289)
                    ·
                      rfl

theorem cell22_4063908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_4063908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063908 prefixEnd_4063908 := by exact prefixLift 4063908
  have htrace : WordTrace (prefixWord ++ tailWord_4063908) baseStart_4063908 baseEnd_4063908 := by
    simpa [prefixWord, tailWord_4063908, baseEnd_4063908] using wordTrace_append hprefix tailTrace_4063908
  have hstable : (prefixWord ++ tailWord_4063908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063908).length < 2 ^ (prefixWord ++ tailWord_4063908).sum := by decide
  have hdescent : baseEnd_4063908 < baseStart_4063908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063919 : List Nat := [1, 1, 2, 1, 2, 6, 1, 1, 2, 5]
def baseStart_4063919 : Nat := 118140960795 + 4063919 * 2 ^ 59
def prefixEnd_4063919 : Nat := 4983230072969 + 3 ^ 40 * 4063919 * 2
def baseEnd_4063919 : Nat := 1391162525292793754615255

theorem tailTrace_4063919 : CollatzResearch.WordTrace tailWord_4063919 prefixEnd_4063919 1391162525292793754615255 := by
  unfold tailWord_4063919
  simp only [CollatzResearch.WordTrace]
  refine ⟨148223302964122999953202811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98815535309415333302135207 148223302964122999953202811)
  ·
    refine ⟨222334954446184499929804217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148223302964122999953202811 222334954446184499929804217)
    ·
      refine ⟨166751215834638374947353163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222334954446184499929804217 166751215834638374947353163)
      ·
        refine ⟨250126823751957562421029745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166751215834638374947353163 250126823751957562421029745)
        ·
          refine ⟨187595117813968171815772309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250126823751957562421029745 187595117813968171815772309)
          ·
            refine ⟨8793521147529758053864327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187595117813968171815772309 8793521147529758053864327)
            ·
              refine ⟨13190281721294637080796491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8793521147529758053864327 13190281721294637080796491)
              ·
                refine ⟨19785422581941955621194737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13190281721294637080796491 19785422581941955621194737)
                ·
                  refine ⟨14839066936456466715896053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19785422581941955621194737 14839066936456466715896053)
                  ·
                    refine ⟨1391162525292793754615255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14839066936456466715896053 1391162525292793754615255)
                    ·
                      rfl

theorem cell22_4063919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 1, 1, 2, 5].length) (baseStart_4063919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063919 prefixEnd_4063919 := by exact prefixLift 4063919
  have htrace : WordTrace (prefixWord ++ tailWord_4063919) baseStart_4063919 baseEnd_4063919 := by
    simpa [prefixWord, tailWord_4063919, baseEnd_4063919] using wordTrace_append hprefix tailTrace_4063919
  have hstable : (prefixWord ++ tailWord_4063919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063919).length < 2 ^ (prefixWord ++ tailWord_4063919).sum := by decide
  have hdescent : baseEnd_4063919 < baseStart_4063919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4063998 : List Nat := [4, 2, 2, 1, 2, 1, 1, 2, 4, 3]
def baseStart_4063998 : Nat := 118140960795 + 4063998 * 2 ^ 59
def prefixEnd_4063998 : Nat := 4983230072969 + 3 ^ 40 * 4063998 * 2
def baseEnd_4063998 : Nat := 1391189568607263881890013

theorem tailTrace_4063998 : CollatzResearch.WordTrace tailWord_4063998 prefixEnd_4063998 1391189568607263881890013 := by
  unfold tailWord_4063998
  simp only [CollatzResearch.WordTrace]
  refine ⟨18528273041354599555666081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98817456220557864296885765 18528273041354599555666081)
  ·
    refine ⟨13896204781015949666749561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18528273041354599555666081 13896204781015949666749561)
    ·
      refine ⟨10422153585761962250062171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13896204781015949666749561 10422153585761962250062171)
      ·
        refine ⟨15633230378642943375093257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10422153585761962250062171 15633230378642943375093257)
        ·
          refine ⟨11724922783982207531319943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15633230378642943375093257 11724922783982207531319943)
          ·
            refine ⟨17587384175973311296979915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11724922783982207531319943 17587384175973311296979915)
            ·
              refine ⟨26381076263959966945469873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17587384175973311296979915 26381076263959966945469873)
              ·
                refine ⟨19785807197969975209102405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26381076263959966945469873 19785807197969975209102405)
                ·
                  refine ⟨3709838849619370351706701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19785807197969975209102405 3709838849619370351706701)
                  ·
                    refine ⟨1391189568607263881890013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3709838849619370351706701 1391189568607263881890013)
                    ·
                      rfl

theorem cell22_4063998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_4063998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4063998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4063998 prefixEnd_4063998 := by exact prefixLift 4063998
  have htrace : WordTrace (prefixWord ++ tailWord_4063998) baseStart_4063998 baseEnd_4063998 := by
    simpa [prefixWord, tailWord_4063998, baseEnd_4063998] using wordTrace_append hprefix tailTrace_4063998
  have hstable : (prefixWord ++ tailWord_4063998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4063998).length < 2 ^ (prefixWord ++ tailWord_4063998).sum := by decide
  have hdescent : baseEnd_4063998 < baseStart_4063998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4063998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064024 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 2, 6]
def baseStart_4064024 : Nat := 118140960795 + 4064024 * 2 ^ 59
def prefixEnd_4064024 : Nat := 4983230072969 + 3 ^ 40 * 4064024 * 2
def baseEnd_4064024 : Nat := 1391198468938608480739933

theorem tailTrace_4064024 : CollatzResearch.WordTrace tailWord_4064024 prefixEnd_4064024 1391198468938608480739933 := by
  unfold tailWord_4064024
  simp only [CollatzResearch.WordTrace]
  refine ⟨74113566314371301442887563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98818088419161735257183417 74113566314371301442887563)
  ·
    refine ⟨111170349471556952164331345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74113566314371301442887563 111170349471556952164331345)
    ·
      refine ⟨83377762103667714123248509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111170349471556952164331345 83377762103667714123248509)
      ·
        refine ⟨31266660788875392796218191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83377762103667714123248509 31266660788875392796218191)
        ·
          refine ⟨46899991183313089194327287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31266660788875392796218191 46899991183313089194327287)
          ·
            refine ⟨70349986774969633791490931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46899991183313089194327287 70349986774969633791490931)
            ·
              refine ⟨105524980162454450687236397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70349986774969633791490931 105524980162454450687236397)
              ·
                refine ⟨39571867560920419007713649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 105524980162454450687236397 39571867560920419007713649)
                ·
                  refine ⟨29678900670690314255785237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39571867560920419007713649 29678900670690314255785237)
                  ·
                    refine ⟨1391198468938608480739933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29678900670690314255785237 1391198468938608480739933)
                    ·
                      rfl

theorem cell22_4064024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_4064024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064024 prefixEnd_4064024 := by exact prefixLift 4064024
  have htrace : WordTrace (prefixWord ++ tailWord_4064024) baseStart_4064024 baseEnd_4064024 := by
    simpa [prefixWord, tailWord_4064024, baseEnd_4064024] using wordTrace_append hprefix tailTrace_4064024
  have hstable : (prefixWord ++ tailWord_4064024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064024).length < 2 ^ (prefixWord ++ tailWord_4064024).sum := by decide
  have hdescent : baseEnd_4064024 < baseStart_4064024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064131 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 4, 4]
def baseStart_4064131 : Nat := 118140960795 + 4064131 * 2 ^ 59
def prefixEnd_4064131 : Nat := 4983230072969 + 3 ^ 40 * 4064131 * 2
def baseEnd_4064131 : Nat := 1391235097225295868314605

theorem tailTrace_4064131 : CollatzResearch.WordTrace tailWord_4064131 prefixEnd_4064131 1391235097225295868314605 := by
  unfold tailWord_4064131
  simp only [CollatzResearch.WordTrace]
  refine ⟨148231035239354960159920247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98820690159569973439946831 148231035239354960159920247)
  ·
    refine ⟨222346552859032440239880371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148231035239354960159920247 222346552859032440239880371)
    ·
      refine ⟨333519829288548660359820557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222346552859032440239880371 333519829288548660359820557)
      ·
        refine ⟨125069935983205747634932709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 333519829288548660359820557 125069935983205747634932709)
        ·
          refine ⟨23450612996851077681549883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 125069935983205747634932709 23450612996851077681549883)
          ·
            refine ⟨35175919495276616522324825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23450612996851077681549883 35175919495276616522324825)
            ·
              refine ⟨26381939621457462391743619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35175919495276616522324825 26381939621457462391743619)
              ·
                refine ⟨39572909432186193587615429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26381939621457462391743619 39572909432186193587615429)
                ·
                  refine ⟨7419920518534911297677893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39572909432186193587615429 7419920518534911297677893)
                  ·
                    refine ⟨1391235097225295868314605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7419920518534911297677893 1391235097225295868314605)
                    ·
                      rfl

theorem cell22_4064131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 4].length) (baseStart_4064131 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064131 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064131 prefixEnd_4064131 := by exact prefixLift 4064131
  have htrace : WordTrace (prefixWord ++ tailWord_4064131) baseStart_4064131 baseEnd_4064131 := by
    simpa [prefixWord, tailWord_4064131, baseEnd_4064131] using wordTrace_append hprefix tailTrace_4064131
  have hstable : (prefixWord ++ tailWord_4064131).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064131).length < 2 ^ (prefixWord ++ tailWord_4064131).sum := by decide
  have hdescent : baseEnd_4064131 < baseStart_4064131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064133 : List Nat := [1, 3, 1, 1, 3, 4, 1, 1, 4, 3]
def baseStart_4064133 : Nat := 118140960795 + 4064133 * 2 ^ 59
def prefixEnd_4064133 : Nat := 4983230072969 + 3 ^ 40 * 4064133 * 2
def baseEnd_4064133 : Nat := 1391235781866168529764599

theorem tailTrace_4064133 : CollatzResearch.WordTrace tailWord_4064133 prefixEnd_4064133 1391235781866168529764599 := by
  unfold tailWord_4064133
  simp only [CollatzResearch.WordTrace]
  refine ⟨148231108185347714501493053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98820738790231809667662035 148231108185347714501493053)
  ·
    refine ⟨55586665569505392938059895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148231108185347714501493053 55586665569505392938059895)
    ·
      refine ⟨83379998354258089407089843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55586665569505392938059895 83379998354258089407089843)
      ·
        refine ⟨125069997531387134110634765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83379998354258089407089843 125069997531387134110634765)
        ·
          refine ⟨46901249074270175291488037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125069997531387134110634765 46901249074270175291488037)
          ·
            refine ⟨8793984201425657867154007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46901249074270175291488037 8793984201425657867154007)
            ·
              refine ⟨13190976302138486800731011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8793984201425657867154007 13190976302138486800731011)
              ·
                refine ⟨19786464453207730201096517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13190976302138486800731011 19786464453207730201096517)
                ·
                  refine ⟨3709962084976449412705597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19786464453207730201096517 3709962084976449412705597)
                  ·
                    refine ⟨1391235781866168529764599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3709962084976449412705597 1391235781866168529764599)
                    ·
                      rfl

theorem cell22_4064133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 1, 4, 3].length) (baseStart_4064133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064133 prefixEnd_4064133 := by exact prefixLift 4064133
  have htrace : WordTrace (prefixWord ++ tailWord_4064133) baseStart_4064133 baseEnd_4064133 := by
    simpa [prefixWord, tailWord_4064133, baseEnd_4064133] using wordTrace_append hprefix tailTrace_4064133
  have hstable : (prefixWord ++ tailWord_4064133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064133).length < 2 ^ (prefixWord ++ tailWord_4064133).sum := by decide
  have hdescent : baseEnd_4064133 < baseStart_4064133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064180 : List Nat := [2, 5, 2, 1, 1, 3, 8]
def baseStart_4064180 : Nat := 118140960795 + 4064180 * 2 ^ 59
def prefixEnd_4064180 : Nat := 4983230072969 + 3 ^ 40 * 4064180 * 2
def baseEnd_4064180 : Nat := 51527847071358373105165

theorem tailTrace_4064180 : CollatzResearch.WordTrace tailWord_4064180 prefixEnd_4064180 51527847071358373105165 := by
  unfold tailWord_4064180
  simp only [CollatzResearch.WordTrace]
  refine ⟨74116411208088720764226997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98821881610784961018969329 74116411208088720764226997)
  ·
    refine ⟨6948413550758317571646281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 74116411208088720764226997 6948413550758317571646281)
    ·
      refine ⟨5211310163068738178734711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6948413550758317571646281 5211310163068738178734711)
      ·
        refine ⟨7816965244603107268102067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5211310163068738178734711 7816965244603107268102067)
        ·
          refine ⟨11725447866904660902153101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7816965244603107268102067 11725447866904660902153101)
          ·
            refine ⟨4397042950089247838307413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11725447866904660902153101 4397042950089247838307413)
            ·
              refine ⟨51527847071358373105165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4397042950089247838307413 51527847071358373105165)
              ·
                rfl

theorem cell22_4064180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 8].length) (baseStart_4064180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064180 prefixEnd_4064180 := by exact prefixLift 4064180
  have htrace : WordTrace (prefixWord ++ tailWord_4064180) baseStart_4064180 baseEnd_4064180 := by
    simpa [prefixWord, tailWord_4064180, baseEnd_4064180] using wordTrace_append hprefix tailTrace_4064180
  have hstable : (prefixWord ++ tailWord_4064180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064180).length < 2 ^ (prefixWord ++ tailWord_4064180).sum := by decide
  have hdescent : baseEnd_4064180 < baseStart_4064180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064242 : List Nat := [3, 2, 1, 5, 1, 1, 2, 2, 5]
def baseStart_4064242 : Nat := 118140960795 + 4064242 * 2 ^ 59
def prefixEnd_4064242 : Nat := 4983230072969 + 3 ^ 40 * 4064242 * 2
def baseEnd_4064242 : Nat := 463757698264576192929755

theorem tailTrace_4064242 : CollatzResearch.WordTrace tailWord_4064242 prefixEnd_4064242 463757698264576192929755 := by
  unfold tailWord_4064242
  simp only [CollatzResearch.WordTrace]
  refine ⟨37058770935488206529302745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98823389161301884078140653 37058770935488206529302745)
  ·
    refine ⟨27794078201616154896977059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37058770935488206529302745 27794078201616154896977059)
    ·
      refine ⟨41691117302424232345465589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27794078201616154896977059 41691117302424232345465589)
      ·
        refine ⟨3908542247102271782387399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41691117302424232345465589 3908542247102271782387399)
        ·
          refine ⟨5862813370653407673581099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3908542247102271782387399 5862813370653407673581099)
          ·
            refine ⟨8794220055980111510371649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5862813370653407673581099 8794220055980111510371649)
            ·
              refine ⟨6595665041985083632778737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8794220055980111510371649 6595665041985083632778737)
              ·
                refine ⟨4946748781488812724584053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6595665041985083632778737 4946748781488812724584053)
                ·
                  refine ⟨463757698264576192929755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4946748781488812724584053 463757698264576192929755)
                  ·
                    rfl

theorem cell22_4064242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_4064242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064242 prefixEnd_4064242 := by exact prefixLift 4064242
  have htrace : WordTrace (prefixWord ++ tailWord_4064242) baseStart_4064242 baseEnd_4064242 := by
    simpa [prefixWord, tailWord_4064242, baseEnd_4064242] using wordTrace_append hprefix tailTrace_4064242
  have hstable : (prefixWord ++ tailWord_4064242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064242).length < 2 ^ (prefixWord ++ tailWord_4064242).sum := by decide
  have hdescent : baseEnd_4064242 < baseStart_4064242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064246 : List Nat := [5, 1, 1, 1, 3, 3, 2, 2, 1, 3]
def baseStart_4064246 : Nat := 118140960795 + 4064246 * 2 ^ 59
def prefixEnd_4064246 : Nat := 4983230072969 + 3 ^ 40 * 4064246 * 2
def baseEnd_4064246 : Nat := 1391274464075473901689253

theorem tailTrace_4064246 : CollatzResearch.WordTrace tailWord_4064246 prefixEnd_4064246 1391274464075473901689253 := by
  unfold tailWord_4064246
  simp only [CollatzResearch.WordTrace]
  refine ⟨9264701852121145925022287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98823486422625556533571061 9264701852121145925022287)
  ·
    refine ⟨13897052778181718887533431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9264701852121145925022287 13897052778181718887533431)
    ·
      refine ⟨20845579167272578331300147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13897052778181718887533431 20845579167272578331300147)
      ·
        refine ⟨31268368750908867496950221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20845579167272578331300147 31268368750908867496950221)
        ·
          refine ⟨11725638281590825311356333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31268368750908867496950221 11725638281590825311356333)
          ·
            refine ⟨4397114355596559491758625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11725638281590825311356333 4397114355596559491758625)
            ·
              refine ⟨3297835766697419618818969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4397114355596559491758625 3297835766697419618818969)
              ·
                refine ⟨2473376825023064714114227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3297835766697419618818969 2473376825023064714114227)
                ·
                  refine ⟨3710065237534597071171341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473376825023064714114227 3710065237534597071171341)
                  ·
                    refine ⟨1391274464075473901689253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3710065237534597071171341 1391274464075473901689253)
                    ·
                      rfl

theorem cell22_4064246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_4064246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064246 prefixEnd_4064246 := by exact prefixLift 4064246
  have htrace : WordTrace (prefixWord ++ tailWord_4064246) baseStart_4064246 baseEnd_4064246 := by
    simpa [prefixWord, tailWord_4064246, baseEnd_4064246] using wordTrace_append hprefix tailTrace_4064246
  have hstable : (prefixWord ++ tailWord_4064246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064246).length < 2 ^ (prefixWord ++ tailWord_4064246).sum := by decide
  have hdescent : baseEnd_4064246 < baseStart_4064246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064251 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 5, 5]
def baseStart_4064251 : Nat := 118140960795 + 4064251 * 2 ^ 59
def prefixEnd_4064251 : Nat := 4983230072969 + 3 ^ 40 * 4064251 * 2
def baseEnd_4064251 : Nat := 1391276175677655555314237

theorem tailTrace_4064251 : CollatzResearch.WordTrace tailWord_4064251 prefixEnd_4064251 1391276175677655555314237 := by
  unfold tailWord_4064251
  simp only [CollatzResearch.WordTrace]
  refine ⟨148235411998920220654288607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98823607999280147102859071 148235411998920220654288607)
  ·
    refine ⟨222353117998380330981432911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148235411998920220654288607 222353117998380330981432911)
    ·
      refine ⟨333529676997570496472149367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222353117998380330981432911 333529676997570496472149367)
      ·
        refine ⟨500294515496355744708224051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333529676997570496472149367 500294515496355744708224051)
        ·
          refine ⟨750441773244533617062336077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500294515496355744708224051 750441773244533617062336077)
          ·
            refine ⟨281415664966700106398376029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 750441773244533617062336077 281415664966700106398376029)
            ·
              refine ⟨105530874362512539899391011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 281415664966700106398376029 105530874362512539899391011)
              ·
                refine ⟨158296311543768809849086517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105530874362512539899391011 158296311543768809849086517)
                ·
                  refine ⟨14840279207228325923351861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 158296311543768809849086517 14840279207228325923351861)
                  ·
                    refine ⟨1391276175677655555314237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14840279207228325923351861 1391276175677655555314237)
                    ·
                      rfl

theorem cell22_4064251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 5].length) (baseStart_4064251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064251 prefixEnd_4064251 := by exact prefixLift 4064251
  have htrace : WordTrace (prefixWord ++ tailWord_4064251) baseStart_4064251 baseEnd_4064251 := by
    simpa [prefixWord, tailWord_4064251, baseEnd_4064251] using wordTrace_append hprefix tailTrace_4064251
  have hstable : (prefixWord ++ tailWord_4064251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064251).length < 2 ^ (prefixWord ++ tailWord_4064251).sum := by decide
  have hdescent : baseEnd_4064251 < baseStart_4064251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064268 : List Nat := [2, 2, 1, 2, 3, 2, 1, 3, 1, 5]
def baseStart_4064268 : Nat := 118140960795 + 4064268 * 2 ^ 59
def prefixEnd_4064268 : Nat := 4983230072969 + 3 ^ 40 * 4064268 * 2
def baseEnd_4064268 : Nat := 1391281995125073177639185

theorem tailTrace_4064268 : CollatzResearch.WordTrace tailWord_4064268 prefixEnd_4064268 1391281995125073177639185 := by
  unfold tailWord_4064268
  simp only [CollatzResearch.WordTrace]
  refine ⟨74118016019929316278828729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98824021359905755038438305 74118016019929316278828729)
  ·
    refine ⟨55588512014946987209121547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74118016019929316278828729 55588512014946987209121547)
    ·
      refine ⟨83382768022420480813682321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55588512014946987209121547 83382768022420480813682321)
      ·
        refine ⟨62537076016815360610261741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83382768022420480813682321 62537076016815360610261741)
        ·
          refine ⟨23451403506305760228848153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62537076016815360610261741 23451403506305760228848153)
          ·
            refine ⟨17588552629729320171636115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23451403506305760228848153 17588552629729320171636115)
            ·
              refine ⟨26382828944593980257454173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17588552629729320171636115 26382828944593980257454173)
              ·
                refine ⟨9893560854222742596545315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26382828944593980257454173 9893560854222742596545315)
                ·
                  refine ⟨14840341281334113894817973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9893560854222742596545315 14840341281334113894817973)
                  ·
                    refine ⟨1391281995125073177639185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14840341281334113894817973 1391281995125073177639185)
                    ·
                      rfl

theorem cell22_4064268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_4064268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064268 prefixEnd_4064268 := by exact prefixLift 4064268
  have htrace : WordTrace (prefixWord ++ tailWord_4064268) baseStart_4064268 baseEnd_4064268 := by
    simpa [prefixWord, tailWord_4064268, baseEnd_4064268] using wordTrace_append hprefix tailTrace_4064268
  have hstable : (prefixWord ++ tailWord_4064268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064268).length < 2 ^ (prefixWord ++ tailWord_4064268).sum := by decide
  have hdescent : baseEnd_4064268 < baseStart_4064268 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064281 : List Nat := [1, 2, 1, 2, 1, 1, 4, 10]
def baseStart_4064281 : Nat := 118140960795 + 4064281 * 2 ^ 59
def prefixEnd_4064281 : Nat := 4983230072969 + 3 ^ 40 * 4064281 * 2
def baseEnd_4064281 : Nat := 154587382810082830784905

theorem tailTrace_4064281 : CollatzResearch.WordTrace tailWord_4064281 prefixEnd_4064281 154587382810082830784905 := by
  unfold tailWord_4064281
  simp only [CollatzResearch.WordTrace]
  refine ⟨148236506188811535777880697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98824337459207690518587131 148236506188811535777880697)
  ·
    refine ⟨111177379641608651833410523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148236506188811535777880697 111177379641608651833410523)
    ·
      refine ⟨166766069462412977750115785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111177379641608651833410523 166766069462412977750115785)
      ·
        refine ⟨125074552096809733312586839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166766069462412977750115785 125074552096809733312586839)
        ·
          refine ⟨187611828145214599968880259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125074552096809733312586839 187611828145214599968880259)
          ·
            refine ⟨281417742217821899953320389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187611828145214599968880259 281417742217821899953320389)
            ·
              refine ⟨52765826665841606241247573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 281417742217821899953320389 52765826665841606241247573)
              ·
                refine ⟨154587382810082830784905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52765826665841606241247573 154587382810082830784905)
                ·
                  rfl

theorem cell22_4064281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 10].length) (baseStart_4064281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064281 prefixEnd_4064281 := by exact prefixLift 4064281
  have htrace : WordTrace (prefixWord ++ tailWord_4064281) baseStart_4064281 baseEnd_4064281 := by
    simpa [prefixWord, tailWord_4064281, baseEnd_4064281] using wordTrace_append hprefix tailTrace_4064281
  have hstable : (prefixWord ++ tailWord_4064281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064281).length < 2 ^ (prefixWord ++ tailWord_4064281).sum := by decide
  have hdescent : baseEnd_4064281 < baseStart_4064281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064330 : List Nat := [3, 1, 2, 1, 1, 2, 4, 2, 3, 3]
def baseStart_4064330 : Nat := 118140960795 + 4064330 * 2 ^ 59
def prefixEnd_4064330 : Nat := 4983230072969 + 3 ^ 40 * 4064330 * 2
def baseEnd_4064330 : Nat := 1391303218992125682588995

theorem tailTrace_4064330 : CollatzResearch.WordTrace tailWord_4064330 prefixEnd_4064330 1391303218992125682588995 := by
  unfold tailWord_4064330
  simp only [CollatzResearch.WordTrace]
  refine ⟨37059573341408504286603611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98825528910422678097609629 37059573341408504286603611)
  ·
    refine ⟨55589360012112756429905417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37059573341408504286603611 55589360012112756429905417)
    ·
      refine ⟨41692020009084567322429063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55589360012112756429905417 41692020009084567322429063)
      ·
        refine ⟨62538030013626850983643595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41692020009084567322429063 62538030013626850983643595)
        ·
          refine ⟨93807045020440276475465393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62538030013626850983643595 93807045020440276475465393)
          ·
            refine ⟨70355283765330207356599045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93807045020440276475465393 70355283765330207356599045)
            ·
              refine ⟨13191615705999413879362321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70355283765330207356599045 13191615705999413879362321)
              ·
                refine ⟨9893711779499560409521741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13191615705999413879362321 9893711779499560409521741)
                ·
                  refine ⟨3710141917312335153570653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9893711779499560409521741 3710141917312335153570653)
                  ·
                    refine ⟨1391303218992125682588995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3710141917312335153570653 1391303218992125682588995)
                    ·
                      rfl

theorem cell22_4064330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_4064330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064330 prefixEnd_4064330 := by exact prefixLift 4064330
  have htrace : WordTrace (prefixWord ++ tailWord_4064330) baseStart_4064330 baseEnd_4064330 := by
    simpa [prefixWord, tailWord_4064330, baseEnd_4064330] using wordTrace_append hprefix tailTrace_4064330
  have hstable : (prefixWord ++ tailWord_4064330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064330).length < 2 ^ (prefixWord ++ tailWord_4064330).sum := by decide
  have hdescent : baseEnd_4064330 < baseStart_4064330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064364 : List Nat := [2, 2, 1, 1, 3, 2, 5, 2, 1, 3]
def baseStart_4064364 : Nat := 118140960795 + 4064364 * 2 ^ 59
def prefixEnd_4064364 : Nat := 4983230072969 + 3 ^ 40 * 4064364 * 2
def baseEnd_4064364 : Nat := 1391314857886960927238891

theorem tailTrace_4064364 : CollatzResearch.WordTrace tailWord_4064364 prefixEnd_4064364 1391314857886960927238891 := by
  unfold tailWord_4064364
  simp only [CollatzResearch.WordTrace]
  refine ⟨74119766723755420476576073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98826355631673893968768097 74119766723755420476576073)
  ·
    refine ⟨55589825042816565357432055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74119766723755420476576073 55589825042816565357432055)
    ·
      refine ⟨83384737564224848036148083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55589825042816565357432055 83384737564224848036148083)
      ·
        refine ⟨125077106346337272054222125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83384737564224848036148083 125077106346337272054222125)
        ·
          refine ⟨46903914879876477020333297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125077106346337272054222125 46903914879876477020333297)
          ·
            refine ⟨35177936159907357765249973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46903914879876477020333297 35177936159907357765249973)
            ·
              refine ⟨3297931514991314790492185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 35177936159907357765249973 3297931514991314790492185)
              ·
                refine ⟨2473448636243486092869139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3297931514991314790492185 2473448636243486092869139)
                ·
                  refine ⟨3710172954365229139303709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473448636243486092869139 3710172954365229139303709)
                  ·
                    refine ⟨1391314857886960927238891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3710172954365229139303709 1391314857886960927238891)
                    ·
                      rfl

theorem cell22_4064364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_4064364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064364 prefixEnd_4064364 := by exact prefixLift 4064364
  have htrace : WordTrace (prefixWord ++ tailWord_4064364) baseStart_4064364 baseEnd_4064364 := by
    simpa [prefixWord, tailWord_4064364, baseEnd_4064364] using wordTrace_append hprefix tailTrace_4064364
  have hstable : (prefixWord ++ tailWord_4064364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064364).length < 2 ^ (prefixWord ++ tailWord_4064364).sum := by decide
  have hdescent : baseEnd_4064364 < baseStart_4064364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064403 : List Nat := [1, 1, 1, 2, 1, 2, 5, 1, 3, 5]
def baseStart_4064403 : Nat := 118140960795 + 4064403 * 2 ^ 59
def prefixEnd_4064403 : Nat := 4983230072969 + 3 ^ 40 * 4064403 * 2
def baseEnd_4064403 : Nat := 1391328208383977825513771

theorem tailTrace_4064403 : CollatzResearch.WordTrace tailWord_4064403 prefixEnd_4064403 1391328208383977825513771 := by
  unfold tailWord_4064403
  simp only [CollatzResearch.WordTrace]
  refine ⟨148240955894369550613821863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98827303929579700409214575 148240955894369550613821863)
  ·
    refine ⟨222361433841554325920732795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148240955894369550613821863 222361433841554325920732795)
    ·
      refine ⟨333542150762331488881099193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222361433841554325920732795 333542150762331488881099193)
      ·
        refine ⟨250156613071748616660824395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333542150762331488881099193 250156613071748616660824395)
        ·
          refine ⟨375234919607622924991236593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250156613071748616660824395 375234919607622924991236593)
          ·
            refine ⟨281426189705717193743427445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 375234919607622924991236593 281426189705717193743427445)
            ·
              refine ⟨26383705284910986913446323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 281426189705717193743427445 26383705284910986913446323)
              ·
                refine ⟨39575557927366480370169485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26383705284910986913446323 39575557927366480370169485)
                ·
                  refine ⟨14840834222762430138813557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39575557927366480370169485 14840834222762430138813557)
                  ·
                    refine ⟨1391328208383977825513771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14840834222762430138813557 1391328208383977825513771)
                    ·
                      rfl

theorem cell22_4064403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 1, 3, 5].length) (baseStart_4064403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064403 prefixEnd_4064403 := by exact prefixLift 4064403
  have htrace : WordTrace (prefixWord ++ tailWord_4064403) baseStart_4064403 baseEnd_4064403 := by
    simpa [prefixWord, tailWord_4064403, baseEnd_4064403] using wordTrace_append hprefix tailTrace_4064403
  have hstable : (prefixWord ++ tailWord_4064403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064403).length < 2 ^ (prefixWord ++ tailWord_4064403).sum := by decide
  have hdescent : baseEnd_4064403 < baseStart_4064403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064452 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_4064452 : Nat := 118140960795 + 4064452 * 2 ^ 59
def prefixEnd_4064452 : Nat := 4983230072969 + 3 ^ 40 * 4064452 * 2
def baseEnd_4064452 : Nat := 1391344982085358031038621

theorem tailTrace_4064452 : CollatzResearch.WordTrace tailWord_4064452 prefixEnd_4064452 1391344982085358031038621 := by
  unfold tailWord_4064452
  simp only [CollatzResearch.WordTrace]
  refine ⟨74121371535596015991177805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98828495380794687988237073 74121371535596015991177805)
  ·
    refine ⟨27795514325848505996691677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74121371535596015991177805 27795514325848505996691677)
    ·
      refine ⟨10423317872193189748759379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27795514325848505996691677 10423317872193189748759379)
      ·
        refine ⟨15634976808289784623139069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10423317872193189748759379 15634976808289784623139069)
        ·
          refine ⟨5863116303108669233677151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15634976808289784623139069 5863116303108669233677151)
          ·
            refine ⟨8794674454663003850515727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5863116303108669233677151 8794674454663003850515727)
            ·
              refine ⟨13192011681994505775773591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8794674454663003850515727 13192011681994505775773591)
              ·
                refine ⟨19788017522991758663660387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13192011681994505775773591 19788017522991758663660387)
                ·
                  refine ⟨29682026284487637995490581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19788017522991758663660387 29682026284487637995490581)
                  ·
                    refine ⟨1391344982085358031038621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29682026284487637995490581 1391344982085358031038621)
                    ·
                      rfl

theorem cell22_4064452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_4064452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064452 prefixEnd_4064452 := by exact prefixLift 4064452
  have htrace : WordTrace (prefixWord ++ tailWord_4064452) baseStart_4064452 baseEnd_4064452 := by
    simpa [prefixWord, tailWord_4064452, baseEnd_4064452] using wordTrace_append hprefix tailTrace_4064452
  have hstable : (prefixWord ++ tailWord_4064452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064452).length < 2 ^ (prefixWord ++ tailWord_4064452).sum := by decide
  have hdescent : baseEnd_4064452 < baseStart_4064452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064463 : List Nat := [1, 1, 2, 1, 1, 3, 2, 2, 1, 8]
def baseStart_4064463 : Nat := 118140960795 + 4064463 * 2 ^ 59
def prefixEnd_4064463 : Nat := 4983230072969 + 3 ^ 40 * 4064463 * 2
def baseEnd_4064463 : Nat := 1391348747610157669013587

theorem tailTrace_4064463 : CollatzResearch.WordTrace tailWord_4064463 prefixEnd_4064463 1391348747610157669013587 := by
  unfold tailWord_4064463
  simp only [CollatzResearch.WordTrace]
  refine ⟨148243144274152180861006043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98828762849434787240670695 148243144274152180861006043)
  ·
    refine ⟨222364716411228271291509065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148243144274152180861006043 222364716411228271291509065)
    ·
      refine ⟨166773537308421203468631799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 222364716411228271291509065 166773537308421203468631799)
      ·
        refine ⟨250160305962631805202947699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166773537308421203468631799 250160305962631805202947699)
        ·
          refine ⟨375240458943947707804421549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 250160305962631805202947699 375240458943947707804421549)
          ·
            refine ⟨140715172103980390426658081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 375240458943947707804421549 140715172103980390426658081)
            ·
              refine ⟨105536379077985292819993561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 140715172103980390426658081 105536379077985292819993561)
              ·
                refine ⟨79152284308488969614995171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 105536379077985292819993561 79152284308488969614995171)
                ·
                  refine ⟨118728426462733454422492757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 79152284308488969614995171 118728426462733454422492757)
                  ·
                    refine ⟨1391348747610157669013587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 118728426462733454422492757 1391348747610157669013587)
                    ·
                      rfl

theorem cell22_4064463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_4064463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064463 prefixEnd_4064463 := by exact prefixLift 4064463
  have htrace : WordTrace (prefixWord ++ tailWord_4064463) baseStart_4064463 baseEnd_4064463 := by
    simpa [prefixWord, tailWord_4064463, baseEnd_4064463] using wordTrace_append hprefix tailTrace_4064463
  have hstable : (prefixWord ++ tailWord_4064463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064463).length < 2 ^ (prefixWord ++ tailWord_4064463).sum := by decide
  have hdescent : baseEnd_4064463 < baseStart_4064463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064465 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 7, 3]
def baseStart_4064465 : Nat := 118140960795 + 4064465 * 2 ^ 59
def prefixEnd_4064465 : Nat := 4983230072969 + 3 ^ 40 * 4064465 * 2
def baseEnd_4064465 : Nat := 1391349432251030330463581

theorem tailTrace_4064465 : CollatzResearch.WordTrace tailWord_4064465 prefixEnd_4064465 1391349432251030330463581 := by
  unfold tailWord_4064465
  simp only [CollatzResearch.WordTrace]
  refine ⟨148243217220144935202578849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98828811480096623468385899 148243217220144935202578849)
  ·
    refine ⟨111182412915108701401934137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148243217220144935202578849 111182412915108701401934137)
    ·
      refine ⟨83386809686331526051450603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 111182412915108701401934137 83386809686331526051450603)
      ·
        refine ⟨125080214529497289077175905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83386809686331526051450603 125080214529497289077175905)
        ·
          refine ⟨93810160897122966807881929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 125080214529497289077175905 93810160897122966807881929)
          ·
            refine ⟨70357620672842225105911447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93810160897122966807881929 70357620672842225105911447)
            ·
              refine ⟨105536431009263337658867171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70357620672842225105911447 105536431009263337658867171)
              ·
                refine ⟨158304646513895006488300757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 105536431009263337658867171 158304646513895006488300757)
                ·
                  refine ⟨3710265152669414214569549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 158304646513895006488300757 3710265152669414214569549)
                  ·
                    refine ⟨1391349432251030330463581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3710265152669414214569549 1391349432251030330463581)
                    ·
                      rfl

theorem cell22_4064465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7, 3].length) (baseStart_4064465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064465 prefixEnd_4064465 := by exact prefixLift 4064465
  have htrace : WordTrace (prefixWord ++ tailWord_4064465) baseStart_4064465 baseEnd_4064465 := by
    simpa [prefixWord, tailWord_4064465, baseEnd_4064465] using wordTrace_append hprefix tailTrace_4064465
  have hstable : (prefixWord ++ tailWord_4064465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064465).length < 2 ^ (prefixWord ++ tailWord_4064465).sum := by decide
  have hdescent : baseEnd_4064465 < baseStart_4064465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064516 : List Nat := [2, 3, 2, 2, 2, 1, 3, 3, 1, 3]
def baseStart_4064516 : Nat := 118140960795 + 4064516 * 2 ^ 59
def prefixEnd_4064516 : Nat := 4983230072969 + 3 ^ 40 * 4064516 * 2
def baseEnd_4064516 : Nat := 1391366890593283197438425

theorem tailTrace_4064516 : CollatzResearch.WordTrace tailWord_4064516 prefixEnd_4064516 1391366890593283197438425 := by
  unfold tailWord_4064516
  simp only [CollatzResearch.WordTrace]
  refine ⟨74122538671480085456342701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98830051561973447275123601 74122538671480085456342701)
  ·
    refine ⟨27795952001805032046128513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74122538671480085456342701 27795952001805032046128513)
    ·
      refine ⟨20846964001353774034596385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27795952001805032046128513 20846964001353774034596385)
      ·
        refine ⟨15635223001015330525947289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20846964001353774034596385 15635223001015330525947289)
        ·
          refine ⟨11726417250761497894460467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15635223001015330525947289 11726417250761497894460467)
          ·
            refine ⟨17589625876142246841690701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11726417250761497894460467 17589625876142246841690701)
            ·
              refine ⟨6596109703553342565634013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17589625876142246841690701 6596109703553342565634013)
              ·
                refine ⟨2473541138832503462112755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6596109703553342565634013 2473541138832503462112755)
                ·
                  refine ⟨3710311708248755193169133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473541138832503462112755 3710311708248755193169133)
                  ·
                    refine ⟨1391366890593283197438425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3710311708248755193169133 1391366890593283197438425)
                    ·
                      rfl

theorem cell22_4064516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_4064516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064516 prefixEnd_4064516 := by exact prefixLift 4064516
  have htrace : WordTrace (prefixWord ++ tailWord_4064516) baseStart_4064516 baseEnd_4064516 := by
    simpa [prefixWord, tailWord_4064516, baseEnd_4064516] using wordTrace_append hprefix tailTrace_4064516
  have hstable : (prefixWord ++ tailWord_4064516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064516).length < 2 ^ (prefixWord ++ tailWord_4064516).sum := by decide
  have hdescent : baseEnd_4064516 < baseStart_4064516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064546 : List Nat := [3, 3, 1, 1, 4, 2, 2, 1, 5]
def baseStart_4064546 : Nat := 118140960795 + 4064546 * 2 ^ 59
def prefixEnd_4064546 : Nat := 4983230072969 + 3 ^ 40 * 4064546 * 2
def baseEnd_4064546 : Nat := 463792386735457706396111

theorem tailTrace_4064546 : CollatzResearch.WordTrace tailWord_4064546 prefixEnd_4064546 463792386735457706396111 := by
  unfold tailWord_4064546
  simp only [CollatzResearch.WordTrace]
  refine ⟨37061542883212871509069373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98830781021900990690851661 37061542883212871509069373)
  ·
    refine ⟨13898078581204826815901015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 37061542883212871509069373 13898078581204826815901015)
    ·
      refine ⟨20847117871807240223851523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13898078581204826815901015 20847117871807240223851523)
      ·
        refine ⟨31270676807710860335777285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20847117871807240223851523 31270676807710860335777285)
        ·
          refine ⟨5863251901445786312958241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31270676807710860335777285 5863251901445786312958241)
          ·
            refine ⟨4397438926084339734718681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5863251901445786312958241 4397438926084339734718681)
            ·
              refine ⟨3298079194563254801039011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4397438926084339734718681 3298079194563254801039011)
              ·
                refine ⟨4947118791844882201558517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3298079194563254801039011 4947118791844882201558517)
                ·
                  refine ⟨463792386735457706396111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4947118791844882201558517 463792386735457706396111)
                  ·
                    rfl

theorem cell22_4064546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_4064546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064546 prefixEnd_4064546 := by exact prefixLift 4064546
  have htrace : WordTrace (prefixWord ++ tailWord_4064546) baseStart_4064546 baseEnd_4064546 := by
    simpa [prefixWord, tailWord_4064546, baseEnd_4064546] using wordTrace_append hprefix tailTrace_4064546
  have hstable : (prefixWord ++ tailWord_4064546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064546).length < 2 ^ (prefixWord ++ tailWord_4064546).sum := by decide
  have hdescent : baseEnd_4064546 < baseStart_4064546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064572 : List Nat := [2, 2, 2, 2, 1, 4, 1, 2, 1, 5]
def baseStart_4064572 : Nat := 118140960795 + 4064572 * 2 ^ 59
def prefixEnd_4064572 : Nat := 4983230072969 + 3 ^ 40 * 4064572 * 2
def baseEnd_4064572 : Nat := 1391386060537717718038253

theorem tailTrace_4064572 : CollatzResearch.WordTrace tailWord_4064572 prefixEnd_4064572 1391386060537717718038253 := by
  unfold tailWord_4064572
  simp only [CollatzResearch.WordTrace]
  refine ⟨74123559915378646238361985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98831413220504861651149313 74123559915378646238361985)
  ·
    refine ⟨55592669936533984678771489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74123559915378646238361985 55592669936533984678771489)
    ·
      refine ⟨41694502452400488509078617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55592669936533984678771489 41694502452400488509078617)
      ·
        refine ⟨31270876839300366381808963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41694502452400488509078617 31270876839300366381808963)
        ·
          refine ⟨46906315258950549572713445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31270876839300366381808963 46906315258950549572713445)
          ·
            refine ⟨8794934111053228044883771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46906315258950549572713445 8794934111053228044883771)
            ·
              refine ⟨13192401166579842067325657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8794934111053228044883771 13192401166579842067325657)
              ·
                refine ⟨9894300874934881550494243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13192401166579842067325657 9894300874934881550494243)
                ·
                  refine ⟨14841451312402322325741365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9894300874934881550494243 14841451312402322325741365)
                  ·
                    refine ⟨1391386060537717718038253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14841451312402322325741365 1391386060537717718038253)
                    ·
                      rfl

theorem cell22_4064572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_4064572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064572 prefixEnd_4064572 := by exact prefixLift 4064572
  have htrace : WordTrace (prefixWord ++ tailWord_4064572) baseStart_4064572 baseEnd_4064572 := by
    simpa [prefixWord, tailWord_4064572, baseEnd_4064572] using wordTrace_append hprefix tailTrace_4064572
  have hstable : (prefixWord ++ tailWord_4064572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064572).length < 2 ^ (prefixWord ++ tailWord_4064572).sum := by decide
  have hdescent : baseEnd_4064572 < baseStart_4064572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064574 : List Nat := [4, 2, 1, 2, 1, 1, 2, 5, 4]
def baseStart_4064574 : Nat := 118140960795 + 4064574 * 2 ^ 59
def prefixEnd_4064574 : Nat := 4983230072969 + 3 ^ 40 * 4064574 * 2
def baseEnd_4064574 : Nat := 463795581726196793162749

theorem tailTrace_4064574 : CollatzResearch.WordTrace tailWord_4064574 prefixEnd_4064574 463795581726196793162749 := by
  unfold tailWord_4064574
  simp only [CollatzResearch.WordTrace]
  refine ⟨18530899097093755852287097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98831461851166697878864517 18530899097093755852287097)
  ·
    refine ⟨13898174322820316889215323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18530899097093755852287097 13898174322820316889215323)
    ·
      refine ⟨20847261484230475333822985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13898174322820316889215323 20847261484230475333822985)
      ·
        refine ⟨15635446113172856500367239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20847261484230475333822985 15635446113172856500367239)
        ·
          refine ⟨23453169169759284750550859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15635446113172856500367239 23453169169759284750550859)
          ·
            refine ⟨35179753754638927125826289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23453169169759284750550859 35179753754638927125826289)
            ·
              refine ⟨26384815315979195344369717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35179753754638927125826289 26384815315979195344369717)
              ·
                refine ⟨2473576435873049563534661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 26384815315979195344369717 2473576435873049563534661)
                ·
                  refine ⟨463795581726196793162749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2473576435873049563534661 463795581726196793162749)
                  ·
                    rfl

theorem cell22_4064574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_4064574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064574 prefixEnd_4064574 := by exact prefixLift 4064574
  have htrace : WordTrace (prefixWord ++ tailWord_4064574) baseStart_4064574 baseEnd_4064574 := by
    simpa [prefixWord, tailWord_4064574, baseEnd_4064574] using wordTrace_append hprefix tailTrace_4064574
  have hstable : (prefixWord ++ tailWord_4064574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064574).length < 2 ^ (prefixWord ++ tailWord_4064574).sum := by decide
  have hdescent : baseEnd_4064574 < baseStart_4064574 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064647 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 7]
def baseStart_4064647 : Nat := 118140960795 + 4064647 * 2 ^ 59
def prefixEnd_4064647 : Nat := 4983230072969 + 3 ^ 40 * 4064647 * 2
def baseEnd_4064647 : Nat := 463803911523480840804341

theorem tailTrace_4064647 : CollatzResearch.WordTrace tailWord_4064647 prefixEnd_4064647 463803911523480840804341 := by
  unfold tailWord_4064647
  simp only [CollatzResearch.WordTrace]
  refine ⟨148249855305485580285704195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98833236870323720190469463 148249855305485580285704195)
  ·
    refine ⟨222374782958228370428556293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148249855305485580285704195 222374782958228370428556293)
    ·
      refine ⟨41695271804667819455354305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 222374782958228370428556293 41695271804667819455354305)
      ·
        refine ⟨31271453853500864591515729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41695271804667819455354305 31271453853500864591515729)
        ·
          refine ⟨23453590390125648443636797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31271453853500864591515729 23453590390125648443636797)
          ·
            refine ⟨8795096396297118166363799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23453590390125648443636797 8795096396297118166363799)
            ·
              refine ⟨13192644594445677249545699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8795096396297118166363799 13192644594445677249545699)
              ·
                refine ⟨19788966891668515874318549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13192644594445677249545699 19788966891668515874318549)
                ·
                  refine ⟨463803911523480840804341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19788966891668515874318549 463803911523480840804341)
                  ·
                    rfl

theorem cell22_4064647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 7].length) (baseStart_4064647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064647 prefixEnd_4064647 := by exact prefixLift 4064647
  have htrace : WordTrace (prefixWord ++ tailWord_4064647) baseStart_4064647 baseEnd_4064647 := by
    simpa [prefixWord, tailWord_4064647, baseEnd_4064647] using wordTrace_append hprefix tailTrace_4064647
  have hstable : (prefixWord ++ tailWord_4064647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064647).length < 2 ^ (prefixWord ++ tailWord_4064647).sum := by decide
  have hdescent : baseEnd_4064647 < baseStart_4064647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064685 : List Nat := [1, 5, 2, 2, 1, 3, 1, 3, 1, 3]
def baseStart_4064685 : Nat := 118140960795 + 4064685 * 2 ^ 59
def prefixEnd_4064685 : Nat := 4983230072969 + 3 ^ 40 * 4064685 * 2
def baseEnd_4064685 : Nat := 1391424742747023089962907

theorem tailTrace_4064685 : CollatzResearch.WordTrace tailWord_4064685 prefixEnd_4064685 1391424742747023089962907 := by
  unfold tailWord_4064685
  simp only [CollatzResearch.WordTrace]
  refine ⟨148251241279347912775587509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98834160852898608517058339 148251241279347912775587509)
  ·
    refine ⟨13898553869938866822711329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148251241279347912775587509 13898553869938866822711329)
    ·
      refine ⟨10423915402454150117033497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13898553869938866822711329 10423915402454150117033497)
      ·
        refine ⟨7817936551840612587775123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10423915402454150117033497 7817936551840612587775123)
        ·
          refine ⟨11726904827760918881662685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7817936551840612587775123 11726904827760918881662685)
          ·
            refine ⟨4397589310410344580623507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11726904827760918881662685 4397589310410344580623507)
            ·
              refine ⟨6596383965615516870935261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397589310410344580623507 6596383965615516870935261)
              ·
                refine ⟨2473643987105818826600723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6596383965615516870935261 2473643987105818826600723)
                ·
                  refine ⟨3710465980658728239901085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473643987105818826600723 3710465980658728239901085)
                  ·
                    refine ⟨1391424742747023089962907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3710465980658728239901085 1391424742747023089962907)
                    ·
                      rfl

theorem cell22_4064685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_4064685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064685 prefixEnd_4064685 := by exact prefixLift 4064685
  have htrace : WordTrace (prefixWord ++ tailWord_4064685) baseStart_4064685 baseEnd_4064685 := by
    simpa [prefixWord, tailWord_4064685, baseEnd_4064685] using wordTrace_append hprefix tailTrace_4064685
  have hstable : (prefixWord ++ tailWord_4064685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064685).length < 2 ^ (prefixWord ++ tailWord_4064685).sum := by decide
  have hdescent : baseEnd_4064685 < baseStart_4064685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064737 : List Nat := [1, 2, 3, 1, 2, 3, 2, 8]
def baseStart_4064737 : Nat := 118140960795 + 4064737 * 2 ^ 59
def prefixEnd_4064737 : Nat := 4983230072969 + 3 ^ 40 * 4064737 * 2
def baseEnd_4064737 : Nat := 154604727045523587518083

theorem tailTrace_4064737 : CollatzResearch.WordTrace tailWord_4064737 prefixEnd_4064737 154604727045523587518083 := by
  unfold tailWord_4064737
  simp only [CollatzResearch.WordTrace]
  refine ⟨148253137875159525656480465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98835425250106350437653643 148253137875159525656480465)
  ·
    refine ⟨111189853406369644242360349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148253137875159525656480465 111189853406369644242360349)
    ·
      refine ⟨41696195027388616590885131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 111189853406369644242360349 41696195027388616590885131)
      ·
        refine ⟨62544292541082924886327697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41696195027388616590885131 62544292541082924886327697)
        ·
          refine ⟨46908219405812193664745773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62544292541082924886327697 46908219405812193664745773)
          ·
            refine ⟨17590582277179572624279665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46908219405812193664745773 17590582277179572624279665)
            ·
              refine ⟨13192936707884679468209749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17590582277179572624279665 13192936707884679468209749)
              ·
                refine ⟨154604727045523587518083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13192936707884679468209749 154604727045523587518083)
                ·
                  rfl

theorem cell22_4064737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 8].length) (baseStart_4064737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064737 prefixEnd_4064737 := by exact prefixLift 4064737
  have htrace : WordTrace (prefixWord ++ tailWord_4064737) baseStart_4064737 baseEnd_4064737 := by
    simpa [prefixWord, tailWord_4064737, baseEnd_4064737] using wordTrace_append hprefix tailTrace_4064737
  have hstable : (prefixWord ++ tailWord_4064737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064737).length < 2 ^ (prefixWord ++ tailWord_4064737).sum := by decide
  have hdescent : baseEnd_4064737 < baseStart_4064737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064739 : List Nat := [1, 1, 1, 6, 2, 1, 1, 3, 2, 4]
def baseStart_4064739 : Nat := 118140960795 + 4064739 * 2 ^ 59
def prefixEnd_4064739 : Nat := 4983230072969 + 3 ^ 40 * 4064739 * 2
def baseEnd_4064739 : Nat := 1391443228050584949112741

theorem tailTrace_4064739 : CollatzResearch.WordTrace tailWord_4064739 prefixEnd_4064739 1391443228050584949112741 := by
  unfold tailWord_4064739
  simp only [CollatzResearch.WordTrace]
  refine ⟨148253210821152279998053271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98835473880768186665368847 148253210821152279998053271)
  ·
    refine ⟨222379816231728419997079907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148253210821152279998053271 222379816231728419997079907)
    ·
      refine ⟨333569724347592629995619861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222379816231728419997079907 333569724347592629995619861)
      ·
        refine ⟨15636080828793404531044681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 333569724347592629995619861 15636080828793404531044681)
        ·
          refine ⟨11727060621595053398283511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15636080828793404531044681 11727060621595053398283511)
          ·
            refine ⟨17590590932392580097425267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11727060621595053398283511 17590590932392580097425267)
            ·
              refine ⟨26385886398588870146137901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17590590932392580097425267 26385886398588870146137901)
              ·
                refine ⟨9894707399470826304801713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26385886398588870146137901 9894707399470826304801713)
                ·
                  refine ⟨7421030549603119728601285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9894707399470826304801713 7421030549603119728601285)
                  ·
                    refine ⟨1391443228050584949112741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7421030549603119728601285 1391443228050584949112741)
                    ·
                      rfl

theorem cell22_4064739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 4].length) (baseStart_4064739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064739 prefixEnd_4064739 := by exact prefixLift 4064739
  have htrace : WordTrace (prefixWord ++ tailWord_4064739) baseStart_4064739 baseEnd_4064739 := by
    simpa [prefixWord, tailWord_4064739, baseEnd_4064739] using wordTrace_append hprefix tailTrace_4064739
  have hstable : (prefixWord ++ tailWord_4064739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064739).length < 2 ^ (prefixWord ++ tailWord_4064739).sum := by decide
  have hdescent : baseEnd_4064739 < baseStart_4064739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064758 : List Nat := [5, 1, 1, 1, 2, 3, 2, 2, 2, 3]
def baseStart_4064758 : Nat := 118140960795 + 4064758 * 2 ^ 59
def prefixEnd_4064758 : Nat := 4983230072969 + 3 ^ 40 * 4064758 * 2
def baseEnd_4064758 : Nat := 1391449732138875232887683

theorem tailTrace_4064758 : CollatzResearch.WordTrace tailWord_4064758 prefixEnd_4064758 1391449732138875232887683 := by
  unfold tailWord_4064758
  simp only [CollatzResearch.WordTrace]
  refine ⟨9265868988005215390187183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 98835935872055630828663285 9265868988005215390187183)
  ·
    refine ⟨13898803482007823085280775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9265868988005215390187183 13898803482007823085280775)
    ·
      refine ⟨20848205223011734627921163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13898803482007823085280775 20848205223011734627921163)
      ·
        refine ⟨31272307834517601941881745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20848205223011734627921163 31272307834517601941881745)
        ·
          refine ⟨23454230875888201456411309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31272307834517601941881745 23454230875888201456411309)
          ·
            refine ⟨8795336578458075546154241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23454230875888201456411309 8795336578458075546154241)
            ·
              refine ⟨6596502433843556659615681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8795336578458075546154241 6596502433843556659615681)
              ·
                refine ⟨4947376825382667494711761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6596502433843556659615681 4947376825382667494711761)
                ·
                  refine ⟨3710532619037000621033821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4947376825382667494711761 3710532619037000621033821)
                  ·
                    refine ⟨1391449732138875232887683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3710532619037000621033821 1391449732138875232887683)
                    ·
                      rfl

theorem cell22_4064758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_4064758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064758 prefixEnd_4064758 := by exact prefixLift 4064758
  have htrace : WordTrace (prefixWord ++ tailWord_4064758) baseStart_4064758 baseEnd_4064758 := by
    simpa [prefixWord, tailWord_4064758, baseEnd_4064758] using wordTrace_append hprefix tailTrace_4064758
  have hstable : (prefixWord ++ tailWord_4064758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064758).length < 2 ^ (prefixWord ++ tailWord_4064758).sum := by decide
  have hdescent : baseEnd_4064758 < baseStart_4064758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064788 : List Nat := [2, 4, 3, 1, 2, 1, 3, 6]
def baseStart_4064788 : Nat := 118140960795 + 4064788 * 2 ^ 59
def prefixEnd_4064788 : Nat := 4983230072969 + 3 ^ 40 * 4064788 * 2
def baseEnd_4064788 : Nat := 154606666861329461626399

theorem tailTrace_4064788 : CollatzResearch.WordTrace tailWord_4064788 prefixEnd_4064788 154606666861329461626399 := by
  unfold tailWord_4064788
  simp only [CollatzResearch.WordTrace]
  refine ⟨74127498998987380683293509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98836665331983174244391345 74127498998987380683293509)
  ·
    refine ⟨13898906062310133878117533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 74127498998987380683293509 13898906062310133878117533)
    ·
      refine ⟨5212089773366300204294075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13898906062310133878117533 5212089773366300204294075)
      ·
        refine ⟨7818134660049450306441113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5212089773366300204294075 7818134660049450306441113)
        ·
          refine ⟨5863600995037087729830835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7818134660049450306441113 5863600995037087729830835)
          ·
            refine ⟨8795401492555631594746253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5863600995037087729830835 8795401492555631594746253)
            ·
              refine ⟨3298275559708361848029845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8795401492555631594746253 3298275559708361848029845)
              ·
                refine ⟨154606666861329461626399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3298275559708361848029845 154606666861329461626399)
                ·
                  rfl

theorem cell22_4064788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 6].length) (baseStart_4064788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064788 prefixEnd_4064788 := by exact prefixLift 4064788
  have htrace : WordTrace (prefixWord ++ tailWord_4064788) baseStart_4064788 baseEnd_4064788 := by
    simpa [prefixWord, tailWord_4064788, baseEnd_4064788] using wordTrace_append hprefix tailTrace_4064788
  have hstable : (prefixWord ++ tailWord_4064788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064788).length < 2 ^ (prefixWord ++ tailWord_4064788).sum := by decide
  have hdescent : baseEnd_4064788 < baseStart_4064788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064844 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 6]
def baseStart_4064844 : Nat := 118140960795 + 4064844 * 2 ^ 59
def prefixEnd_4064844 : Nat := 4983230072969 + 3 ^ 40 * 4064844 * 2
def baseEnd_4064844 : Nat := 463826390565466558412473

theorem tailTrace_4064844 : CollatzResearch.WordTrace tailWord_4064844 prefixEnd_4064844 463826390565466558412473 := by
  unfold tailWord_4064844
  simp only [CollatzResearch.WordTrace]
  refine ⟨74128520242885941465312793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98838026990514588620417057 74128520242885941465312793)
  ·
    refine ⟨55596390182164456098984595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74128520242885941465312793 55596390182164456098984595)
    ·
      refine ⟨83394585273246684148476893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55596390182164456098984595 83394585273246684148476893)
      ·
        refine ⟨31272969477467506555678835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 83394585273246684148476893 31272969477467506555678835)
        ·
          refine ⟨46909454216201259833518253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31272969477467506555678835 46909454216201259833518253)
          ·
            refine ⟨17591045331075472437569345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46909454216201259833518253 17591045331075472437569345)
            ·
              refine ⟨13193283998306604328177009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17591045331075472437569345 13193283998306604328177009)
              ·
                refine ⟨9894962998729953246132757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13193283998306604328177009 9894962998729953246132757)
                ·
                  refine ⟨463826390565466558412473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9894962998729953246132757 463826390565466558412473)
                  ·
                    rfl

theorem cell22_4064844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 6].length) (baseStart_4064844 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064844 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064844 prefixEnd_4064844 := by exact prefixLift 4064844
  have htrace : WordTrace (prefixWord ++ tailWord_4064844) baseStart_4064844 baseEnd_4064844 := by
    simpa [prefixWord, tailWord_4064844, baseEnd_4064844] using wordTrace_append hprefix tailTrace_4064844
  have hstable : (prefixWord ++ tailWord_4064844).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064844).length < 2 ^ (prefixWord ++ tailWord_4064844).sum := by decide
  have hdescent : baseEnd_4064844 < baseStart_4064844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064876 : List Nat := [2, 2, 1, 1, 3, 1, 1, 6, 2, 3]
def baseStart_4064876 : Nat := 118140960795 + 4064876 * 2 ^ 59
def prefixEnd_4064876 : Nat := 4983230072969 + 3 ^ 40 * 4064876 * 2
def baseEnd_4064876 : Nat := 1391490125950362258437321

theorem tailTrace_4064876 : CollatzResearch.WordTrace tailWord_4064876 prefixEnd_4064876 1391490125950362258437321 := by
  unfold tailWord_4064876
  simp only [CollatzResearch.WordTrace]
  refine ⟨74129103810827976197895241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98838805081103968263860321 74129103810827976197895241)
  ·
    refine ⟨55596827858120982148421431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74129103810827976197895241 55596827858120982148421431)
    ·
      refine ⟨83395241787181473222632147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55596827858120982148421431 83395241787181473222632147)
      ·
        refine ⟨125092862680772209833948221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83395241787181473222632147 125092862680772209833948221)
        ·
          refine ⟨46909823505289578687730583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 125092862680772209833948221 46909823505289578687730583)
          ·
            refine ⟨70364735257934368031595875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46909823505289578687730583 70364735257934368031595875)
            ·
              refine ⟨105547102886901552047393813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 70364735257934368031595875 105547102886901552047393813)
              ·
                refine ⟨4947520447823510252221585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 105547102886901552047393813 4947520447823510252221585)
                ·
                  refine ⟨3710640335867632689166189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4947520447823510252221585 3710640335867632689166189)
                  ·
                    refine ⟨1391490125950362258437321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3710640335867632689166189 1391490125950362258437321)
                    ·
                      rfl

theorem cell22_4064876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 3].length) (baseStart_4064876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064876 prefixEnd_4064876 := by exact prefixLift 4064876
  have htrace : WordTrace (prefixWord ++ tailWord_4064876) baseStart_4064876 baseEnd_4064876 := by
    simpa [prefixWord, tailWord_4064876, baseEnd_4064876] using wordTrace_append hprefix tailTrace_4064876
  have hstable : (prefixWord ++ tailWord_4064876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064876).length < 2 ^ (prefixWord ++ tailWord_4064876).sum := by decide
  have hdescent : baseEnd_4064876 < baseStart_4064876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064878 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 6]
def baseStart_4064878 : Nat := 118140960795 + 4064878 * 2 ^ 59
def prefixEnd_4064878 : Nat := 4983230072969 + 3 ^ 40 * 4064878 * 2
def baseEnd_4064878 : Nat := 463830270197078306629105

theorem tailTrace_4064878 : CollatzResearch.WordTrace tailWord_4064878 prefixEnd_4064878 463830270197078306629105 := by
  unfold tailWord_4064878
  simp only [CollatzResearch.WordTrace]
  refine ⟨18532285070956088342170411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98838853711765804491575525 18532285070956088342170411)
  ·
    refine ⟨27798427606434132513255617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18532285070956088342170411 27798427606434132513255617)
    ·
      refine ⟨20848820704825599384941713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27798427606434132513255617 20848820704825599384941713)
      ·
        refine ⟨15636615528619199538706285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20848820704825599384941713 15636615528619199538706285)
        ·
          refine ⟨5863730823232199827014857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15636615528619199538706285 5863730823232199827014857)
          ·
            refine ⟨4397798117424149870261143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5863730823232199827014857 4397798117424149870261143)
            ·
              refine ⟨6596697176136224805391715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4397798117424149870261143 6596697176136224805391715)
              ·
                refine ⟨9895045764204337208087573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6596697176136224805391715 9895045764204337208087573)
                ·
                  refine ⟨463830270197078306629105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9895045764204337208087573 463830270197078306629105)
                  ·
                    rfl

theorem cell22_4064878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_4064878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064878 prefixEnd_4064878 := by exact prefixLift 4064878
  have htrace : WordTrace (prefixWord ++ tailWord_4064878) baseStart_4064878 baseEnd_4064878 := by
    simpa [prefixWord, tailWord_4064878, baseEnd_4064878] using wordTrace_append hprefix tailTrace_4064878
  have hstable : (prefixWord ++ tailWord_4064878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064878).length < 2 ^ (prefixWord ++ tailWord_4064878).sum := by decide
  have hdescent : baseEnd_4064878 < baseStart_4064878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064889 : List Nat := [1, 2, 1, 3, 3, 1, 4, 7]
def baseStart_4064889 : Nat := 118140960795 + 4064889 * 2 ^ 59
def prefixEnd_4064889 : Nat := 4983230072969 + 3 ^ 40 * 4064889 * 2
def baseEnd_4064889 : Nat := 154610508457337173095809

theorem tailTrace_4064889 : CollatzResearch.WordTrace tailWord_4064889 prefixEnd_4064889 154610508457337173095809 := by
  unfold tailWord_4064889
  simp only [CollatzResearch.WordTrace]
  refine ⟨148258681770608855616013721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98839121180405903744009147 148258681770608855616013721)
  ·
    refine ⟨111194011327956641712010291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148258681770608855616013721 111194011327956641712010291)
    ·
      refine ⟨166791016991934962568015437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111194011327956641712010291 166791016991934962568015437)
      ·
        refine ⟨62546631371975610963005789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 166791016991934962568015437 62546631371975610963005789)
        ·
          refine ⟨23454986764490854111127171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62546631371975610963005789 23454986764490854111127171)
          ·
            refine ⟨35182480146736281166690757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23454986764490854111127171 35182480146736281166690757)
            ·
              refine ⟨6596715027513052718754517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35182480146736281166690757 6596715027513052718754517)
              ·
                refine ⟨154610508457337173095809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6596715027513052718754517 154610508457337173095809)
                ·
                  rfl

theorem cell22_4064889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 7].length) (baseStart_4064889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064889 prefixEnd_4064889 := by exact prefixLift 4064889
  have htrace : WordTrace (prefixWord ++ tailWord_4064889) baseStart_4064889 baseEnd_4064889 := by
    simpa [prefixWord, tailWord_4064889, baseEnd_4064889] using wordTrace_append hprefix tailTrace_4064889
  have hstable : (prefixWord ++ tailWord_4064889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064889).length < 2 ^ (prefixWord ++ tailWord_4064889).sum := by decide
  have hdescent : baseEnd_4064889 < baseStart_4064889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064893 : List Nat := [1, 4, 1, 1, 4, 2, 1, 3, 2, 3]
def baseStart_4064893 : Nat := 118140960795 + 4064893 * 2 ^ 59
def prefixEnd_4064893 : Nat := 4983230072969 + 3 ^ 40 * 4064893 * 2
def baseEnd_4064893 : Nat := 1391495945397779880762269

theorem tailTrace_4064893 : CollatzResearch.WordTrace tailWord_4064893 prefixEnd_4064893 1391495945397779880762269 := by
  unfold tailWord_4064893
  simp only [CollatzResearch.WordTrace]
  refine ⟨148258827662594364299159333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98839218441729576199439555 148258827662594364299159333)
  ·
    refine ⟨27798530186736443306092375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148258827662594364299159333 27798530186736443306092375)
    ·
      refine ⟨41697795280104664959138563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27798530186736443306092375 41697795280104664959138563)
      ·
        refine ⟨62546692920156997438707845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41697795280104664959138563 62546692920156997438707845)
        ·
          refine ⟨11727504922529437019757721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62546692920156997438707845 11727504922529437019757721)
          ·
            refine ⟨8795628691897077764818291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11727504922529437019757721 8795628691897077764818291)
            ·
              refine ⟨13193443037845616647227437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8795628691897077764818291 13193443037845616647227437)
              ·
                refine ⟨4947541139192106242710289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13193443037845616647227437 4947541139192106242710289)
                ·
                  refine ⟨3710655854394079682032717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4947541139192106242710289 3710655854394079682032717)
                  ·
                    refine ⟨1391495945397779880762269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3710655854394079682032717 1391495945397779880762269)
                    ·
                      rfl

theorem cell22_4064893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_4064893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064893 prefixEnd_4064893 := by exact prefixLift 4064893
  have htrace : WordTrace (prefixWord ++ tailWord_4064893) baseStart_4064893 baseEnd_4064893 := by
    simpa [prefixWord, tailWord_4064893, baseEnd_4064893] using wordTrace_append hprefix tailTrace_4064893
  have hstable : (prefixWord ++ tailWord_4064893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064893).length < 2 ^ (prefixWord ++ tailWord_4064893).sum := by decide
  have hdescent : baseEnd_4064893 < baseStart_4064893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064951 : List Nat := [1, 1, 3, 1, 5, 1, 2, 3, 5]
def baseStart_4064951 : Nat := 118140960795 + 4064951 * 2 ^ 59
def prefixEnd_4064951 : Nat := 4983230072969 + 3 ^ 40 * 4064951 * 2
def baseEnd_4064951 : Nat := 463838599994362354270697

theorem tailTrace_4064951 : CollatzResearch.WordTrace tailWord_4064951 prefixEnd_4064951 463838599994362354270697 := by
  unfold tailWord_4064951
  simp only [CollatzResearch.WordTrace]
  refine ⟨148260943096384240204770707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98840628730922826803180471 148260943096384240204770707)
  ·
    refine ⟨222391414644576360307156061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148260943096384240204770707 222391414644576360307156061)
    ·
      refine ⟨83396780491716135115183523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 222391414644576360307156061 83396780491716135115183523)
      ·
        refine ⟨125095170737574202672775285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 83396780491716135115183523 125095170737574202672775285)
        ·
          refine ⟨11727672256647581500572683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 125095170737574202672775285 11727672256647581500572683)
          ·
            refine ⟨17591508384971372250859025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11727672256647581500572683 17591508384971372250859025)
            ·
              refine ⟨13193631288728529188144269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17591508384971372250859025 13193631288728529188144269)
              ·
                refine ⟨4947611733273198445554101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13193631288728529188144269 4947611733273198445554101)
                ·
                  refine ⟨463838599994362354270697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4947611733273198445554101 463838599994362354270697)
                  ·
                    rfl

theorem cell22_4064951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 5].length) (baseStart_4064951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064951 prefixEnd_4064951 := by exact prefixLift 4064951
  have htrace : WordTrace (prefixWord ++ tailWord_4064951) baseStart_4064951 baseEnd_4064951 := by
    simpa [prefixWord, tailWord_4064951, baseEnd_4064951] using wordTrace_append hprefix tailTrace_4064951
  have hstable : (prefixWord ++ tailWord_4064951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064951).length < 2 ^ (prefixWord ++ tailWord_4064951).sum := by decide
  have hdescent : baseEnd_4064951 < baseStart_4064951 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064972 : List Nat := [2, 2, 1, 5, 2, 1, 2, 3, 1, 3]
def baseStart_4064972 : Nat := 118140960795 + 4064972 * 2 ^ 59
def prefixEnd_4064972 : Nat := 4983230072969 + 3 ^ 40 * 4064972 * 2
def baseEnd_4064972 : Nat := 1391522988712250008037027

theorem tailTrace_4064972 : CollatzResearch.WordTrace tailWord_4064972 prefixEnd_4064972 1391522988712250008037027 := by
  unfold tailWord_4064972
  simp only [CollatzResearch.WordTrace]
  refine ⟨74130854514654080395642585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98841139352872107194190113 74130854514654080395642585)
  ·
    refine ⟨55598140885990560296731939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74130854514654080395642585 55598140885990560296731939)
    ·
      refine ⟨83397211328985840445097909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55598140885990560296731939 83397211328985840445097909)
      ·
        refine ⟨7818488562092422541727929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 83397211328985840445097909 7818488562092422541727929)
        ·
          refine ⟨5863866421569316906295947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7818488562092422541727929 5863866421569316906295947)
          ·
            refine ⟨8795799632353975359443921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5863866421569316906295947 8795799632353975359443921)
            ·
              refine ⟨6596849724265481519582941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8795799632353975359443921 6596849724265481519582941)
              ·
                refine ⟨2473818646599555569843603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6596849724265481519582941 2473818646599555569843603)
                ·
                  refine ⟨3710727969899333354765405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2473818646599555569843603 3710727969899333354765405)
                  ·
                    refine ⟨1391522988712250008037027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3710727969899333354765405 1391522988712250008037027)
                    ·
                      rfl

theorem cell22_4064972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 3, 1, 3].length) (baseStart_4064972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064972 prefixEnd_4064972 := by exact prefixLift 4064972
  have htrace : WordTrace (prefixWord ++ tailWord_4064972) baseStart_4064972 baseEnd_4064972 := by
    simpa [prefixWord, tailWord_4064972, baseEnd_4064972] using wordTrace_append hprefix tailTrace_4064972
  have hstable : (prefixWord ++ tailWord_4064972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064972).length < 2 ^ (prefixWord ++ tailWord_4064972).sum := by decide
  have hdescent : baseEnd_4064972 < baseStart_4064972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4064996 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 6]
def baseStart_4064996 : Nat := 118140960795 + 4064996 * 2 ^ 59
def prefixEnd_4064996 : Nat := 4983230072969 + 3 ^ 40 * 4064996 * 2
def baseEnd_4064996 : Nat := 463843734800907315145651

theorem tailTrace_4064996 : CollatzResearch.WordTrace tailWord_4064996 prefixEnd_4064996 463843734800907315145651 := by
  unfold tailWord_4064996
  simp only [CollatzResearch.WordTrace]
  refine ⟨74131292190610606445079421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98841722920814141926772561 74131292190610606445079421)
  ·
    refine ⟨27799234571478977416904783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74131292190610606445079421 27799234571478977416904783)
    ·
      refine ⟨41698851857218466125357175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27799234571478977416904783 41698851857218466125357175)
      ·
        refine ⟨62548277785827699188035763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41698851857218466125357175 62548277785827699188035763)
        ·
          refine ⟨93822416678741548782053645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62548277785827699188035763 93822416678741548782053645)
          ·
            refine ⟨35183406254528080793270117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93822416678741548782053645 35183406254528080793270117)
            ·
              refine ⟨6596888672724015148738147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35183406254528080793270117 6596888672724015148738147)
              ·
                refine ⟨9895333009086022723107221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6596888672724015148738147 9895333009086022723107221)
                ·
                  refine ⟨463843734800907315145651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9895333009086022723107221 463843734800907315145651)
                  ·
                    rfl

theorem cell22_4064996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 6].length) (baseStart_4064996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4064996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4064996 prefixEnd_4064996 := by exact prefixLift 4064996
  have htrace : WordTrace (prefixWord ++ tailWord_4064996) baseStart_4064996 baseEnd_4064996 := by
    simpa [prefixWord, tailWord_4064996, baseEnd_4064996] using wordTrace_append hprefix tailTrace_4064996
  have hstable : (prefixWord ++ tailWord_4064996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4064996).length < 2 ^ (prefixWord ++ tailWord_4064996).sum := by decide
  have hdescent : baseEnd_4064996 < baseStart_4064996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4064996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065011 : List Nat := [1, 1, 1, 2, 2, 3, 5, 1, 1, 5]
def baseStart_4065011 : Nat := 118140960795 + 4065011 * 2 ^ 59
def prefixEnd_4065011 : Nat := 4983230072969 + 3 ^ 40 * 4065011 * 2
def baseEnd_4065011 : Nat := 1391536339209266906311907

theorem tailTrace_4065011 : CollatzResearch.WordTrace tailWord_4065011 prefixEnd_4065011 1391536339209266906311907 := by
  unfold tailWord_4065011
  simp only [CollatzResearch.WordTrace]
  refine ⟨148263131476166870451954887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98842087650777913634636591 148263131476166870451954887)
  ·
    refine ⟨222394697214250305677932331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148263131476166870451954887 222394697214250305677932331)
    ·
      refine ⟨333592045821375458516898497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222394697214250305677932331 333592045821375458516898497)
      ·
        refine ⟨250194034366031593887673873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 333592045821375458516898497 250194034366031593887673873)
        ·
          refine ⟨187645525774523695415755405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250194034366031593887673873 187645525774523695415755405)
          ·
            refine ⟨70367072165446385780908277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 187645525774523695415755405 70367072165446385780908277)
            ·
              refine ⟨6596913015510598666960151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 70367072165446385780908277 6596913015510598666960151)
              ·
                refine ⟨9895369523265898000440227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6596913015510598666960151 9895369523265898000440227)
                ·
                  refine ⟨14843054284898847000660341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9895369523265898000440227 14843054284898847000660341)
                  ·
                    refine ⟨1391536339209266906311907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14843054284898847000660341 1391536339209266906311907)
                    ·
                      rfl

theorem cell22_4065011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 1, 1, 5].length) (baseStart_4065011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065011 prefixEnd_4065011 := by exact prefixLift 4065011
  have htrace : WordTrace (prefixWord ++ tailWord_4065011) baseStart_4065011 baseEnd_4065011 := by
    simpa [prefixWord, tailWord_4065011, baseEnd_4065011] using wordTrace_append hprefix tailTrace_4065011
  have hstable : (prefixWord ++ tailWord_4065011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065011).length < 2 ^ (prefixWord ++ tailWord_4065011).sum := by decide
  have hdescent : baseEnd_4065011 < baseStart_4065011 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065024 : List Nat := [2, 1, 1, 2, 1, 1, 2, 12]
def baseStart_4065024 : Nat := 118140960795 + 4065024 * 2 ^ 59
def prefixEnd_4065024 : Nat := 4983230072969 + 3 ^ 40 * 4065024 * 2
def baseEnd_4065024 : Nat := 154615643263882133970763

theorem tailTrace_4065024 : CollatzResearch.WordTrace tailWord_4065024 prefixEnd_4065024 154615643263882133970763 := by
  unfold tailWord_4065024
  simp only [CollatzResearch.WordTrace]
  refine ⟨74131802812559886836089063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98842403750079849114785417 74131802812559886836089063)
  ·
    refine ⟨111197704218839830254133595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74131802812559886836089063 111197704218839830254133595)
    ·
      refine ⟨166796556328259745381200393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111197704218839830254133595 166796556328259745381200393)
      ·
        refine ⟨125097417246194809035900295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 166796556328259745381200393 125097417246194809035900295)
        ·
          refine ⟨187646125869292213553850443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 125097417246194809035900295 187646125869292213553850443)
          ·
            refine ⟨281469188803938320330775665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187646125869292213553850443 281469188803938320330775665)
            ·
              refine ⟨211101891602953740248081749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281469188803938320330775665 211101891602953740248081749)
              ·
                refine ⟨154615643263882133970763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 211101891602953740248081749 154615643263882133970763)
                ·
                  rfl

theorem cell22_4065024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 12].length) (baseStart_4065024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065024 prefixEnd_4065024 := by exact prefixLift 4065024
  have htrace : WordTrace (prefixWord ++ tailWord_4065024) baseStart_4065024 baseEnd_4065024 := by
    simpa [prefixWord, tailWord_4065024, baseEnd_4065024] using wordTrace_append hprefix tailTrace_4065024
  have hstable : (prefixWord ++ tailWord_4065024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065024).length < 2 ^ (prefixWord ++ tailWord_4065024).sum := by decide
  have hdescent : baseEnd_4065024 < baseStart_4065024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065028 : List Nat := [2, 3, 2, 2, 1, 2, 1, 2, 4, 3]
def baseStart_4065028 : Nat := 118140960795 + 4065028 * 2 ^ 59
def prefixEnd_4065028 : Nat := 4983230072969 + 3 ^ 40 * 4065028 * 2
def baseEnd_4065028 : Nat := 1391542158656684528636855

theorem tailTrace_4065028 : CollatzResearch.WordTrace tailWord_4065028 prefixEnd_4065028 1391542158656684528636855 := by
  unfold tailWord_4065028
  simp only [CollatzResearch.WordTrace]
  refine ⟨74131875758552641177661869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98842501011403521570215825 74131875758552641177661869)
  ·
    refine ⟨27799453409457240441623201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 74131875758552641177661869 27799453409457240441623201)
    ·
      refine ⟨20849590057092930331217401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27799453409457240441623201 20849590057092930331217401)
      ·
        refine ⟨15637192542819697748413051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20849590057092930331217401 15637192542819697748413051)
        ·
          refine ⟨23455788814229546622619577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15637192542819697748413051 23455788814229546622619577)
          ·
            refine ⟨17591841610672159966964683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23455788814229546622619577 17591841610672159966964683)
            ·
              refine ⟨26387762416008239950447025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17591841610672159966964683 26387762416008239950447025)
              ·
                refine ⟨19790821812006179962835269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26387762416008239950447025 19790821812006179962835269)
                ·
                  refine ⟨3710779089751158743031613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19790821812006179962835269 3710779089751158743031613)
                  ·
                    refine ⟨1391542158656684528636855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3710779089751158743031613 1391542158656684528636855)
                    ·
                      rfl

theorem cell22_4065028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_4065028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065028 prefixEnd_4065028 := by exact prefixLift 4065028
  have htrace : WordTrace (prefixWord ++ tailWord_4065028) baseStart_4065028 baseEnd_4065028 := by
    simpa [prefixWord, tailWord_4065028, baseEnd_4065028] using wordTrace_append hprefix tailTrace_4065028
  have hstable : (prefixWord ++ tailWord_4065028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065028).length < 2 ^ (prefixWord ++ tailWord_4065028).sum := by decide
  have hdescent : baseEnd_4065028 < baseStart_4065028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065133 : List Nat := [1, 5, 1, 1, 1, 1, 4, 1, 3, 4]
def baseStart_4065133 : Nat := 118140960795 + 4065133 * 2 ^ 59
def prefixEnd_4065133 : Nat := 4983230072969 + 3 ^ 40 * 4065133 * 2
def baseEnd_4065133 : Nat := 1391578102302499254761533

theorem tailTrace_4065133 : CollatzResearch.WordTrace tailWord_4065133 prefixEnd_4065133 1391578102302499254761533 := by
  unfold tailWord_4065133
  simp only [CollatzResearch.WordTrace]
  refine ⟨148267581181724885287896053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98845054121149923525264035 148267581181724885287896053)
  ·
    refine ⟨13900085735786707995740255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 148267581181724885287896053 13900085735786707995740255)
    ·
      refine ⟨20850128603680061993610383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13900085735786707995740255 20850128603680061993610383)
      ·
        refine ⟨31275192905520092990415575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20850128603680061993610383 31275192905520092990415575)
        ·
          refine ⟨46912789358280139485623363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31275192905520092990415575 46912789358280139485623363)
          ·
            refine ⟨70369184037420209228435045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46912789358280139485623363 70369184037420209228435045)
            ·
              refine ⟨13194222007016289230331571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 70369184037420209228435045 13194222007016289230331571)
              ·
                refine ⟨19791333010524433845497357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13194222007016289230331571 19791333010524433845497357)
                ·
                  refine ⟨7421749878946662692061509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19791333010524433845497357 7421749878946662692061509)
                  ·
                    refine ⟨1391578102302499254761533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7421749878946662692061509 1391578102302499254761533)
                    ·
                      rfl

theorem cell22_4065133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_4065133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065133 prefixEnd_4065133 := by exact prefixLift 4065133
  have htrace : WordTrace (prefixWord ++ tailWord_4065133) baseStart_4065133 baseEnd_4065133 := by
    simpa [prefixWord, tailWord_4065133, baseEnd_4065133] using wordTrace_append hprefix tailTrace_4065133
  have hstable : (prefixWord ++ tailWord_4065133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065133).length < 2 ^ (prefixWord ++ tailWord_4065133).sum := by decide
  have hdescent : baseEnd_4065133 < baseStart_4065133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065178 : List Nat := [3, 1, 1, 4, 2, 1, 1, 2, 1, 6]
def baseStart_4065178 : Nat := 118140960795 + 4065178 * 2 ^ 59
def prefixEnd_4065178 : Nat := 4983230072969 + 3 ^ 40 * 4065178 * 2
def baseEnd_4065178 : Nat := 1391593506722134137386395

theorem tailTrace_4065178 : CollatzResearch.WordTrace tailWord_4065178 prefixEnd_4065178 1391593506722134137386395 := by
  unfold tailWord_4065178
  simp only [CollatzResearch.WordTrace]
  refine ⟨37067305616640464493321047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98846148311041238648856125 37067305616640464493321047)
  ·
    refine ⟨55600958424960696739981571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37067305616640464493321047 55600958424960696739981571)
    ·
      refine ⟨83401437637441045109972357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55600958424960696739981571 83401437637441045109972357)
      ·
        refine ⟨15637769557020195958119817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 83401437637441045109972357 15637769557020195958119817)
        ·
          refine ⟨11728327167765146968589863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15637769557020195958119817 11728327167765146968589863)
          ·
            refine ⟨17592490751647720452884795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11728327167765146968589863 17592490751647720452884795)
            ·
              refine ⟨26388736127471580679327193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17592490751647720452884795 26388736127471580679327193)
              ·
                refine ⟨19791552095603685509495395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26388736127471580679327193 19791552095603685509495395)
                ·
                  refine ⟨29687328143405528264243093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19791552095603685509495395 29687328143405528264243093)
                  ·
                    refine ⟨1391593506722134137386395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29687328143405528264243093 1391593506722134137386395)
                    ·
                      rfl

theorem cell22_4065178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_4065178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065178 prefixEnd_4065178 := by exact prefixLift 4065178
  have htrace : WordTrace (prefixWord ++ tailWord_4065178) baseStart_4065178 baseEnd_4065178 := by
    simpa [prefixWord, tailWord_4065178, baseEnd_4065178] using wordTrace_append hprefix tailTrace_4065178
  have hstable : (prefixWord ++ tailWord_4065178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065178).length < 2 ^ (prefixWord ++ tailWord_4065178).sum := by decide
  have hdescent : baseEnd_4065178 < baseStart_4065178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065180 : List Nat := [2, 2, 3, 3, 1, 1, 3, 1, 1, 5]
def baseStart_4065180 : Nat := 118140960795 + 4065180 * 2 ^ 59
def prefixEnd_4065180 : Nat := 4983230072969 + 3 ^ 40 * 4065180 * 2
def baseEnd_4065180 : Nat := 1391594191363006798836389

theorem tailTrace_4065180 : CollatzResearch.WordTrace tailWord_4065180 prefixEnd_4065180 1391594191363006798836389 := by
  unfold tailWord_4065180
  simp only [CollatzResearch.WordTrace]
  refine ⟨74134647706277306157428497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98846196941703074876571329 74134647706277306157428497)
  ·
    refine ⟨55600985779707979618071373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74134647706277306157428497 55600985779707979618071373)
    ·
      refine ⟨20850369667390492356776765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55600985779707979618071373 20850369667390492356776765)
      ·
        refine ⟨7818888625271434633791287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20850369667390492356776765 7818888625271434633791287)
        ·
          refine ⟨11728332937907151950686931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7818888625271434633791287 11728332937907151950686931)
          ·
            refine ⟨17592499406860727926030397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11728332937907151950686931 17592499406860727926030397)
            ·
              refine ⟨6597187277572772972261399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17592499406860727926030397 6597187277572772972261399)
              ·
                refine ⟨9895780916359159458392099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6597187277572772972261399 9895780916359159458392099)
                ·
                  refine ⟨14843671374538739187588149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9895780916359159458392099 14843671374538739187588149)
                  ·
                    refine ⟨1391594191363006798836389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14843671374538739187588149 1391594191363006798836389)
                    ·
                      rfl

theorem cell22_4065180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_4065180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065180 prefixEnd_4065180 := by exact prefixLift 4065180
  have htrace : WordTrace (prefixWord ++ tailWord_4065180) baseStart_4065180 baseEnd_4065180 := by
    simpa [prefixWord, tailWord_4065180, baseEnd_4065180] using wordTrace_append hprefix tailTrace_4065180
  have hstable : (prefixWord ++ tailWord_4065180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065180).length < 2 ^ (prefixWord ++ tailWord_4065180).sum := by decide
  have hdescent : baseEnd_4065180 < baseStart_4065180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065212 : List Nat := [2, 2, 2, 5, 1, 1, 1, 2, 2, 4]
def baseStart_4065212 : Nat := 118140960795 + 4065212 * 2 ^ 59
def prefixEnd_4065212 : Nat := 4983230072969 + 3 ^ 40 * 4065212 * 2
def baseEnd_4065212 : Nat := 1391605145616969382036291

theorem tailTrace_4065212 : CollatzResearch.WordTrace tailWord_4065212 prefixEnd_4065212 1391605145616969382036291 := by
  unfold tailWord_4065212
  simp only [CollatzResearch.WordTrace]
  refine ⟨74135231274219340890010945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98846975032292454520014593 74135231274219340890010945)
  ·
    refine ⟨55601423455664505667508209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 74135231274219340890010945 55601423455664505667508209)
    ·
      refine ⟨41701067591748379250631157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55601423455664505667508209 41701067591748379250631157)
      ·
        refine ⟨3909475086726410554746671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 41701067591748379250631157 3909475086726410554746671)
        ·
          refine ⟨5864212630089615832120007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3909475086726410554746671 5864212630089615832120007)
          ·
            refine ⟨8796318945134423748180011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864212630089615832120007 8796318945134423748180011)
            ·
              refine ⟨13194478417701635622270017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8796318945134423748180011 13194478417701635622270017)
              ·
                refine ⟨9895858813276226716702513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13194478417701635622270017 9895858813276226716702513)
                ·
                  refine ⟨7421894109957170037526885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9895858813276226716702513 7421894109957170037526885)
                  ·
                    refine ⟨1391605145616969382036291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7421894109957170037526885 1391605145616969382036291)
                    ·
                      rfl

theorem cell22_4065212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_4065212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065212 prefixEnd_4065212 := by exact prefixLift 4065212
  have htrace : WordTrace (prefixWord ++ tailWord_4065212) baseStart_4065212 baseEnd_4065212 := by
    simpa [prefixWord, tailWord_4065212, baseEnd_4065212] using wordTrace_append hprefix tailTrace_4065212
  have hstable : (prefixWord ++ tailWord_4065212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065212).length < 2 ^ (prefixWord ++ tailWord_4065212).sum := by decide
  have hdescent : baseEnd_4065212 < baseStart_4065212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065315 : List Nat := [1, 1, 1, 4, 3, 1, 2, 2, 4, 3]
def baseStart_4065315 : Nat := 118140960795 + 4065315 * 2 ^ 59
def prefixEnd_4065315 : Nat := 4983230072969 + 3 ^ 40 * 4065315 * 2
def baseEnd_4065315 : Nat := 1391640404621911446710975

theorem tailTrace_4065315 : CollatzResearch.WordTrace tailWord_4065315 prefixEnd_4065315 1391640404621911446710975 := by
  unfold tailWord_4065315
  simp only [CollatzResearch.WordTrace]
  refine ⟨148274219267065530371021399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98849479511377020247347599 148274219267065530371021399)
  ·
    refine ⟨222411328900598295556532099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148274219267065530371021399 222411328900598295556532099)
    ·
      refine ⟨333616993350897443334798149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222411328900598295556532099 333616993350897443334798149)
      ·
        refine ⟨62553186253293270625274653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 333616993350897443334798149 62553186253293270625274653)
        ·
          refine ⟨23457444844984976484477995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62553186253293270625274653 23457444844984976484477995)
          ·
            refine ⟨35186167267477464726716993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23457444844984976484477995 35186167267477464726716993)
            ·
              refine ⟨26389625450608098545037745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35186167267477464726716993 26389625450608098545037745)
              ·
                refine ⟨19792219087956073908778309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26389625450608098545037745 19792219087956073908778309)
                ·
                  refine ⟨3711041078991763857895933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19792219087956073908778309 3711041078991763857895933)
                  ·
                    refine ⟨1391640404621911446710975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3711041078991763857895933 1391640404621911446710975)
                    ·
                      rfl

theorem cell22_4065315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 2, 4, 3].length) (baseStart_4065315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065315 prefixEnd_4065315 := by exact prefixLift 4065315
  have htrace : WordTrace (prefixWord ++ tailWord_4065315) baseStart_4065315 baseEnd_4065315 := by
    simpa [prefixWord, tailWord_4065315, baseEnd_4065315] using wordTrace_append hprefix tailTrace_4065315
  have hstable : (prefixWord ++ tailWord_4065315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065315).length < 2 ^ (prefixWord ++ tailWord_4065315).sum := by decide
  have hdescent : baseEnd_4065315 < baseStart_4065315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065317 : List Nat := [1, 3, 1, 2, 2, 4, 2, 3, 4]
def baseStart_4065317 : Nat := 118140960795 + 4065317 * 2 ^ 59
def prefixEnd_4065317 : Nat := 4983230072969 + 3 ^ 40 * 4065317 * 2
def baseEnd_4065317 : Nat := 463880363087594702720323

theorem tailTrace_4065317 : CollatzResearch.WordTrace tailWord_4065317 prefixEnd_4065317 463880363087594702720323 := by
  unfold tailWord_4065317
  simp only [CollatzResearch.WordTrace]
  refine ⟨148274292213058284712594205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98849528142038856475062803 148274292213058284712594205)
  ·
    refine ⟨55602859579896856767222827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 148274292213058284712594205 55602859579896856767222827)
    ·
      refine ⟨83404289369845285150834241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55602859579896856767222827 83404289369845285150834241)
      ·
        refine ⟨62553217027383963863125681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 83404289369845285150834241 62553217027383963863125681)
        ·
          refine ⟨46914912770537972897344261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62553217027383963863125681 46914912770537972897344261)
          ·
            refine ⟨8796546144475869918252049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46914912770537972897344261 8796546144475869918252049)
            ·
              refine ⟨6597409608356902438689037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8796546144475869918252049 6597409608356902438689037)
              ·
                refine ⟨2474028603133838414508389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6597409608356902438689037 2474028603133838414508389)
                ·
                  refine ⟨463880363087594702720323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2474028603133838414508389 463880363087594702720323)
                  ·
                    rfl

theorem cell22_4065317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 4].length) (baseStart_4065317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065317 prefixEnd_4065317 := by exact prefixLift 4065317
  have htrace : WordTrace (prefixWord ++ tailWord_4065317) baseStart_4065317 baseEnd_4065317 := by
    simpa [prefixWord, tailWord_4065317, baseEnd_4065317] using wordTrace_append hprefix tailTrace_4065317
  have hstable : (prefixWord ++ tailWord_4065317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065317).length < 2 ^ (prefixWord ++ tailWord_4065317).sum := by decide
  have hdescent : baseEnd_4065317 < baseStart_4065317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065319 : List Nat := [1, 1, 7, 1, 2, 1, 1, 3, 1, 4]
def baseStart_4065319 : Nat := 118140960795 + 4065319 * 2 ^ 59
def prefixEnd_4065319 : Nat := 4983230072969 + 3 ^ 40 * 4065319 * 2
def baseEnd_4065319 : Nat := 1391641773903656769610963

theorem tailTrace_4065319 : CollatzResearch.WordTrace tailWord_4065319 prefixEnd_4065319 1391641773903656769610963 := by
  unfold tailWord_4065319
  simp only [CollatzResearch.WordTrace]
  refine ⟨148274365159051039054167011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98849576772700692702778007 148274365159051039054167011)
  ·
    refine ⟨222411547738576558581250517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148274365159051039054167011 222411547738576558581250517)
    ·
      refine ⟨5212770650122888091748059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 222411547738576558581250517 5212770650122888091748059)
      ·
        refine ⟨7819155975184332137622089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5212770650122888091748059 7819155975184332137622089)
        ·
          refine ⟨5864366981388249103216567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7819155975184332137622089 5864366981388249103216567)
          ·
            refine ⟨8796550472082373654824851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5864366981388249103216567 8796550472082373654824851)
            ·
              refine ⟨13194825708123560482237277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8796550472082373654824851 13194825708123560482237277)
              ·
                refine ⟨4948059640546335180838979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13194825708123560482237277 4948059640546335180838979)
                ·
                  refine ⟨7422089460819502771258469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4948059640546335180838979 7422089460819502771258469)
                  ·
                    refine ⟨1391641773903656769610963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7422089460819502771258469 1391641773903656769610963)
                    ·
                      rfl

theorem cell22_4065319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_4065319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065319 prefixEnd_4065319 := by exact prefixLift 4065319
  have htrace : WordTrace (prefixWord ++ tailWord_4065319) baseStart_4065319 baseEnd_4065319 := by
    simpa [prefixWord, tailWord_4065319, baseEnd_4065319] using wordTrace_append hprefix tailTrace_4065319
  have hstable : (prefixWord ++ tailWord_4065319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065319).length < 2 ^ (prefixWord ++ tailWord_4065319).sum := by decide
  have hdescent : baseEnd_4065319 < baseStart_4065319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065328 : List Nat := [2, 1, 1, 1, 2, 6, 9]
def baseStart_4065328 : Nat := 118140960795 + 4065328 * 2 ^ 59
def prefixEnd_4065328 : Nat := 4983230072969 + 3 ^ 40 * 4065328 * 2
def baseEnd_4065328 : Nat := 51542402029169768375405

theorem tailTrace_4065328 : CollatzResearch.WordTrace tailWord_4065328 prefixEnd_4065328 51542402029169768375405 := by
  unfold tailWord_4065328
  simp only [CollatzResearch.WordTrace]
  refine ⟨74137346708009216795622319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 98849795610678955727496425 74137346708009216795622319)
  ·
    refine ⟨111206020062013825193433479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 74137346708009216795622319 111206020062013825193433479)
    ·
      refine ⟨166809030093020737790150219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111206020062013825193433479 166809030093020737790150219)
      ·
        refine ⟨250213545139531106685225329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166809030093020737790150219 250213545139531106685225329)
        ·
          refine ⟨187660158854648330013918997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 250213545139531106685225329 187660158854648330013918997)
          ·
            refine ⟨8796569946311640469402453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 187660158854648330013918997 8796569946311640469402453)
            ·
              refine ⟨51542402029169768375405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8796569946311640469402453 51542402029169768375405)
              ·
                rfl

theorem cell22_4065328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 9].length) (baseStart_4065328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065328 prefixEnd_4065328 := by exact prefixLift 4065328
  have htrace : WordTrace (prefixWord ++ tailWord_4065328) baseStart_4065328 baseEnd_4065328 := by
    simpa [prefixWord, tailWord_4065328, baseEnd_4065328] using wordTrace_append hprefix tailTrace_4065328
  have hstable : (prefixWord ++ tailWord_4065328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065328).length < 2 ^ (prefixWord ++ tailWord_4065328).sum := by decide
  have hdescent : baseEnd_4065328 < baseStart_4065328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065390 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 7]
def baseStart_4065390 : Nat := 118140960795 + 4065390 * 2 ^ 59
def prefixEnd_4065390 : Nat := 4983230072969 + 3 ^ 40 * 4065390 * 2
def baseEnd_4065390 : Nat := 463888692884878750361915

theorem tailTrace_4065390 : CollatzResearch.WordTrace tailWord_4065390 prefixEnd_4065390 463888692884878750361915 := by
  unfold tailWord_4065390
  simp only [CollatzResearch.WordTrace]
  refine ⟨18534619342724227272500203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 98851303161195878786667749 18534619342724227272500203)
  ·
    refine ⟨27801929014086340908750305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18534619342724227272500203 27801929014086340908750305)
    ·
      refine ⟨20851446760564755681562729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27801929014086340908750305 20851446760564755681562729)
      ·
        refine ⟨15638585070423566761172047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20851446760564755681562729 15638585070423566761172047)
        ·
          refine ⟨23457877605635350141758071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15638585070423566761172047 23457877605635350141758071)
          ·
            refine ⟨35186816408453025212637107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23457877605635350141758071 35186816408453025212637107)
            ·
              refine ⟨52780224612679537818955661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35186816408453025212637107 52780224612679537818955661)
              ·
                refine ⟨19792584229754826682108373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52780224612679537818955661 19792584229754826682108373)
                ·
                  refine ⟨463888692884878750361915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19792584229754826682108373 463888692884878750361915)
                  ·
                    rfl

theorem cell22_4065390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_4065390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065390 prefixEnd_4065390 := by exact prefixLift 4065390
  have htrace : WordTrace (prefixWord ++ tailWord_4065390) baseStart_4065390 baseEnd_4065390 := by
    simpa [prefixWord, tailWord_4065390, baseEnd_4065390] using wordTrace_append hprefix tailTrace_4065390
  have hstable : (prefixWord ++ tailWord_4065390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065390).length < 2 ^ (prefixWord ++ tailWord_4065390).sum := by decide
  have hdescent : baseEnd_4065390 < baseStart_4065390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065394 : List Nat := [3, 2, 1, 2, 2, 4, 1, 1, 3, 3]
def baseStart_4065394 : Nat := 118140960795 + 4065394 * 2 ^ 59
def prefixEnd_4065394 : Nat := 4983230072969 + 3 ^ 40 * 4065394 * 2
def baseEnd_4065394 : Nat := 1391667447936381573985733

theorem tailTrace_4065394 : CollatzResearch.WordTrace tailWord_4065394 prefixEnd_4065394 1391667447936381573985733 := by
  unfold tailWord_4065394
  simp only [CollatzResearch.WordTrace]
  refine ⟨37069275158444831715786809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 98851400422519551242098157 37069275158444831715786809)
  ·
    refine ⟨27801956368833623786840107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37069275158444831715786809 27801956368833623786840107)
    ·
      refine ⟨41702934553250435680260161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27801956368833623786840107 41702934553250435680260161)
      ·
        refine ⟨31277200914937826760195121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41702934553250435680260161 31277200914937826760195121)
        ·
          refine ⟨23457900686203370070146341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31277200914937826760195121 23457900686203370070146341)
          ·
            refine ⟨4398356378663131888152439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23457900686203370070146341 4398356378663131888152439)
            ·
              refine ⟨6597534567994697832228659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4398356378663131888152439 6597534567994697832228659)
              ·
                refine ⟨9896301851992046748342989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6597534567994697832228659 9896301851992046748342989)
                ·
                  refine ⟨3711113194497017530628621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9896301851992046748342989 3711113194497017530628621)
                  ·
                    refine ⟨1391667447936381573985733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3711113194497017530628621 1391667447936381573985733)
                    ·
                      rfl

theorem cell22_4065394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_4065394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065394 prefixEnd_4065394 := by exact prefixLift 4065394
  have htrace : WordTrace (prefixWord ++ tailWord_4065394) baseStart_4065394 baseEnd_4065394 := by
    simpa [prefixWord, tailWord_4065394, baseEnd_4065394] using wordTrace_append hprefix tailTrace_4065394
  have hstable : (prefixWord ++ tailWord_4065394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065394).length < 2 ^ (prefixWord ++ tailWord_4065394).sum := by decide
  have hdescent : baseEnd_4065394 < baseStart_4065394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065403 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 1, 10]
def baseStart_4065403 : Nat := 118140960795 + 4065403 * 2 ^ 59
def prefixEnd_4065403 : Nat := 4983230072969 + 3 ^ 40 * 4065403 * 2
def baseEnd_4065403 : Nat := 1391670528820308550510705

theorem tailTrace_4065403 : CollatzResearch.WordTrace tailWord_4065403 prefixEnd_4065403 1391670528820308550510705 := by
  unfold tailWord_4065403
  simp only [CollatzResearch.WordTrace]
  refine ⟨148277428890746721400224863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98851619260497814266816575 148277428890746721400224863)
  ·
    refine ⟨222416143336120082100337295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148277428890746721400224863 222416143336120082100337295)
    ·
      refine ⟨333624215004180123150505943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222416143336120082100337295 333624215004180123150505943)
      ·
        refine ⟨500436322506270184725758915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333624215004180123150505943 500436322506270184725758915)
        ·
          refine ⟨750654483759405277088638373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500436322506270184725758915 750654483759405277088638373)
          ·
            refine ⟨140747715704888489454119695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 750654483759405277088638373 140747715704888489454119695)
            ·
              refine ⟨211121573557332734181179543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 140747715704888489454119695 211121573557332734181179543)
              ·
                refine ⟨316682360335999101271769315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 211121573557332734181179543 316682360335999101271769315)
                ·
                  refine ⟨475023540503998651907653973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316682360335999101271769315 475023540503998651907653973)
                  ·
                    refine ⟨1391670528820308550510705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 475023540503998651907653973 1391670528820308550510705)
                    ·
                      rfl

theorem cell22_4065403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 10].length) (baseStart_4065403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065403 prefixEnd_4065403 := by exact prefixLift 4065403
  have htrace : WordTrace (prefixWord ++ tailWord_4065403) baseStart_4065403 baseEnd_4065403 := by
    simpa [prefixWord, tailWord_4065403, baseEnd_4065403] using wordTrace_append hprefix tailTrace_4065403
  have hstable : (prefixWord ++ tailWord_4065403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065403).length < 2 ^ (prefixWord ++ tailWord_4065403).sum := by decide
  have hdescent : baseEnd_4065403 < baseStart_4065403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065465 : List Nat := [1, 2, 1, 4, 1, 2, 2, 2, 1, 6]
def baseStart_4065465 : Nat := 118140960795 + 4065465 * 2 ^ 59
def prefixEnd_4065465 : Nat := 4983230072969 + 3 ^ 40 * 4065465 * 2
def baseEnd_4065465 : Nat := 1391691752687361055460515

theorem tailTrace_4065465 : CollatzResearch.WordTrace tailWord_4065465 prefixEnd_4065465 1391691752687361055460515 := by
  unfold tailWord_4065465
  simp only [CollatzResearch.WordTrace]
  refine ⟨148279690216522105988981849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98853126811014737325987899 148279690216522105988981849)
  ·
    refine ⟨111209767662391579491736387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 148279690216522105988981849 111209767662391579491736387)
    ·
      refine ⟨166814651493587369237604581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 111209767662391579491736387 166814651493587369237604581)
      ·
        refine ⟨31277747155047631732050859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 166814651493587369237604581 31277747155047631732050859)
        ·
          refine ⟨46916620732571447598076289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31277747155047631732050859 46916620732571447598076289)
          ·
            refine ⟨35187465549428585698557217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46916620732571447598076289 35187465549428585698557217)
            ·
              refine ⟨26390599162071439273917913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35187465549428585698557217 26390599162071439273917913)
              ·
                refine ⟨19792949371553579455438435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26390599162071439273917913 19792949371553579455438435)
                ·
                  refine ⟨29689424057330369183157653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19792949371553579455438435 29689424057330369183157653)
                  ·
                    refine ⟨1391691752687361055460515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29689424057330369183157653 1391691752687361055460515)
                    ·
                      rfl

theorem cell22_4065465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_4065465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065465 prefixEnd_4065465 := by exact prefixLift 4065465
  have htrace : WordTrace (prefixWord ++ tailWord_4065465) baseStart_4065465 baseEnd_4065465 := by
    simpa [prefixWord, tailWord_4065465, baseEnd_4065465] using wordTrace_append hprefix tailTrace_4065465
  have hstable : (prefixWord ++ tailWord_4065465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065465).length < 2 ^ (prefixWord ++ tailWord_4065465).sum := by decide
  have hdescent : baseEnd_4065465 < baseStart_4065465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065467 : List Nat := [1, 1, 1, 1, 1, 2, 5, 5, 2, 3]
def baseStart_4065467 : Nat := 118140960795 + 4065467 * 2 ^ 59
def prefixEnd_4065467 : Nat := 4983230072969 + 3 ^ 40 * 4065467 * 2
def baseEnd_4065467 : Nat := 1391692437328233716910509

theorem tailTrace_4065467 : CollatzResearch.WordTrace tailWord_4065467 prefixEnd_4065467 1391692437328233716910509 := by
  unfold tailWord_4065467
  simp only [CollatzResearch.WordTrace]
  refine ⟨148279763162514860330554655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98853175441676573553703103 148279763162514860330554655)
  ·
    refine ⟨222419644743772290495831983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 148279763162514860330554655 222419644743772290495831983)
    ·
      refine ⟨333629467115658435743747975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 222419644743772290495831983 333629467115658435743747975)
      ·
        refine ⟨500444200673487653615621963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 333629467115658435743747975 500444200673487653615621963)
        ·
          refine ⟨750666301010231480423432945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 500444200673487653615621963 750666301010231480423432945)
          ·
            refine ⟨562999725757673610317574709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 750666301010231480423432945 562999725757673610317574709)
            ·
              refine ⟨52781224289781900967272629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 562999725757673610317574709 52781224289781900967272629)
              ·
                refine ⟨4948239777167053215681809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52781224289781900967272629 4948239777167053215681809)
                ·
                  refine ⟨3711179832875289911761357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4948239777167053215681809 3711179832875289911761357)
                  ·
                    refine ⟨1391692437328233716910509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3711179832875289911761357 1391692437328233716910509)
                    ·
                      rfl

theorem cell22_4065467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 5, 2, 3].length) (baseStart_4065467 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065467 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065467 prefixEnd_4065467 := by exact prefixLift 4065467
  have htrace : WordTrace (prefixWord ++ tailWord_4065467) baseStart_4065467 baseEnd_4065467 := by
    simpa [prefixWord, tailWord_4065467, baseEnd_4065467] using wordTrace_append hprefix tailTrace_4065467
  have hstable : (prefixWord ++ tailWord_4065467).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065467).length < 2 ^ (prefixWord ++ tailWord_4065467).sum := by decide
  have hdescent : baseEnd_4065467 < baseStart_4065467 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4065501 : List Nat := [1, 4, 3, 2, 1, 1, 3, 2, 2, 3]
def baseStart_4065501 : Nat := 118140960795 + 4065501 * 2 ^ 59
def prefixEnd_4065501 : Nat := 4983230072969 + 3 ^ 40 * 4065501 * 2
def baseEnd_4065501 : Nat := 1391704076223068961560405

theorem tailTrace_4065501 : CollatzResearch.WordTrace tailWord_4065501 prefixEnd_4065501 1391704076223068961560405 := by
  unfold tailWord_4065501
  simp only [CollatzResearch.WordTrace]
  refine ⟨148281003244391684137292357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 98854002162927789424861571 148281003244391684137292357)
  ·
    refine ⟨27802688108323440775742317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 148281003244391684137292357 27802688108323440775742317)
    ·
      refine ⟨10426008040621290290903369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27802688108323440775742317 10426008040621290290903369)
      ·
        refine ⟨7819506030465967718177527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10426008040621290290903369 7819506030465967718177527)
        ·
          refine ⟨11729259045698951577266291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7819506030465967718177527 11729259045698951577266291)
          ·
            refine ⟨17593888568548427365899437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11729259045698951577266291 17593888568548427365899437)
            ·
              refine ⟨6597708213205660262212289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17593888568548427365899437 6597708213205660262212289)
              ·
                refine ⟨4948281159904245196659217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6597708213205660262212289 4948281159904245196659217)
                ·
                  refine ⟨3711210869928183897494413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4948281159904245196659217 3711210869928183897494413)
                  ·
                    refine ⟨1391704076223068961560405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3711210869928183897494413 1391704076223068961560405)
                    ·
                      rfl

theorem cell22_4065501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_4065501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_4065501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_4065501 prefixEnd_4065501 := by exact prefixLift 4065501
  have htrace : WordTrace (prefixWord ++ tailWord_4065501) baseStart_4065501 baseEnd_4065501 := by
    simpa [prefixWord, tailWord_4065501, baseEnd_4065501] using wordTrace_append hprefix tailTrace_4065501
  have hstable : (prefixWord ++ tailWord_4065501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4065501).length < 2 ^ (prefixWord ++ tailWord_4065501).sum := by decide
  have hdescent : baseEnd_4065501 < baseStart_4065501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4065501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
