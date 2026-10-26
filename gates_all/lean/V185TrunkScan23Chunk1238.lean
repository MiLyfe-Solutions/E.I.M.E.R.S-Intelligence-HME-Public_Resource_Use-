import V185TrunkScan23Chunk1237

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7334613 : List Nat := [1, 3, 2, 5, 1, 1, 2, 2, 6]
def baseStart_7334613 : Nat := 118140960795 + 7334613 * 2 ^ 59
def prefixEnd_7334613 : Nat := 4983230072969 + 3 ^ 40 * 7334613 * 2
def baseEnd_7334613 : Nat := 418464653746179669622915

theorem tailTrace_7334613 : CollatzResearch.WordTrace tailWord_7334613 prefixEnd_7334613 418464653746179669622915 := by
  unfold tailWord_7334613
  simp only [CollatzResearch.WordTrace]
  refine ⟨267515313376957228016776493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178343542251304818677850995 267515313376957228016776493)
  ·
    refine ⟨100318242516358960506291185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267515313376957228016776493 100318242516358960506291185)
    ·
      refine ⟨75238681887269220379718389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100318242516358960506291185 75238681887269220379718389)
      ·
        refine ⟨7053626426931489410598599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75238681887269220379718389 7053626426931489410598599)
        ·
          refine ⟨10580439640397234115897899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7053626426931489410598599 10580439640397234115897899)
          ·
            refine ⟨15870659460595851173846849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10580439640397234115897899 15870659460595851173846849)
            ·
              refine ⟨11902994595446888380385137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15870659460595851173846849 11902994595446888380385137)
              ·
                refine ⟨8927245946585166285288853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11902994595446888380385137 8927245946585166285288853)
                ·
                  refine ⟨418464653746179669622915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8927245946585166285288853 418464653746179669622915)
                  ·
                    rfl

theorem cell23_7334613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 6].length) (baseStart_7334613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334613 prefixEnd_7334613 := by exact prefixLift 7334613
  have htrace : WordTrace (prefixWord ++ tailWord_7334613) baseStart_7334613 baseEnd_7334613 := by
    simpa [prefixWord, tailWord_7334613, baseEnd_7334613] using wordTrace_append hprefix tailTrace_7334613
  have hstable : (prefixWord ++ tailWord_7334613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334613).length < 2 ^ (prefixWord ++ tailWord_7334613).sum := by decide
  have hdescent : baseEnd_7334613 < baseStart_7334613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334639 : List Nat := [1, 1, 2, 1, 5, 2, 1, 3, 1, 6]
def baseStart_7334639 : Nat := 118140960795 + 7334639 * 2 ^ 59
def prefixEnd_7334639 : Nat := 4983230072969 + 3 ^ 40 * 7334639 * 2
def baseEnd_7334639 : Nat := 1255398411404211308293705

theorem tailTrace_7334639 : CollatzResearch.WordTrace tailWord_7334639 prefixEnd_7334639 1255398411404211308293705 := by
  unfold tailWord_7334639
  simp only [CollatzResearch.WordTrace]
  refine ⟨267516261674863034457222971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178344174449908689638148647 267516261674863034457222971)
  ·
    refine ⟨401274392512294551685834457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267516261674863034457222971 401274392512294551685834457)
    ·
      refine ⟨300955794384220913764375843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401274392512294551685834457 300955794384220913764375843)
      ·
        refine ⟨451433691576331370646563765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300955794384220913764375843 451433691576331370646563765)
        ·
          refine ⟨42321908585281065998115353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 451433691576331370646563765 42321908585281065998115353)
          ·
            refine ⟨31741431438960799498586515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42321908585281065998115353 31741431438960799498586515)
            ·
              refine ⟨47612147158441199247879773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31741431438960799498586515 47612147158441199247879773)
              ·
                refine ⟨17854555184415449717954915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47612147158441199247879773 17854555184415449717954915)
                ·
                  refine ⟨26781832776623174576932373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17854555184415449717954915 26781832776623174576932373)
                  ·
                    refine ⟨1255398411404211308293705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26781832776623174576932373 1255398411404211308293705)
                    ·
                      rfl

theorem cell23_7334639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 1, 6].length) (baseStart_7334639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334639 prefixEnd_7334639 := by exact prefixLift 7334639
  have htrace : WordTrace (prefixWord ++ tailWord_7334639) baseStart_7334639 baseEnd_7334639 := by
    simpa [prefixWord, tailWord_7334639, baseEnd_7334639] using wordTrace_append hprefix tailTrace_7334639
  have hstable : (prefixWord ++ tailWord_7334639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334639).length < 2 ^ (prefixWord ++ tailWord_7334639).sum := by decide
  have hdescent : baseEnd_7334639 < baseStart_7334639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334644 : List Nat := [2, 6, 1, 1, 3, 1, 1, 1, 2, 2, 3]
def baseStart_7334644 : Nat := 118140960795 + 7334644 * 2 ^ 59
def prefixEnd_7334644 : Nat := 4983230072969 + 3 ^ 40 * 7334644 * 2
def baseEnd_7334644 : Nat := 3766197801615906405318593

theorem tailTrace_7334644 : CollatzResearch.WordTrace tailWord_7334644 prefixEnd_7334644 3766197801615906405318593 := by
  unfold tailWord_7334644
  simp only [CollatzResearch.WordTrace]
  refine ⟨133758222019922460155577493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178344296026563280207436657 133758222019922460155577493)
  ·
    refine ⟨6269916657183865319792695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 133758222019922460155577493 6269916657183865319792695)
    ·
      refine ⟨9404874985775797979689043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6269916657183865319792695 9404874985775797979689043)
      ·
        refine ⟨14107312478663696969533565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9404874985775797979689043 14107312478663696969533565)
        ·
          refine ⟨5290242179498886363575087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14107312478663696969533565 5290242179498886363575087)
          ·
            refine ⟨7935363269248329545362631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5290242179498886363575087 7935363269248329545362631)
            ·
              refine ⟨11903044903872494318043947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7935363269248329545362631 11903044903872494318043947)
              ·
                refine ⟨17854567355808741477065921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11903044903872494318043947 17854567355808741477065921)
                ·
                  refine ⟨13390925516856556107799441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17854567355808741477065921 13390925516856556107799441)
                  ·
                    refine ⟨10043194137642417080849581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13390925516856556107799441 10043194137642417080849581)
                    ·
                      refine ⟨3766197801615906405318593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10043194137642417080849581 3766197801615906405318593)
                      ·
                        rfl

theorem cell23_7334644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_7334644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334644 prefixEnd_7334644 := by exact prefixLift 7334644
  have htrace : WordTrace (prefixWord ++ tailWord_7334644) baseStart_7334644 baseEnd_7334644 := by
    simpa [prefixWord, tailWord_7334644, baseEnd_7334644] using wordTrace_append hprefix tailTrace_7334644
  have hstable : (prefixWord ++ tailWord_7334644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334644).length < 2 ^ (prefixWord ++ tailWord_7334644).sum := by decide
  have hdescent : baseEnd_7334644 < baseStart_7334644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334646 : List Nat := [5, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4]
def baseStart_7334646 : Nat := 118140960795 + 7334646 * 2 ^ 59
def prefixEnd_7334646 : Nat := 4983230072969 + 3 ^ 40 * 7334646 * 2
def baseEnd_7334646 : Nat := 3766198828577215397493583

theorem tailTrace_7334646 : CollatzResearch.WordTrace tailWord_7334646 prefixEnd_7334646 3766198828577215397493583 := by
  unfold tailWord_7334646
  simp only [CollatzResearch.WordTrace]
  refine ⟨16719782311614854665795487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178344344657225116435151861 16719782311614854665795487)
  ·
    refine ⟨25079673467422281998693231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16719782311614854665795487 25079673467422281998693231)
    ·
      refine ⟨37619510201133422998039847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25079673467422281998693231 37619510201133422998039847)
      ·
        refine ⟨56429265301700134497059771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37619510201133422998039847 56429265301700134497059771)
        ·
          refine ⟨84643897952550201745589657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56429265301700134497059771 84643897952550201745589657)
          ·
            refine ⟨63482923464412651309192243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84643897952550201745589657 63482923464412651309192243)
            ·
              refine ⟨95224385196618976963788365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63482923464412651309192243 95224385196618976963788365)
              ·
                refine ⟨35709144448732116361420637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95224385196618976963788365 35709144448732116361420637)
                ·
                  refine ⟨13390929168274543635532739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35709144448732116361420637 13390929168274543635532739)
                  ·
                    refine ⟨20086393752411815453299109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13390929168274543635532739 20086393752411815453299109)
                    ·
                      refine ⟨3766198828577215397493583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20086393752411815453299109 3766198828577215397493583)
                      ·
                        rfl

theorem cell23_7334646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_7334646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334646 prefixEnd_7334646 := by exact prefixLift 7334646
  have htrace : WordTrace (prefixWord ++ tailWord_7334646) baseStart_7334646 baseEnd_7334646 := by
    simpa [prefixWord, tailWord_7334646, baseEnd_7334646] using wordTrace_append hprefix tailTrace_7334646
  have hstable : (prefixWord ++ tailWord_7334646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334646).length < 2 ^ (prefixWord ++ tailWord_7334646).sum := by decide
  have hdescent : baseEnd_7334646 < baseStart_7334646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334663 : List Nat := [1, 1, 4, 4, 1, 2, 1, 3, 1, 1, 4]
def baseStart_7334663 : Nat := 118140960795 + 7334663 * 2 ^ 59
def prefixEnd_7334663 : Nat := 4983230072969 + 3 ^ 40 * 7334663 * 2
def baseEnd_7334663 : Nat := 3766207557748341830981005

theorem tailTrace_7334663 : CollatzResearch.WordTrace tailWord_7334663 prefixEnd_7334663 3766207557748341830981005 := by
  unfold tailWord_7334663
  simp only [CollatzResearch.WordTrace]
  refine ⟨267517137026776086556096643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178344758017850724370731095 267517137026776086556096643)
  ·
    refine ⟨401275705540164129834144965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267517137026776086556096643 401275705540164129834144965)
    ·
      refine ⟨75239194788780774343902181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401275705540164129834144965 75239194788780774343902181)
      ·
        refine ⟨14107349022896395189481659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75239194788780774343902181 14107349022896395189481659)
        ·
          refine ⟨21161023534344592784222489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14107349022896395189481659 21161023534344592784222489)
          ·
            refine ⟨15870767650758444588166867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21161023534344592784222489 15870767650758444588166867)
            ·
              refine ⟨23806151476137666882250301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15870767650758444588166867 23806151476137666882250301)
              ·
                refine ⟨8927306803551625080843863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23806151476137666882250301 8927306803551625080843863)
                ·
                  refine ⟨13390960205327437621265795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8927306803551625080843863 13390960205327437621265795)
                  ·
                    refine ⟨20086440307991156431898693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13390960205327437621265795 20086440307991156431898693)
                    ·
                      refine ⟨3766207557748341830981005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20086440307991156431898693 3766207557748341830981005)
                      ·
                        rfl

theorem cell23_7334663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_7334663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334663 prefixEnd_7334663 := by exact prefixLift 7334663
  have htrace : WordTrace (prefixWord ++ tailWord_7334663) baseStart_7334663 baseEnd_7334663 := by
    simpa [prefixWord, tailWord_7334663, baseEnd_7334663] using wordTrace_append hprefix tailTrace_7334663
  have hstable : (prefixWord ++ tailWord_7334663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334663).length < 2 ^ (prefixWord ++ tailWord_7334663).sum := by decide
  have hdescent : baseEnd_7334663 < baseStart_7334663 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334690 : List Nat := [3, 3, 1, 1, 2, 3, 3, 1, 2, 4]
def baseStart_7334690 : Nat := 118140960795 + 7334690 * 2 ^ 59
def prefixEnd_7334690 : Nat := 4983230072969 + 3 ^ 40 * 7334690 * 2
def baseEnd_7334690 : Nat := 1255407140575337741781127

theorem tailTrace_7334690 : CollatzResearch.WordTrace tailWord_7334690 prefixEnd_7334690 1255407140575337741781127 := by
  unfold tailWord_7334690
  simp only [CollatzResearch.WordTrace]
  refine ⟨66879530449419567541832381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178345414531785513444886349 66879530449419567541832381)
  ·
    refine ⟨25079823918532337828187143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66879530449419567541832381 25079823918532337828187143)
    ·
      refine ⟨37619735877798506742280715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25079823918532337828187143 37619735877798506742280715)
      ·
        refine ⟨56429603816697760113421073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37619735877798506742280715 56429603816697760113421073)
        ·
          refine ⟨42322202862523320085065805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56429603816697760113421073 42322202862523320085065805)
          ·
            refine ⟨15870826073446245031899677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42322202862523320085065805 15870826073446245031899677)
            ·
              refine ⟨5951559777542341886962379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15870826073446245031899677 5951559777542341886962379)
              ·
                refine ⟨8927339666313512830443569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5951559777542341886962379 8927339666313512830443569)
                ·
                  refine ⟨6695504749735134622832677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8927339666313512830443569 6695504749735134622832677)
                  ·
                    refine ⟨1255407140575337741781127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6695504749735134622832677 1255407140575337741781127)
                    ·
                      rfl

theorem cell23_7334690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_7334690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334690 prefixEnd_7334690 := by exact prefixLift 7334690
  have htrace : WordTrace (prefixWord ++ tailWord_7334690) baseStart_7334690 baseEnd_7334690 := by
    simpa [prefixWord, tailWord_7334690, baseEnd_7334690] using wordTrace_append hprefix tailTrace_7334690
  have hstable : (prefixWord ++ tailWord_7334690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334690).length < 2 ^ (prefixWord ++ tailWord_7334690).sum := by decide
  have hdescent : baseEnd_7334690 < baseStart_7334690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334714 : List Nat := [3, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2]
def baseStart_7334714 : Nat := 118140960795 + 7334714 * 2 ^ 59
def prefixEnd_7334714 : Nat := 4983230072969 + 3 ^ 40 * 7334714 * 2
def baseEnd_7334714 : Nat := 3766233745261721131443271

theorem tailTrace_7334714 : CollatzResearch.WordTrace tailWord_7334714 prefixEnd_7334714 3766233745261721131443271 := by
  unfold tailWord_7334714
  simp only [CollatzResearch.WordTrace]
  refine ⟨66879749287397830566550799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178345998099727548177468797 66879749287397830566550799)
  ·
    refine ⟨100319623931096745849826199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66879749287397830566550799 100319623931096745849826199)
    ·
      refine ⟨150479435896645118774739299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100319623931096745849826199 150479435896645118774739299)
      ·
        refine ⟨225719153844967678162108949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150479435896645118774739299 225719153844967678162108949)
        ·
          refine ⟨10580585336482859913848857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 225719153844967678162108949 10580585336482859913848857)
          ·
            refine ⟨7935439002362144935386643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10580585336482859913848857 7935439002362144935386643)
            ·
              refine ⟨11903158503543217403079965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7935439002362144935386643 11903158503543217403079965)
              ·
                refine ⟨4463684438828706526154987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11903158503543217403079965 4463684438828706526154987)
                ·
                  refine ⟨6695526658243059789232481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4463684438828706526154987 6695526658243059789232481)
                  ·
                    refine ⟨5021644993682294841924361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6695526658243059789232481 5021644993682294841924361)
                    ·
                      refine ⟨3766233745261721131443271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5021644993682294841924361 3766233745261721131443271)
                      ·
                        rfl

theorem cell23_7334714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 3, 1, 2, 2].length) (baseStart_7334714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334714 prefixEnd_7334714 := by exact prefixLift 7334714
  have htrace : WordTrace (prefixWord ++ tailWord_7334714) baseStart_7334714 baseEnd_7334714 := by
    simpa [prefixWord, tailWord_7334714, baseEnd_7334714] using wordTrace_append hprefix tailTrace_7334714
  have hstable : (prefixWord ++ tailWord_7334714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334714).length < 2 ^ (prefixWord ++ tailWord_7334714).sum := by decide
  have hdescent : baseEnd_7334714 < baseStart_7334714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334723 : List Nat := [1, 1, 1, 3, 1, 4, 1, 5, 1, 3, 2]
def baseStart_7334723 : Nat := 118140960795 + 7334723 * 2 ^ 59
def prefixEnd_7334723 : Nat := 4983230072969 + 3 ^ 40 * 7334723 * 2
def baseEnd_7334723 : Nat := 3766238366587611596230729

theorem tailTrace_7334723 : CollatzResearch.WordTrace tailWord_7334723 prefixEnd_7334723 3766238366587611596230729 := by
  unfold tailWord_7334723
  simp only [CollatzResearch.WordTrace]
  refine ⟨267519325406558716803280823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178346216937705811202187215 267519325406558716803280823)
  ·
    refine ⟨401278988109838075204921235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267519325406558716803280823 401278988109838075204921235)
    ·
      refine ⟨601918482164757112807381853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401278988109838075204921235 601918482164757112807381853)
      ·
        refine ⟨225719430811783917302768195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 601918482164757112807381853 225719430811783917302768195)
        ·
          refine ⟨338579146217675875954152293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225719430811783917302768195 338579146217675875954152293)
          ·
            refine ⟨63483589915814226741403555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338579146217675875954152293 63483589915814226741403555)
            ·
              refine ⟨95225384873721340112105333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63483589915814226741403555 95225384873721340112105333)
              ·
                refine ⟨8927379831911375635509875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95225384873721340112105333 8927379831911375635509875)
                ·
                  refine ⟨13391069747867063453264813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8927379831911375635509875 13391069747867063453264813)
                  ·
                    refine ⟨5021651155450148794974305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13391069747867063453264813 5021651155450148794974305)
                    ·
                      refine ⟨3766238366587611596230729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5021651155450148794974305 3766238366587611596230729)
                      ·
                        rfl

theorem cell23_7334723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 3, 2].length) (baseStart_7334723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334723 prefixEnd_7334723 := by exact prefixLift 7334723
  have htrace : WordTrace (prefixWord ++ tailWord_7334723) baseStart_7334723 baseEnd_7334723 := by
    simpa [prefixWord, tailWord_7334723, baseEnd_7334723] using wordTrace_append hprefix tailTrace_7334723
  have hstable : (prefixWord ++ tailWord_7334723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334723).length < 2 ^ (prefixWord ++ tailWord_7334723).sum := by decide
  have hdescent : baseEnd_7334723 < baseStart_7334723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334753 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 6, 2, 2]
def baseStart_7334753 : Nat := 118140960795 + 7334753 * 2 ^ 59
def prefixEnd_7334753 : Nat := 4983230072969 + 3 ^ 40 * 7334753 * 2
def baseEnd_7334753 : Nat := 3766253771007246478855591

theorem tailTrace_7334753 : CollatzResearch.WordTrace tailWord_7334753 prefixEnd_7334753 3766253771007246478855591 := by
  unfold tailWord_7334753
  simp only [CollatzResearch.WordTrace]
  refine ⟨267520419596450031926872913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178346946397633354617915275 267520419596450031926872913)
  ·
    refine ⟨200640314697337523945154685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267520419596450031926872913 200640314697337523945154685)
    ·
      refine ⟨75240118011501571479433007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200640314697337523945154685 75240118011501571479433007)
      ·
        refine ⟨112860177017252357219149511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75240118011501571479433007 112860177017252357219149511)
        ·
          refine ⟨169290265525878535828724267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112860177017252357219149511 169290265525878535828724267)
          ·
            refine ⟨253935398288817803743086401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169290265525878535828724267 253935398288817803743086401)
            ·
              refine ⟨190451548716613352807314801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253935398288817803743086401 190451548716613352807314801)
              ·
                refine ⟨142838661537460014605486101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190451548716613352807314801 142838661537460014605486101)
                ·
                  refine ⟨6695562259568438184632161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 142838661537460014605486101 6695562259568438184632161)
                  ·
                    refine ⟨5021671694676328638474121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6695562259568438184632161 5021671694676328638474121)
                    ·
                      refine ⟨3766253771007246478855591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5021671694676328638474121 3766253771007246478855591)
                      ·
                        rfl

theorem cell23_7334753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 2, 2].length) (baseStart_7334753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334753 prefixEnd_7334753 := by exact prefixLift 7334753
  have htrace : WordTrace (prefixWord ++ tailWord_7334753) baseStart_7334753 baseEnd_7334753 := by
    simpa [prefixWord, tailWord_7334753, baseEnd_7334753] using wordTrace_append hprefix tailTrace_7334753
  have hstable : (prefixWord ++ tailWord_7334753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334753).length < 2 ^ (prefixWord ++ tailWord_7334753).sum := by decide
  have hdescent : baseEnd_7334753 < baseStart_7334753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334756 : List Nat := [2, 3, 1, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_7334756 : Nat := 118140960795 + 7334756 * 2 ^ 59
def prefixEnd_7334756 : Nat := 4983230072969 + 3 ^ 40 * 7334756 * 2
def baseEnd_7334756 : Nat := 3766255311449209967118077

theorem tailTrace_7334756 : CollatzResearch.WordTrace tailWord_7334756 prefixEnd_7334756 3766255311449209967118077 := by
  unfold tailWord_7334756
  simp only [CollatzResearch.WordTrace]
  refine ⟨133760264507719581719616061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178347019343626108959488081 133760264507719581719616061)
  ·
    refine ⟨50160099190394843144856023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133760264507719581719616061 50160099190394843144856023)
    ·
      refine ⟨75240148785592264717284035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50160099190394843144856023 75240148785592264717284035)
      ·
        refine ⟨112860223178388397075926053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75240148785592264717284035 112860223178388397075926053)
        ·
          refine ⟨21161291845947824451736135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112860223178388397075926053 21161291845947824451736135)
          ·
            refine ⟨31741937768921736677604203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21161291845947824451736135 31741937768921736677604203)
            ·
              refine ⟨47612906653382605016406305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31741937768921736677604203 47612906653382605016406305)
              ·
                refine ⟨35709679990036953762304729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47612906653382605016406305 35709679990036953762304729)
                ·
                  refine ⟨26782259992527715321728547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35709679990036953762304729 26782259992527715321728547)
                  ·
                    refine ⟨40173389988791572982592821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26782259992527715321728547 40173389988791572982592821)
                    ·
                      refine ⟨3766255311449209967118077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40173389988791572982592821 3766255311449209967118077)
                      ·
                        rfl

theorem cell23_7334756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_7334756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334756 prefixEnd_7334756 := by exact prefixLift 7334756
  have htrace : WordTrace (prefixWord ++ tailWord_7334756) baseStart_7334756 baseEnd_7334756 := by
    simpa [prefixWord, tailWord_7334756, baseEnd_7334756] using wordTrace_append hprefix tailTrace_7334756
  have hstable : (prefixWord ++ tailWord_7334756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334756).length < 2 ^ (prefixWord ++ tailWord_7334756).sum := by decide
  have hdescent : baseEnd_7334756 < baseStart_7334756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334774 : List Nat := [5, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2]
def baseStart_7334774 : Nat := 118140960795 + 7334774 * 2 ^ 59
def prefixEnd_7334774 : Nat := 4983230072969 + 3 ^ 40 * 7334774 * 2
def baseEnd_7334774 : Nat := 3766264554100990896692995

theorem tailTrace_7334774 : CollatzResearch.WordTrace tailWord_7334774 prefixEnd_7334774 3766264554100990896692995 := by
  unfold tailWord_7334774
  simp only [CollatzResearch.WordTrace]
  refine ⟨16720074095585872032086711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178347457019582635008924917 16720074095585872032086711)
  ·
    refine ⟨25080111143378808048130067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16720074095585872032086711 25080111143378808048130067)
    ·
      refine ⟨37620166715068212072195101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25080111143378808048130067 37620166715068212072195101)
      ·
        refine ⟨14107562518150579527073163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37620166715068212072195101 14107562518150579527073163)
        ·
          refine ⟨21161343777225869290609745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14107562518150579527073163 21161343777225869290609745)
          ·
            refine ⟨15871007832919401967957309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21161343777225869290609745 15871007832919401967957309)
            ·
              refine ⟨5951627937344775737983991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15871007832919401967957309 5951627937344775737983991)
              ·
                refine ⟨8927441906017163606975987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5951627937344775737983991 8927441906017163606975987)
                ·
                  refine ⟨13391162859025745410463981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8927441906017163606975987 13391162859025745410463981)
                  ·
                    refine ⟨5021686072134654528923993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13391162859025745410463981 5021686072134654528923993)
                    ·
                      refine ⟨3766264554100990896692995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5021686072134654528923993 3766264554100990896692995)
                      ·
                        rfl

theorem cell23_7334774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_7334774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334774 prefixEnd_7334774 := by exact prefixLift 7334774
  have htrace : WordTrace (prefixWord ++ tailWord_7334774) baseStart_7334774 baseEnd_7334774 := by
    simpa [prefixWord, tailWord_7334774, baseEnd_7334774] using wordTrace_append hprefix tailTrace_7334774
  have hstable : (prefixWord ++ tailWord_7334774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334774).length < 2 ^ (prefixWord ++ tailWord_7334774).sum := by decide
  have hdescent : baseEnd_7334774 < baseStart_7334774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334793 : List Nat := [1, 2, 1, 1, 5, 3, 1, 4, 5]
def baseStart_7334793 : Nat := 118140960795 + 7334793 * 2 ^ 59
def prefixEnd_7334793 : Nat := 4983230072969 + 3 ^ 40 * 7334793 * 2
def baseEnd_7334793 : Nat := 418474923359269591372823

theorem tailTrace_7334793 : CollatzResearch.WordTrace tailWord_7334793 prefixEnd_7334793 418474923359269591372823 := by
  unfold tailWord_7334793
  simp only [CollatzResearch.WordTrace]
  refine ⟨267521878516305118758329033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178347919010870079172219355 267521878516305118758329033)
  ·
    refine ⟨200641408887228839068746775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267521878516305118758329033 200641408887228839068746775)
    ·
      refine ⟨300962113330843258603120163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200641408887228839068746775 300962113330843258603120163)
      ·
        refine ⟨451443169996264887904680245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300962113330843258603120163 451443169996264887904680245)
        ·
          refine ⟨42322797187149833241063773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 451443169996264887904680245 42322797187149833241063773)
          ·
            refine ⟨15871048945181187465398915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42322797187149833241063773 15871048945181187465398915)
            ·
              refine ⟨23806573417771781198098373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15871048945181187465398915 23806573417771781198098373)
              ·
                refine ⟨4463732515832208974643445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23806573417771781198098373 4463732515832208974643445)
                ·
                  refine ⟨418474923359269591372823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4463732515832208974643445 418474923359269591372823)
                  ·
                    rfl

theorem cell23_7334793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 5].length) (baseStart_7334793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334793 prefixEnd_7334793 := by exact prefixLift 7334793
  have htrace : WordTrace (prefixWord ++ tailWord_7334793) baseStart_7334793 baseEnd_7334793 := by
    simpa [prefixWord, tailWord_7334793, baseEnd_7334793] using wordTrace_append hprefix tailTrace_7334793
  have hstable : (prefixWord ++ tailWord_7334793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334793).length < 2 ^ (prefixWord ++ tailWord_7334793).sum := by decide
  have hdescent : baseEnd_7334793 < baseStart_7334793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334813 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 2, 5, 2]
def baseStart_7334813 : Nat := 118140960795 + 7334813 * 2 ^ 59
def prefixEnd_7334813 : Nat := 4983230072969 + 3 ^ 40 * 7334813 * 2
def baseEnd_7334813 : Nat := 3766284579846516244105315

theorem tailTrace_7334813 : CollatzResearch.WordTrace tailWord_7334813 prefixEnd_7334813 3766284579846516244105315 := by
  unfold tailWord_7334813
  simp only [CollatzResearch.WordTrace]
  refine ⟨267522607976232662174057093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178348405317488441449371395 267522607976232662174057093)
  ·
    refine ⟨50160488995543624157635705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267522607976232662174057093 50160488995543624157635705)
    ·
      refine ⟨37620366746657718118226779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50160488995543624157635705 37620366746657718118226779)
      ·
        refine ⟨56430550119986577177340169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37620366746657718118226779 56430550119986577177340169)
        ·
          refine ⟨42322912589989932883005127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56430550119986577177340169 42322912589989932883005127)
          ·
            refine ⟨63484368884984899324507691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42322912589989932883005127 63484368884984899324507691)
            ·
              refine ⟨95226553327477348986761537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63484368884984899324507691 95226553327477348986761537)
              ·
                refine ⟨71419914995608011740071153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95226553327477348986761537 71419914995608011740071153)
                ·
                  refine ⟨53564936246706008805053365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71419914995608011740071153 53564936246706008805053365)
                  ·
                    refine ⟨5021712773128688325473753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53564936246706008805053365 5021712773128688325473753)
                    ·
                      refine ⟨3766284579846516244105315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5021712773128688325473753 3766284579846516244105315)
                      ·
                        rfl

theorem cell23_7334813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_7334813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334813 prefixEnd_7334813 := by exact prefixLift 7334813
  have htrace : WordTrace (prefixWord ++ tailWord_7334813) baseStart_7334813 baseEnd_7334813 := by
    simpa [prefixWord, tailWord_7334813, baseEnd_7334813] using wordTrace_append hprefix tailTrace_7334813
  have hstable : (prefixWord ++ tailWord_7334813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334813).length < 2 ^ (prefixWord ++ tailWord_7334813).sum := by decide
  have hdescent : baseEnd_7334813 < baseStart_7334813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334823 : List Nat := [1, 1, 6, 1, 3, 1, 1, 1, 1, 7]
def baseStart_7334823 : Nat := 118140960795 + 7334823 * 2 ^ 59
def prefixEnd_7334823 : Nat := 4983230072969 + 3 ^ 40 * 7334823 * 2
def baseEnd_7334823 : Nat := 1255429904884353734993423

theorem tailTrace_7334823 : CollatzResearch.WordTrace tailWord_7334823 prefixEnd_7334823 1255429904884353734993423 := by
  unfold tailWord_7334823
  simp only [CollatzResearch.WordTrace]
  refine ⟨267522972706196433881921123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178348648470797622587947415 267522972706196433881921123)
  ·
    refine ⟨401284459059294650822881685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267522972706196433881921123 401284459059294650822881685)
    ·
      refine ⟨18810209018404436757322579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 401284459059294650822881685 18810209018404436757322579)
      ·
        refine ⟨28215313527606655135983869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18810209018404436757322579 28215313527606655135983869)
        ·
          refine ⟨10580742572852495675993951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28215313527606655135983869 10580742572852495675993951)
          ·
            refine ⟨15871113859278743513990927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10580742572852495675993951 15871113859278743513990927)
            ·
              refine ⟨23806670788918115270986391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15871113859278743513990927 23806670788918115270986391)
              ·
                refine ⟨35710006183377172906479587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23806670788918115270986391 35710006183377172906479587)
                ·
                  refine ⟨53565009275065759359719381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35710006183377172906479587 53565009275065759359719381)
                  ·
                    refine ⟨1255429904884353734993423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53565009275065759359719381 1255429904884353734993423)
                    ·
                      rfl

theorem cell23_7334823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_7334823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334823 prefixEnd_7334823 := by exact prefixLift 7334823
  have htrace : WordTrace (prefixWord ++ tailWord_7334823) baseStart_7334823 baseEnd_7334823 := by
    simpa [prefixWord, tailWord_7334823, baseEnd_7334823] using wordTrace_append hprefix tailTrace_7334823
  have hstable : (prefixWord ++ tailWord_7334823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334823).length < 2 ^ (prefixWord ++ tailWord_7334823).sum := by decide
  have hdescent : baseEnd_7334823 < baseStart_7334823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334887 : List Nat := [1, 1, 5, 2, 2, 1, 3, 3, 1, 4]
def baseStart_7334887 : Nat := 118140960795 + 7334887 * 2 ^ 59
def prefixEnd_7334887 : Nat := 4983230072969 + 3 ^ 40 * 7334887 * 2
def baseEnd_7334887 : Nat := 1255440859138316318193325

theorem tailTrace_7334887 : CollatzResearch.WordTrace tailWord_7334887 prefixEnd_7334887 1255440859138316318193325 := by
  unfold tailWord_7334887
  simp only [CollatzResearch.WordTrace]
  refine ⟨267525306977964572812250915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178350204651976381874833943 267525306977964572812250915)
  ·
    refine ⟨401287960466946859218376373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267525306977964572812250915 401287960466946859218376373)
    ·
      refine ⟨37620746293776268051722785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 401287960466946859218376373 37620746293776268051722785)
      ·
        refine ⟨28215559720332201038792089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37620746293776268051722785 28215559720332201038792089)
        ·
          refine ⟨21161669790249150779094067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28215559720332201038792089 21161669790249150779094067)
          ·
            refine ⟨31742504685373726168641101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21161669790249150779094067 31742504685373726168641101)
            ·
              refine ⟨11903439257015147313240413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31742504685373726168641101 11903439257015147313240413)
              ·
                refine ⟨4463789721380680242465155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11903439257015147313240413 4463789721380680242465155)
                ·
                  refine ⟨6695684582071020363697733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4463789721380680242465155 6695684582071020363697733)
                  ·
                    refine ⟨1255440859138316318193325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6695684582071020363697733 1255440859138316318193325)
                    ·
                      rfl

theorem cell23_7334887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_7334887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334887 prefixEnd_7334887 := by exact prefixLift 7334887
  have htrace : WordTrace (prefixWord ++ tailWord_7334887) baseStart_7334887 baseEnd_7334887 := by
    simpa [prefixWord, tailWord_7334887, baseEnd_7334887] using wordTrace_append hprefix tailTrace_7334887
  have hstable : (prefixWord ++ tailWord_7334887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334887).length < 2 ^ (prefixWord ++ tailWord_7334887).sum := by decide
  have hdescent : baseEnd_7334887 < baseStart_7334887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334896 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 5, 5]
def baseStart_7334896 : Nat := 118140960795 + 7334896 * 2 ^ 59
def prefixEnd_7334896 : Nat := 4983230072969 + 3 ^ 40 * 7334896 * 2
def baseEnd_7334896 : Nat := 1255442399580279806455811

theorem tailTrace_7334896 : CollatzResearch.WordTrace tailWord_7334896 prefixEnd_7334896 1255442399580279806455811 := by
  unfold tailWord_7334896
  simp only [CollatzResearch.WordTrace]
  refine ⟨133762817617465983674664271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178350423489954644899552361 133762817617465983674664271)
  ·
    refine ⟨200644226426198975511996407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133762817617465983674664271 200644226426198975511996407)
    ·
      refine ⟨300966339639298463267994611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200644226426198975511996407 300966339639298463267994611)
      ·
        refine ⟨451449509458947694901991917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300966339639298463267994611 451449509458947694901991917)
        ·
          refine ⟨169293566047105385588246969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451449509458947694901991917 169293566047105385588246969)
          ·
            refine ⟨126970174535329039191185227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169293566047105385588246969 126970174535329039191185227)
            ·
              refine ⟨190455261802993558786777841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126970174535329039191185227 190455261802993558786777841)
              ·
                refine ⟨142841446352245169090083381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190455261802993558786777841 142841446352245169090083381)
                ·
                  refine ⟨13391385595522984602195317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142841446352245169090083381 13391385595522984602195317)
                  ·
                    refine ⟨1255442399580279806455811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13391385595522984602195317 1255442399580279806455811)
                    ·
                      rfl

theorem cell23_7334896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 5, 5].length) (baseStart_7334896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334896 prefixEnd_7334896 := by exact prefixLift 7334896
  have htrace : WordTrace (prefixWord ++ tailWord_7334896) baseStart_7334896 baseEnd_7334896 := by
    simpa [prefixWord, tailWord_7334896, baseEnd_7334896] using wordTrace_append hprefix tailTrace_7334896
  have hstable : (prefixWord ++ tailWord_7334896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334896).length < 2 ^ (prefixWord ++ tailWord_7334896).sum := by decide
  have hdescent : baseEnd_7334896 < baseStart_7334896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334943 : List Nat := [1, 1, 2, 4, 1, 4, 1, 2, 1, 6]
def baseStart_7334943 : Nat := 118140960795 + 7334943 * 2 ^ 59
def prefixEnd_7334943 : Nat := 4983230072969 + 3 ^ 40 * 7334943 * 2
def baseEnd_7334943 : Nat := 1255450444110533578493239

theorem tailTrace_7334943 : CollatzResearch.WordTrace tailWord_7334943 prefixEnd_7334943 1255450444110533578493239 := by
  unfold tailWord_7334943
  simp only [CollatzResearch.WordTrace]
  refine ⟨267527349465761694376289483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178351566310507796250859655 267527349465761694376289483)
  ·
    refine ⟨401291024198642541564434225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267527349465761694376289483 401291024198642541564434225)
    ·
      refine ⟨300968268148981906173325669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401291024198642541564434225 300968268148981906173325669)
      ·
        refine ⟨56431550277934107407498563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300968268148981906173325669 56431550277934107407498563)
        ·
          refine ⟨84647325416901161111247845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56431550277934107407498563 84647325416901161111247845)
          ·
            refine ⟨15871373515668967708358971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84647325416901161111247845 15871373515668967708358971)
            ·
              refine ⟨23807060273503451562538457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15871373515668967708358971 23807060273503451562538457)
              ·
                refine ⟨17855295205127588671903843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23807060273503451562538457 17855295205127588671903843)
                ·
                  refine ⟨26782942807691383007855765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17855295205127588671903843 26782942807691383007855765)
                  ·
                    refine ⟨1255450444110533578493239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26782942807691383007855765 1255450444110533578493239)
                    ·
                      rfl

theorem cell23_7334943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 6].length) (baseStart_7334943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334943 prefixEnd_7334943 := by exact prefixLift 7334943
  have htrace : WordTrace (prefixWord ++ tailWord_7334943) baseStart_7334943 baseEnd_7334943 := by
    simpa [prefixWord, tailWord_7334943, baseEnd_7334943] using wordTrace_append hprefix tailTrace_7334943
  have hstable : (prefixWord ++ tailWord_7334943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334943).length < 2 ^ (prefixWord ++ tailWord_7334943).sum := by decide
  have hdescent : baseEnd_7334943 < baseStart_7334943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334960 : List Nat := [2, 1, 1, 1, 2, 4, 4, 2, 2, 4]
def baseStart_7334960 : Nat := 118140960795 + 7334960 * 2 ^ 59
def prefixEnd_7334960 : Nat := 4983230072969 + 3 ^ 40 * 7334960 * 2
def baseEnd_7334960 : Nat := 1255453353834242389655713

theorem tailTrace_7334960 : CollatzResearch.WordTrace tailWord_7334960 prefixEnd_7334960 1255453353834242389655713 := by
  unfold tailWord_7334960
  simp only [CollatzResearch.WordTrace]
  refine ⟨133763984753350053139829167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178351979671133404186438889 133763984753350053139829167)
  ·
    refine ⟨200645977130025079709743751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133763984753350053139829167 200645977130025079709743751)
    ·
      refine ⟨300968965695037619564615627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200645977130025079709743751 300968965695037619564615627)
      ·
        refine ⟨451453448542556429346923441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300968965695037619564615627 451453448542556429346923441)
        ·
          refine ⟨338590086406917322010192581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451453448542556429346923441 338590086406917322010192581)
          ·
            refine ⟨63485641201296997876911109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338590086406917322010192581 63485641201296997876911109)
            ·
              refine ⟨11903557725243187101920833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63485641201296997876911109 11903557725243187101920833)
              ·
                refine ⟨8927668293932390326440625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11903557725243187101920833 8927668293932390326440625)
                ·
                  refine ⟨6695751220449292744830469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8927668293932390326440625 6695751220449292744830469)
                  ·
                    refine ⟨1255453353834242389655713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6695751220449292744830469 1255453353834242389655713)
                    ·
                      rfl

theorem cell23_7334960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 4, 2, 2, 4].length) (baseStart_7334960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334960 prefixEnd_7334960 := by exact prefixLift 7334960
  have htrace : WordTrace (prefixWord ++ tailWord_7334960) baseStart_7334960 baseEnd_7334960 := by
    simpa [prefixWord, tailWord_7334960, baseEnd_7334960] using wordTrace_append hprefix tailTrace_7334960
  have hstable : (prefixWord ++ tailWord_7334960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334960).length < 2 ^ (prefixWord ++ tailWord_7334960).sum := by decide
  have hdescent : baseEnd_7334960 < baseStart_7334960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334973 : List Nat := [1, 4, 1, 3, 1, 2, 3, 8]
def baseStart_7334973 : Nat := 118140960795 + 7334973 * 2 ^ 59
def prefixEnd_7334973 : Nat := 4983230072969 + 3 ^ 40 * 7334973 * 2
def baseEnd_7334973 : Nat := 139495064324119837707577

theorem tailTrace_7334973 : CollatzResearch.WordTrace tailWord_7334973 prefixEnd_7334973 139495064324119837707577 := by
  unfold tailWord_7334973
  simp only [CollatzResearch.WordTrace]
  refine ⟨267528443655653009499881573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178352295770435339666587715 267528443655653009499881573)
  ·
    refine ⟨50161583185434939281227795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267528443655653009499881573 50161583185434939281227795)
    ·
      refine ⟨75242374778152408921841693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50161583185434939281227795 75242374778152408921841693)
      ·
        refine ⟨28215890541807153345690635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75242374778152408921841693 28215890541807153345690635)
        ·
          refine ⟨42323835812710730018535953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28215890541807153345690635 42323835812710730018535953)
          ·
            refine ⟨31742876859533047513901965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42323835812710730018535953 31742876859533047513901965)
            ·
              refine ⟨11903578822324892817713237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31742876859533047513901965 11903578822324892817713237)
              ·
                refine ⟨139495064324119837707577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11903578822324892817713237 139495064324119837707577)
                ·
                  rfl

theorem cell23_7334973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 3, 8].length) (baseStart_7334973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334973 prefixEnd_7334973 := by exact prefixLift 7334973
  have htrace : WordTrace (prefixWord ++ tailWord_7334973) baseStart_7334973 baseEnd_7334973 := by
    simpa [prefixWord, tailWord_7334973, baseEnd_7334973] using wordTrace_append hprefix tailTrace_7334973
  have hstable : (prefixWord ++ tailWord_7334973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334973).length < 2 ^ (prefixWord ++ tailWord_7334973).sum := by decide
  have hdescent : baseEnd_7334973 < baseStart_7334973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334998 : List Nat := [5, 2, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_7334998 : Nat := 118140960795 + 7334998 * 2 ^ 59
def prefixEnd_7334998 : Nat := 4983230072969 + 3 ^ 40 * 7334998 * 2
def baseEnd_7334998 : Nat := 1255459857922532673430655

theorem tailTrace_7334998 : CollatzResearch.WordTrace tailWord_7334998 prefixEnd_7334998 1255459857922532673430655 := by
  unfold tailWord_7334998
  simp only [CollatzResearch.WordTrace]
  refine ⟨16720584717535152423096353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178352903653708292513027765 16720584717535152423096353)
  ·
    refine ⟨12540438538151364317322265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16720584717535152423096353 12540438538151364317322265)
    ·
      refine ⟨9405328903613523237991699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12540438538151364317322265 9405328903613523237991699)
      ·
        refine ⟨14107993355420284856987549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9405328903613523237991699 14107993355420284856987549)
        ·
          refine ⟨5290497508282606821370331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14107993355420284856987549 5290497508282606821370331)
          ·
            refine ⟨7935746262423910232055497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5290497508282606821370331 7935746262423910232055497)
            ·
              refine ⟨5951809696817932674041623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7935746262423910232055497 5951809696817932674041623)
              ·
                refine ⟨8927714545226899011062435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5951809696817932674041623 8927714545226899011062435)
                ·
                  refine ⟨13391571817840348516593653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8927714545226899011062435 13391571817840348516593653)
                  ·
                    refine ⟨1255459857922532673430655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13391571817840348516593653 1255459857922532673430655)
                    ·
                      rfl

theorem cell23_7334998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_7334998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334998 prefixEnd_7334998 := by exact prefixLift 7334998
  have htrace : WordTrace (prefixWord ++ tailWord_7334998) baseStart_7334998 baseEnd_7334998 := by
    simpa [prefixWord, tailWord_7334998, baseEnd_7334998] using wordTrace_append hprefix tailTrace_7334998
  have hstable : (prefixWord ++ tailWord_7334998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334998).length < 2 ^ (prefixWord ++ tailWord_7334998).sum := by decide
  have hdescent : baseEnd_7334998 < baseStart_7334998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335000 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 4, 1, 3]
def baseStart_7335000 : Nat := 118140960795 + 7335000 * 2 ^ 59
def prefixEnd_7335000 : Nat := 4983230072969 + 3 ^ 40 * 7335000 * 2
def baseEnd_7335000 : Nat := 3766380600728907012466955

theorem tailTrace_7335000 : CollatzResearch.WordTrace tailWord_7335000 prefixEnd_7335000 3766380600728907012466955 := by
  unfold tailWord_7335000
  simp only [CollatzResearch.WordTrace]
  refine ⟨133764714213277596555557227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178352952284370128740742969 133764714213277596555557227)
  ·
    refine ⟨200647071319916394833335841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133764714213277596555557227 200647071319916394833335841)
    ·
      refine ⟨150485303489937296125001881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200647071319916394833335841 150485303489937296125001881)
      ·
        refine ⟨112863977617452972093751411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150485303489937296125001881 112863977617452972093751411)
        ·
          refine ⟨169295966426179458140627117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112863977617452972093751411 169295966426179458140627117)
          ·
            refine ⟨63485987409817296802735169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169295966426179458140627117 63485987409817296802735169)
            ·
              refine ⟨47614490557362972602051377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63485987409817296802735169 47614490557362972602051377)
              ·
                refine ⟨35710867918022229451538533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47614490557362972602051377 35710867918022229451538533)
                ·
                  refine ⟨6695787734629168022163475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35710867918022229451538533 6695787734629168022163475)
                  ·
                    refine ⟨10043681601943752033245213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6695787734629168022163475 10043681601943752033245213)
                    ·
                      refine ⟨3766380600728907012466955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10043681601943752033245213 3766380600728907012466955)
                      ·
                        rfl

theorem cell23_7335000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 4, 1, 3].length) (baseStart_7335000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335000 prefixEnd_7335000 := by exact prefixLift 7335000
  have htrace : WordTrace (prefixWord ++ tailWord_7335000) baseStart_7335000 baseEnd_7335000 := by
    simpa [prefixWord, tailWord_7335000, baseEnd_7335000] using wordTrace_append hprefix tailTrace_7335000
  have hstable : (prefixWord ++ tailWord_7335000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335000).length < 2 ^ (prefixWord ++ tailWord_7335000).sum := by decide
  have hdescent : baseEnd_7335000 < baseStart_7335000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335017 : List Nat := [1, 2, 1, 1, 1, 6, 3, 2, 2, 1, 3]
def baseStart_7335017 : Nat := 118140960795 + 7335017 * 2 ^ 59
def prefixEnd_7335017 : Nat := 4983230072969 + 3 ^ 40 * 7335017 * 2
def baseEnd_7335017 : Nat := 3766389329900033445954377

theorem tailTrace_7335017 : CollatzResearch.WordTrace tailWord_7335017 prefixEnd_7335017 3766389329900033445954377 := by
  unfold tailWord_7335017
  simp only [CollatzResearch.WordTrace]
  refine ⟨267530048467493605014483305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178353365644995736676322203 267530048467493605014483305)
  ·
    refine ⟨200647536350620203760862479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267530048467493605014483305 200647536350620203760862479)
    ·
      refine ⟨300971304525930305641293719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200647536350620203760862479 300971304525930305641293719)
      ·
        refine ⟨451456956788895458461940579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300971304525930305641293719 451456956788895458461940579)
        ·
          refine ⟨677185435183343187692910869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451456956788895458461940579 677185435183343187692910869)
          ·
            refine ⟨31743067274219211923105197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 677185435183343187692910869 31743067274219211923105197)
            ·
              refine ⟨11903650227832204471164449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31743067274219211923105197 11903650227832204471164449)
              ·
                refine ⟨8927737670874153353373337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11903650227832204471164449 8927737670874153353373337)
                ·
                  refine ⟨6695803253155615015030003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8927737670874153353373337 6695803253155615015030003)
                  ·
                    refine ⟨10043704879733422522545005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6695803253155615015030003 10043704879733422522545005)
                    ·
                      refine ⟨3766389329900033445954377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10043704879733422522545005 3766389329900033445954377)
                      ·
                        rfl

theorem cell23_7335017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 1, 3].length) (baseStart_7335017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335017 prefixEnd_7335017 := by exact prefixLift 7335017
  have htrace : WordTrace (prefixWord ++ tailWord_7335017) baseStart_7335017 baseEnd_7335017 := by
    simpa [prefixWord, tailWord_7335017, baseEnd_7335017] using wordTrace_append hprefix tailTrace_7335017
  have hstable : (prefixWord ++ tailWord_7335017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335017).length < 2 ^ (prefixWord ++ tailWord_7335017).sum := by decide
  have hdescent : baseEnd_7335017 < baseStart_7335017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335038 : List Nat := [4, 2, 4, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_7335038 : Nat := 118140960795 + 7335038 * 2 ^ 59
def prefixEnd_7335038 : Nat := 4983230072969 + 3 ^ 40 * 7335038 * 2
def baseEnd_7335038 : Nat := 3766400112993777863791781

theorem tailTrace_7335038 : CollatzResearch.WordTrace tailWord_7335038 prefixEnd_7335038 3766400112993777863791781 := by
  unfold tailWord_7335038
  simp only [CollatzResearch.WordTrace]
  refine ⟨33441351800052190700124721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178353876266945017067331845 33441351800052190700124721)
  ·
    refine ⟨25081013850039143025093541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33441351800052190700124721 25081013850039143025093541)
    ·
      refine ⟨4702690096882339317205039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25081013850039143025093541 4702690096882339317205039)
      ·
        refine ⟨7054035145323508975807559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4702690096882339317205039 7054035145323508975807559)
        ·
          refine ⟨10581052717985263463711339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7054035145323508975807559 10581052717985263463711339)
          ·
            refine ⟨15871579076977895195567009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10581052717985263463711339 15871579076977895195567009)
            ·
              refine ⟨11903684307733421396675257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15871579076977895195567009 11903684307733421396675257)
              ·
                refine ⟨8927763230800066047506443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11903684307733421396675257 8927763230800066047506443)
                ·
                  refine ⟨13391644846200099071259665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8927763230800066047506443 13391644846200099071259665)
                  ·
                    refine ⟨10043733634650074303444749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13391644846200099071259665 10043733634650074303444749)
                    ·
                      refine ⟨3766400112993777863791781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10043733634650074303444749 3766400112993777863791781)
                      ·
                        rfl

theorem cell23_7335038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_7335038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335038 prefixEnd_7335038 := by exact prefixLift 7335038
  have htrace : WordTrace (prefixWord ++ tailWord_7335038) baseStart_7335038 baseEnd_7335038 := by
    simpa [prefixWord, tailWord_7335038, baseEnd_7335038] using wordTrace_append hprefix tailTrace_7335038
  have hstable : (prefixWord ++ tailWord_7335038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335038).length < 2 ^ (prefixWord ++ tailWord_7335038).sum := by decide
  have hdescent : baseEnd_7335038 < baseStart_7335038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335043 : List Nat := [1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 5]
def baseStart_7335043 : Nat := 118140960795 + 7335043 * 2 ^ 59
def prefixEnd_7335043 : Nat := 4983230072969 + 3 ^ 40 * 7335043 * 2
def baseEnd_7335043 : Nat := 3766402680397050344229257

theorem tailTrace_7335043 : CollatzResearch.WordTrace tailWord_7335043 prefixEnd_7335043 3766402680397050344229257 := by
  unfold tailWord_7335043
  simp only [CollatzResearch.WordTrace]
  refine ⟨267530996765399411454929783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178353997843599607636619855 267530996765399411454929783)
  ·
    refine ⟨401296495148099117182394675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267530996765399411454929783 401296495148099117182394675)
    ·
      refine ⟨601944742722148675773592013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401296495148099117182394675 601944742722148675773592013)
      ·
        refine ⟨225729278520805753415097005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 601944742722148675773592013 225729278520805753415097005)
        ·
          refine ⟨84648479445302157530661377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225729278520805753415097005 84648479445302157530661377)
          ·
            refine ⟨63486359583976618147996033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84648479445302157530661377 63486359583976618147996033)
            ·
              refine ⟨47614769687982463610997025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63486359583976618147996033 47614769687982463610997025)
              ·
                refine ⟨35711077265986847708247769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47614769687982463610997025 35711077265986847708247769)
                ·
                  refine ⟨26783307949490135781185827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35711077265986847708247769 26783307949490135781185827)
                  ·
                    refine ⟨40174961924235203671778741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26783307949490135781185827 40174961924235203671778741)
                    ·
                      refine ⟨3766402680397050344229257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40174961924235203671778741 3766402680397050344229257)
                      ·
                        rfl

theorem cell23_7335043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_7335043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335043 prefixEnd_7335043 := by exact prefixLift 7335043
  have htrace : WordTrace (prefixWord ++ tailWord_7335043) baseStart_7335043 baseEnd_7335043 := by
    simpa [prefixWord, tailWord_7335043, baseEnd_7335043] using wordTrace_append hprefix tailTrace_7335043
  have hstable : (prefixWord ++ tailWord_7335043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335043).length < 2 ^ (prefixWord ++ tailWord_7335043).sum := by decide
  have hdescent : baseEnd_7335043 < baseStart_7335043 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335044 : List Nat := [2, 3, 2, 1, 2, 3, 2, 2, 1, 3, 2]
def baseStart_7335044 : Nat := 118140960795 + 7335044 * 2 ^ 59
def prefixEnd_7335044 : Nat := 4983230072969 + 3 ^ 40 * 7335044 * 2
def baseEnd_7335044 : Nat := 3766403193877704840316753

theorem tailTrace_7335044 : CollatzResearch.WordTrace tailWord_7335044 prefixEnd_7335044 3766403193877704840316753 := by
  unfold tailWord_7335044
  simp only [CollatzResearch.WordTrace]
  refine ⟨133765516619197894312858093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178354022158930525750477457 133765516619197894312858093)
  ·
    refine ⟨50162068732199210367321785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133765516619197894312858093 50162068732199210367321785)
    ·
      refine ⟨37621551549149407775491339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50162068732199210367321785 37621551549149407775491339)
      ·
        refine ⟨56432327323724111663237009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37621551549149407775491339 56432327323724111663237009)
        ·
          refine ⟨42324245492793083747427757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56432327323724111663237009 42324245492793083747427757)
          ·
            refine ⟨15871592059797406405285409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42324245492793083747427757 15871592059797406405285409)
            ·
              refine ⟨11903694044848054803964057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15871592059797406405285409 11903694044848054803964057)
              ·
                refine ⟨8927770533636041102973043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11903694044848054803964057 8927770533636041102973043)
                ·
                  refine ⟨13391655800454061654459565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8927770533636041102973043 13391655800454061654459565)
                  ·
                    refine ⟨5021870925170273120422337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13391655800454061654459565 5021870925170273120422337)
                    ·
                      refine ⟨3766403193877704840316753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5021870925170273120422337 3766403193877704840316753)
                      ·
                        rfl

theorem cell23_7335044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 1, 3, 2].length) (baseStart_7335044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335044 prefixEnd_7335044 := by exact prefixLift 7335044
  have htrace : WordTrace (prefixWord ++ tailWord_7335044) baseStart_7335044 baseEnd_7335044 := by
    simpa [prefixWord, tailWord_7335044, baseEnd_7335044] using wordTrace_append hprefix tailTrace_7335044
  have hstable : (prefixWord ++ tailWord_7335044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335044).length < 2 ^ (prefixWord ++ tailWord_7335044).sum := by decide
  have hdescent : baseEnd_7335044 < baseStart_7335044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335073 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 7]
def baseStart_7335073 : Nat := 118140960795 + 7335073 * 2 ^ 59
def prefixEnd_7335073 : Nat := 4983230072969 + 3 ^ 40 * 7335073 * 2
def baseEnd_7335073 : Nat := 3766418084816685226854119

theorem tailTrace_7335073 : CollatzResearch.WordTrace tailWord_7335073 prefixEnd_7335073 3766418084816685226854119 := by
  unfold tailWord_7335073
  simp only [CollatzResearch.WordTrace]
  refine ⟨267532090955290726578521873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178354727303527151052347915 267532090955290726578521873)
  ·
    refine ⟨200649068216468044933891405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267532090955290726578521873 200649068216468044933891405)
    ·
      refine ⟨75243400581175516850209277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200649068216468044933891405 75243400581175516850209277)
      ·
        refine ⟨28216275217940818818828479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75243400581175516850209277 28216275217940818818828479)
        ·
          refine ⟨42324412826911228228242719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28216275217940818818828479 42324412826911228228242719)
          ·
            refine ⟨63486619240366842342364079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42324412826911228228242719 63486619240366842342364079)
            ·
              refine ⟨95229928860550263513546119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63486619240366842342364079 95229928860550263513546119)
              ·
                refine ⟨142844893290825395270319179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95229928860550263513546119 142844893290825395270319179)
                ·
                  refine ⟨214267339936238092905478769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142844893290825395270319179 214267339936238092905478769)
                  ·
                    refine ⟨160700504952178569679109077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 214267339936238092905478769 160700504952178569679109077)
                    ·
                      refine ⟨3766418084816685226854119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160700504952178569679109077 3766418084816685226854119)
                      ·
                        rfl

theorem cell23_7335073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_7335073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335073 prefixEnd_7335073 := by exact prefixLift 7335073
  have htrace : WordTrace (prefixWord ++ tailWord_7335073) baseStart_7335073 baseEnd_7335073 := by
    simpa [prefixWord, tailWord_7335073, baseEnd_7335073] using wordTrace_append hprefix tailTrace_7335073
  have hstable : (prefixWord ++ tailWord_7335073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335073).length < 2 ^ (prefixWord ++ tailWord_7335073).sum := by decide
  have hdescent : baseEnd_7335073 < baseStart_7335073 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335113 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 5, 3, 4]
def baseStart_7335113 : Nat := 118140960795 + 7335113 * 2 ^ 59
def prefixEnd_7335113 : Nat := 4983230072969 + 3 ^ 40 * 7335113 * 2
def baseEnd_7335113 : Nat := 3766438624042865070353935

theorem tailTrace_7335113 : CollatzResearch.WordTrace tailWord_7335113 prefixEnd_7335113 3766438624042865070353935 := by
  unfold tailWord_7335113
  simp only [CollatzResearch.WordTrace]
  refine ⟨267533549875145813409977993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178355699916763875606651995 267533549875145813409977993)
  ·
    refine ⟨200650162406359360057483495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267533549875145813409977993 200650162406359360057483495)
    ·
      refine ⟨300975243609539040086225243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200650162406359360057483495 300975243609539040086225243)
      ·
        refine ⟨451462865414308560129337865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300975243609539040086225243 451462865414308560129337865)
        ·
          refine ⟨338597149060731420097003399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451462865414308560129337865 338597149060731420097003399)
          ·
            refine ⟨507895723591097130145505099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338597149060731420097003399 507895723591097130145505099)
            ·
              refine ⟨761843585386645695218257649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507895723591097130145505099 761843585386645695218257649)
              ·
                refine ⟨571382689039984271413693237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761843585386645695218257649 571382689039984271413693237)
                ·
                  refine ⟨53567127097498525445033741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 571382689039984271413693237 53567127097498525445033741)
                  ·
                    refine ⟨20087672661561947041887653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53567127097498525445033741 20087672661561947041887653)
                    ·
                      refine ⟨3766438624042865070353935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20087672661561947041887653 3766438624042865070353935)
                      ·
                        rfl

theorem cell23_7335113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 5, 3, 4].length) (baseStart_7335113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335113 prefixEnd_7335113 := by exact prefixLift 7335113
  have htrace : WordTrace (prefixWord ++ tailWord_7335113) baseStart_7335113 baseEnd_7335113 := by
    simpa [prefixWord, tailWord_7335113, baseEnd_7335113] using wordTrace_append hprefix tailTrace_7335113
  have hstable : (prefixWord ++ tailWord_7335113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335113).length < 2 ^ (prefixWord ++ tailWord_7335113).sum := by decide
  have hdescent : baseEnd_7335113 < baseStart_7335113 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335147 : List Nat := [1, 1, 1, 1, 2, 7, 1, 1, 2, 4, 2]
def baseStart_7335147 : Nat := 118140960795 + 7335147 * 2 ^ 59
def prefixEnd_7335147 : Nat := 4983230072969 + 3 ^ 40 * 7335147 * 2
def baseEnd_7335147 : Nat := 3766456082385117937328779

theorem tailTrace_7335147 : CollatzResearch.WordTrace tailWord_7335147 prefixEnd_7335147 3766456082385117937328779 := by
  unfold tailWord_7335147
  simp only [CollatzResearch.WordTrace]
  refine ⟨267534789957022637216715695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178356526638015091477810463 267534789957022637216715695)
  ·
    refine ⟨401302184935533955825073543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267534789957022637216715695 401302184935533955825073543)
    ·
      refine ⟨601953277403300933737610315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401302184935533955825073543 601953277403300933737610315)
      ·
        refine ⟨902929916104951400606415473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601953277403300933737610315 902929916104951400606415473)
        ·
          refine ⟨677197437078713550454811605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 902929916104951400606415473 677197437078713550454811605)
          ·
            refine ⟨15871814931532348838784647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 677197437078713550454811605 15871814931532348838784647)
            ·
              refine ⟨23807722397298523258176971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15871814931532348838784647 23807722397298523258176971)
              ·
                refine ⟨35711583595947784887265457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23807722397298523258176971 35711583595947784887265457)
                ·
                  refine ⟨26783687696960838665449093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35711583595947784887265457 26783687696960838665449093)
                  ·
                    refine ⟨5021941443180157249771705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26783687696960838665449093 5021941443180157249771705)
                    ·
                      refine ⟨3766456082385117937328779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5021941443180157249771705 3766456082385117937328779)
                      ·
                        rfl

theorem cell23_7335147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 4, 2].length) (baseStart_7335147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335147 prefixEnd_7335147 := by exact prefixLift 7335147
  have htrace : WordTrace (prefixWord ++ tailWord_7335147) baseStart_7335147 baseEnd_7335147 := by
    simpa [prefixWord, tailWord_7335147, baseEnd_7335147] using wordTrace_append hprefix tailTrace_7335147
  have hstable : (prefixWord ++ tailWord_7335147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335147).length < 2 ^ (prefixWord ++ tailWord_7335147).sum := by decide
  have hdescent : baseEnd_7335147 < baseStart_7335147 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335153 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 10]
def baseStart_7335153 : Nat := 118140960795 + 7335153 * 2 ^ 59
def prefixEnd_7335153 : Nat := 4983230072969 + 3 ^ 40 * 7335153 * 2
def baseEnd_7335153 : Nat := 418495462585449434872639

theorem tailTrace_7335153 : CollatzResearch.WordTrace tailWord_7335153 prefixEnd_7335153 418495462585449434872639 := by
  unfold tailWord_7335153
  simp only [CollatzResearch.WordTrace]
  refine ⟨267535008795000900241434113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178356672530000600160956075 267535008795000900241434113)
  ·
    refine ⟨200651256596250675181075585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267535008795000900241434113 200651256596250675181075585)
    ·
      refine ⟨150488442447188006385806689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200651256596250675181075585 150488442447188006385806689)
      ·
        refine ⟨112866331835391004789355017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150488442447188006385806689 112866331835391004789355017)
        ·
          refine ⟨84649748876543253592016263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112866331835391004789355017 84649748876543253592016263)
          ·
            refine ⟨126974623314814880388024395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84649748876543253592016263 126974623314814880388024395)
            ·
              refine ⟨190461934972222320582036593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126974623314814880388024395 190461934972222320582036593)
              ·
                refine ⟨142846451229166740436527445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190461934972222320582036593 142846451229166740436527445)
                ·
                  refine ⟨418495462585449434872639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 142846451229166740436527445 418495462585449434872639)
                  ·
                    rfl

theorem cell23_7335153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 10].length) (baseStart_7335153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335153 prefixEnd_7335153 := by exact prefixLift 7335153
  have htrace : WordTrace (prefixWord ++ tailWord_7335153) baseStart_7335153 baseEnd_7335153 := by
    simpa [prefixWord, tailWord_7335153, baseEnd_7335153] using wordTrace_append hprefix tailTrace_7335153
  have hstable : (prefixWord ++ tailWord_7335153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335153).length < 2 ^ (prefixWord ++ tailWord_7335153).sum := by decide
  have hdescent : baseEnd_7335153 < baseStart_7335153 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335164 : List Nat := [2, 2, 2, 1, 5, 2, 1, 1, 2, 1, 4]
def baseStart_7335164 : Nat := 118140960795 + 7335164 * 2 ^ 59
def prefixEnd_7335164 : Nat := 4983230072969 + 3 ^ 40 * 7335164 * 2
def baseEnd_7335164 : Nat := 3766464811556244370816201

theorem tailTrace_7335164 : CollatzResearch.WordTrace tailWord_7335164 prefixEnd_7335164 3766464811556244370816201 := by
  unfold tailWord_7335164
  simp only [CollatzResearch.WordTrace]
  refine ⟨133767704998980524560042273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178356939998640699413389697 133767704998980524560042273)
  ·
    refine ⟨100325778749235393420031705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133767704998980524560042273 100325778749235393420031705)
    ·
      refine ⟨75244334061926545065023779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100325778749235393420031705 75244334061926545065023779)
      ·
        refine ⟨112866501092889817597535669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75244334061926545065023779 112866501092889817597535669)
        ·
          refine ⟨10581234477458420399768969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112866501092889817597535669 10581234477458420399768969)
          ·
            refine ⟨7935925858093815299826727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10581234477458420399768969 7935925858093815299826727)
            ·
              refine ⟨11903888787140722949740091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7935925858093815299826727 11903888787140722949740091)
              ·
                refine ⟨17855833180711084424610137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11903888787140722949740091 17855833180711084424610137)
                ·
                  refine ⟨13391874885533313318457603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17855833180711084424610137 13391874885533313318457603)
                  ·
                    refine ⟨20087812328299969977686405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13391874885533313318457603 20087812328299969977686405)
                    ·
                      refine ⟨3766464811556244370816201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20087812328299969977686405 3766464811556244370816201)
                      ·
                        rfl

theorem cell23_7335164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_7335164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335164 prefixEnd_7335164 := by exact prefixLift 7335164
  have htrace : WordTrace (prefixWord ++ tailWord_7335164) baseStart_7335164 baseEnd_7335164 := by
    simpa [prefixWord, tailWord_7335164, baseEnd_7335164] using wordTrace_append hprefix tailTrace_7335164
  have hstable : (prefixWord ++ tailWord_7335164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335164).length < 2 ^ (prefixWord ++ tailWord_7335164).sum := by decide
  have hdescent : baseEnd_7335164 < baseStart_7335164 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335167 : List Nat := [1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 3]
def baseStart_7335167 : Nat := 118140960795 + 7335167 * 2 ^ 59
def prefixEnd_7335167 : Nat := 4983230072969 + 3 ^ 40 * 7335167 * 2
def baseEnd_7335167 : Nat := 3766466351998207859078687

theorem tailTrace_7335167 : CollatzResearch.WordTrace tailWord_7335167 prefixEnd_7335167 3766466351998207859078687 := by
  unfold tailWord_7335167
  simp only [CollatzResearch.WordTrace]
  refine ⟨267535519416950180632443755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178357012944633453754962503 267535519416950180632443755)
  ·
    refine ⟨401303279125425270948665633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267535519416950180632443755 401303279125425270948665633)
    ·
      refine ⟨300977459344068953211499225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401303279125425270948665633 300977459344068953211499225)
      ·
        refine ⟨225733094508051714908624419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300977459344068953211499225 225733094508051714908624419)
        ·
          refine ⟨338599641762077572362936629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225733094508051714908624419 338599641762077572362936629)
          ·
            refine ⟨31743716415194772409025309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 338599641762077572362936629 31743716415194772409025309)
            ·
              refine ⟨11903893655698039653384491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31743716415194772409025309 11903893655698039653384491)
              ·
                refine ⟨17855840483547059480076737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11903893655698039653384491 17855840483547059480076737)
                ·
                  refine ⟨13391880362660294610057553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17855840483547059480076737 13391880362660294610057553)
                  ·
                    refine ⟨10043910271995220957543165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13391880362660294610057553 10043910271995220957543165)
                    ·
                      refine ⟨3766466351998207859078687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10043910271995220957543165 3766466351998207859078687)
                      ·
                        rfl

theorem cell23_7335167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_7335167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335167 prefixEnd_7335167 := by exact prefixLift 7335167
  have htrace : WordTrace (prefixWord ++ tailWord_7335167) baseStart_7335167 baseEnd_7335167 := by
    simpa [prefixWord, tailWord_7335167, baseEnd_7335167] using wordTrace_append hprefix tailTrace_7335167
  have hstable : (prefixWord ++ tailWord_7335167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335167).length < 2 ^ (prefixWord ++ tailWord_7335167).sum := by decide
  have hdescent : baseEnd_7335167 < baseStart_7335167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335217 : List Nat := [1, 2, 2, 3, 3, 1, 1, 4, 1, 5]
def baseStart_7335217 : Nat := 118140960795 + 7335217 * 2 ^ 59
def prefixEnd_7335217 : Nat := 4983230072969 + 3 ^ 40 * 7335217 * 2
def baseEnd_7335217 : Nat := 1255497342010310887817819

theorem tailTrace_7335217 : CollatzResearch.WordTrace tailWord_7335217 prefixEnd_7335217 1255497342010310887817819 := by
  unfold tailWord_7335217
  simp only [CollatzResearch.WordTrace]
  refine ⟨267537343066769039171763905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178358228711179359447842603 267537343066769039171763905)
  ·
    refine ⟨200653007300076779378822929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267537343066769039171763905 200653007300076779378822929)
    ·
      refine ⟨150489755475057584534117197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200653007300076779378822929 150489755475057584534117197)
      ·
        refine ⟨56433658303146594200293949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150489755475057584534117197 56433658303146594200293949)
        ·
          refine ⟨21162621863679972825110231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56433658303146594200293949 21162621863679972825110231)
          ·
            refine ⟨31743932795519959237665347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21162621863679972825110231 31743932795519959237665347)
            ·
              refine ⟨47615899193279938856498021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31743932795519959237665347 47615899193279938856498021)
              ·
                refine ⟨8927981098739988535593379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47615899193279938856498021 8927981098739988535593379)
                ·
                  refine ⟨13391971648109982803390069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8927981098739988535593379 13391971648109982803390069)
                  ·
                    refine ⟨1255497342010310887817819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13391971648109982803390069 1255497342010310887817819)
                    ·
                      rfl

theorem cell23_7335217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_7335217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335217 prefixEnd_7335217 := by exact prefixLift 7335217
  have htrace : WordTrace (prefixWord ++ tailWord_7335217) baseStart_7335217 baseEnd_7335217 := by
    simpa [prefixWord, tailWord_7335217, baseEnd_7335217] using wordTrace_append hprefix tailTrace_7335217
  have hstable : (prefixWord ++ tailWord_7335217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335217).length < 2 ^ (prefixWord ++ tailWord_7335217).sum := by decide
  have hdescent : baseEnd_7335217 < baseStart_7335217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335231 : List Nat := [1, 1, 2, 2, 4, 2, 3, 3, 1, 1, 3]
def baseStart_7335231 : Nat := 118140960795 + 7335231 * 2 ^ 59
def prefixEnd_7335231 : Nat := 4983230072969 + 3 ^ 40 * 7335231 * 2
def baseEnd_7335231 : Nat := 3766499214760095608678393

theorem tailTrace_7335231 : CollatzResearch.WordTrace tailWord_7335231 prefixEnd_7335231 3766499214760095608678393 := by
  unfold tailWord_7335231
  simp only [CollatzResearch.WordTrace]
  refine ⟨267537853688718319562773547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178358569125812213041849031 267537853688718319562773547)
  ·
    refine ⟨401306780533077479344160321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267537853688718319562773547 401306780533077479344160321)
    ·
      refine ⟨300980085399808109508120241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401306780533077479344160321 300980085399808109508120241)
      ·
        refine ⟨225735064049856082131090181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300980085399808109508120241 225735064049856082131090181)
        ·
          refine ⟨42325324509348015399579409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225735064049856082131090181 42325324509348015399579409)
          ·
            refine ⟨31743993382011011549684557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42325324509348015399579409 31743993382011011549684557)
            ·
              refine ⟨11903997518254129331131709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31743993382011011549684557 11903997518254129331131709)
              ·
                refine ⟨4463999069345298499174391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11903997518254129331131709 4463999069345298499174391)
                ·
                  refine ⟨6695998604017947748761587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4463999069345298499174391 6695998604017947748761587)
                  ·
                    refine ⟨10043997906026921623142381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6695998604017947748761587 10043997906026921623142381)
                    ·
                      refine ⟨3766499214760095608678393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10043997906026921623142381 3766499214760095608678393)
                      ·
                        rfl

theorem cell23_7335231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 3, 1, 1, 3].length) (baseStart_7335231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335231 prefixEnd_7335231 := by exact prefixLift 7335231
  have htrace : WordTrace (prefixWord ++ tailWord_7335231) baseStart_7335231 baseEnd_7335231 := by
    simpa [prefixWord, tailWord_7335231, baseEnd_7335231] using wordTrace_append hprefix tailTrace_7335231
  have hstable : (prefixWord ++ tailWord_7335231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335231).length < 2 ^ (prefixWord ++ tailWord_7335231).sum := by decide
  have hdescent : baseEnd_7335231 < baseStart_7335231 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335264 : List Nat := [2, 1, 1, 3, 4, 2, 1, 3, 2, 4]
def baseStart_7335264 : Nat := 118140960795 + 7335264 * 2 ^ 59
def prefixEnd_7335264 : Nat := 4983230072969 + 3 ^ 40 * 7335264 * 2
def baseEnd_7335264 : Nat := 1255505386540564659855247

theorem tailTrace_7335264 : CollatzResearch.WordTrace tailWord_7335264 prefixEnd_7335264 1255505386540564659855247 := by
  unfold tailWord_7335264
  simp only [CollatzResearch.WordTrace]
  refine ⟨133769528648799383099362423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178359371531732510799149897 133769528648799383099362423)
  ·
    refine ⟨200654292973199074649043635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133769528648799383099362423 200654292973199074649043635)
    ·
      refine ⟨300981439459798611973565453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200654292973199074649043635 300981439459798611973565453)
      ·
        refine ⟨112868039797424479490087045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300981439459798611973565453 112868039797424479490087045)
        ·
          refine ⟨21162757462017089904391321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112868039797424479490087045 21162757462017089904391321)
          ·
            refine ⟨15872068096512817428293491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21162757462017089904391321 15872068096512817428293491)
            ·
              refine ⟨23808102144769226142440237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15872068096512817428293491 23808102144769226142440237)
              ·
                refine ⟨8928038304288459803415089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23808102144769226142440237 8928038304288459803415089)
                ·
                  refine ⟨6696028728216344852561317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8928038304288459803415089 6696028728216344852561317)
                  ·
                    refine ⟨1255505386540564659855247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6696028728216344852561317 1255505386540564659855247)
                    ·
                      rfl

theorem cell23_7335264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 3, 2, 4].length) (baseStart_7335264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335264 prefixEnd_7335264 := by exact prefixLift 7335264
  have htrace : WordTrace (prefixWord ++ tailWord_7335264) baseStart_7335264 baseEnd_7335264 := by
    simpa [prefixWord, tailWord_7335264, baseEnd_7335264] using wordTrace_append hprefix tailTrace_7335264
  have hstable : (prefixWord ++ tailWord_7335264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335264).length < 2 ^ (prefixWord ++ tailWord_7335264).sum := by decide
  have hdescent : baseEnd_7335264 < baseStart_7335264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335271 : List Nat := [1, 1, 5, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_7335271 : Nat := 118140960795 + 7335271 * 2 ^ 59
def prefixEnd_7335271 : Nat := 4983230072969 + 3 ^ 40 * 7335271 * 2
def baseEnd_7335271 : Nat := 3766519753986275452178209

theorem tailTrace_7335271 : CollatzResearch.WordTrace tailWord_7335271 prefixEnd_7335271 3766519753986275452178209 := by
  unfold tailWord_7335271
  simp only [CollatzResearch.WordTrace]
  refine ⟨267539312608573406394229667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178359541739048937596153111 267539312608573406394229667)
  ·
    refine ⟨401308968912860109591344501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267539312608573406394229667 401308968912860109591344501)
    ·
      refine ⟨37622715835580635274188547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 401308968912860109591344501 37622715835580635274188547)
      ·
        refine ⟨56434073753370952911282821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37622715835580635274188547 56434073753370952911282821)
        ·
          refine ⟨10581388828757053670865529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56434073753370952911282821 10581388828757053670865529)
          ·
            refine ⟨7936041621567790253149147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10581388828757053670865529 7936041621567790253149147)
            ·
              refine ⟨11904062432351685379723721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7936041621567790253149147 11904062432351685379723721)
              ·
                refine ⟨8928046824263764034792791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11904062432351685379723721 8928046824263764034792791)
                ·
                  refine ⟨13392070236395646052189187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8928046824263764034792791 13392070236395646052189187)
                  ·
                    refine ⟨20088105354593469078283781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13392070236395646052189187 20088105354593469078283781)
                    ·
                      refine ⟨3766519753986275452178209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20088105354593469078283781 3766519753986275452178209)
                      ·
                        rfl

theorem cell23_7335271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_7335271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335271 prefixEnd_7335271 := by exact prefixLift 7335271
  have htrace : WordTrace (prefixWord ++ tailWord_7335271) baseStart_7335271 baseEnd_7335271 := by
    simpa [prefixWord, tailWord_7335271, baseEnd_7335271] using wordTrace_append hprefix tailTrace_7335271
  have hstable : (prefixWord ++ tailWord_7335271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335271).length < 2 ^ (prefixWord ++ tailWord_7335271).sum := by decide
  have hdescent : baseEnd_7335271 < baseStart_7335271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335287 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 3]
def baseStart_7335287 : Nat := 118140960795 + 7335287 * 2 ^ 59
def prefixEnd_7335287 : Nat := 4983230072969 + 3 ^ 40 * 7335287 * 2
def baseEnd_7335287 : Nat := 3766527969676747389578135

theorem tailTrace_7335287 : CollatzResearch.WordTrace tailWord_7335287 prefixEnd_7335287 3766527969676747389578135 := by
  unfold tailWord_7335287
  simp only [CollatzResearch.WordTrace]
  refine ⟨267539896176515441126812115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178359930784343627417874743 267539896176515441126812115)
  ·
    refine ⟨401309844264773161690218173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267539896176515441126812115 401309844264773161690218173)
    ·
      refine ⟨150491191599289935633831815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401309844264773161690218173 150491191599289935633831815)
      ·
        refine ⟨225736787398934903450747723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150491191599289935633831815 225736787398934903450747723)
        ·
          refine ⟨338605181098402355176121585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225736787398934903450747723 338605181098402355176121585)
          ·
            refine ⟨253953885823801766382091189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338605181098402355176121585 253953885823801766382091189)
            ·
              refine ⟨23808176795981415598321049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253953885823801766382091189 23808176795981415598321049)
              ·
                refine ⟨17856132596986061698740787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23808176795981415598321049 17856132596986061698740787)
                ·
                  refine ⟨26784198895479092548111181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17856132596986061698740787 26784198895479092548111181)
                  ·
                    refine ⟨10044074585804659705541693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26784198895479092548111181 10044074585804659705541693)
                    ·
                      refine ⟨3766527969676747389578135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10044074585804659705541693 3766527969676747389578135)
                      ·
                        rfl

theorem cell23_7335287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 3, 3].length) (baseStart_7335287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335287 prefixEnd_7335287 := by exact prefixLift 7335287
  have htrace : WordTrace (prefixWord ++ tailWord_7335287) baseStart_7335287 baseEnd_7335287 := by
    simpa [prefixWord, tailWord_7335287, baseEnd_7335287] using wordTrace_append hprefix tailTrace_7335287
  have hstable : (prefixWord ++ tailWord_7335287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335287).length < 2 ^ (prefixWord ++ tailWord_7335287).sum := by decide
  have hdescent : baseEnd_7335287 < baseStart_7335287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335294 : List Nat := [4, 2, 3, 2, 1, 11]
def baseStart_7335294 : Nat := 118140960795 + 7335294 * 2 ^ 59
def prefixEnd_7335294 : Nat := 4983230072969 + 3 ^ 40 * 7335294 * 2
def baseEnd_7335294 : Nat := 15500129893174192848521

theorem tailTrace_7335294 : CollatzResearch.WordTrace tailWord_7335294 prefixEnd_7335294 15500129893174192848521 := by
  unfold tailWord_7335294
  simp only [CollatzResearch.WordTrace]
  refine ⟨33442518935936260165289617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178360100991660054214877957 33442518935936260165289617)
  ·
    refine ⟨25081889201952195123967213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33442518935936260165289617 25081889201952195123967213)
    ·
      refine ⟨9405708450732073171487705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25081889201952195123967213 9405708450732073171487705)
      ·
        refine ⟨7054281338049054878615779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9405708450732073171487705 7054281338049054878615779)
        ·
          refine ⟨10581422007073582317923669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7054281338049054878615779 10581422007073582317923669)
          ·
            refine ⟨15500129893174192848521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10581422007073582317923669 15500129893174192848521)
            ·
              rfl

theorem cell23_7335294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 11].length) (baseStart_7335294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335294 prefixEnd_7335294 := by exact prefixLift 7335294
  have htrace : WordTrace (prefixWord ++ tailWord_7335294) baseStart_7335294 baseEnd_7335294 := by
    simpa [prefixWord, tailWord_7335294, baseEnd_7335294] using wordTrace_append hprefix tailTrace_7335294
  have hstable : (prefixWord ++ tailWord_7335294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335294).length < 2 ^ (prefixWord ++ tailWord_7335294).sum := by decide
  have hdescent : baseEnd_7335294 < baseStart_7335294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335298 : List Nat := [3, 4, 2, 1, 1, 2, 2, 2, 2, 4]
def baseStart_7335298 : Nat := 118140960795 + 7335298 * 2 ^ 59
def prefixEnd_7335298 : Nat := 4983230072969 + 3 ^ 40 * 7335298 * 2
def baseEnd_7335298 : Nat := 1255511205987982282180195

theorem tailTrace_7335298 : CollatzResearch.WordTrace tailWord_7335298 prefixEnd_7335298 1255511205987982282180195 := by
  unfold tailWord_7335298
  simp only [CollatzResearch.WordTrace]
  refine ⟨66885074344868897501365637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178360198252983726670308365 66885074344868897501365637)
  ·
    refine ⟨12540951439662918281506057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 66885074344868897501365637 12540951439662918281506057)
    ·
      refine ⟨9405713579747188711129543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12540951439662918281506057 9405713579747188711129543)
      ·
        refine ⟨14108570369620783066694315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9405713579747188711129543 14108570369620783066694315)
        ·
          refine ⟨21162855554431174600041473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14108570369620783066694315 21162855554431174600041473)
          ·
            refine ⟨15872141665823380950031105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21162855554431174600041473 15872141665823380950031105)
            ·
              refine ⟨11904106249367535712523329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15872141665823380950031105 11904106249367535712523329)
              ·
                refine ⟨8928079687025651784392497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11904106249367535712523329 8928079687025651784392497)
                ·
                  refine ⟨6696059765269238838294373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8928079687025651784392497 6696059765269238838294373)
                  ·
                    refine ⟨1255511205987982282180195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6696059765269238838294373 1255511205987982282180195)
                    ·
                      rfl

theorem cell23_7335298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_7335298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335298 prefixEnd_7335298 := by exact prefixLift 7335298
  have htrace : WordTrace (prefixWord ++ tailWord_7335298) baseStart_7335298 baseEnd_7335298 := by
    simpa [prefixWord, tailWord_7335298, baseEnd_7335298] using wordTrace_append hprefix tailTrace_7335298
  have hstable : (prefixWord ++ tailWord_7335298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335298).length < 2 ^ (prefixWord ++ tailWord_7335298).sum := by decide
  have hdescent : baseEnd_7335298 < baseStart_7335298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335357 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_7335357 : Nat := 118140960795 + 7335357 * 2 ^ 59
def prefixEnd_7335357 : Nat := 4983230072969 + 3 ^ 40 * 7335357 * 2
def baseEnd_7335357 : Nat := 3766563913322562115702813

theorem tailTrace_7335357 : CollatzResearch.WordTrace tailWord_7335357 prefixEnd_7335357 3766563913322562115702813 := by
  unfold tailWord_7335357
  simp only [CollatzResearch.WordTrace]
  refine ⟨267542449286261843081860325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178361632857507895387906883 267542449286261843081860325)
  ·
    refine ⟨50164209241174095577848811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267542449286261843081860325 50164209241174095577848811)
    ·
      refine ⟨75246313861761143366773217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50164209241174095577848811 75246313861761143366773217)
      ·
        refine ⟨56434735396320857525079913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75246313861761143366773217 56434735396320857525079913)
        ·
          refine ⟨42326051547240643143809935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56434735396320857525079913 42326051547240643143809935)
          ·
            refine ⟨63489077320860964715714903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42326051547240643143809935 63489077320860964715714903)
            ·
              refine ⟨95233615981291447073572355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63489077320860964715714903 95233615981291447073572355)
              ·
                refine ⟨142850423971937170610358533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95233615981291447073572355 142850423971937170610358533)
                ·
                  refine ⟨26784454494738219489442225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142850423971937170610358533 26784454494738219489442225)
                  ·
                    refine ⟨20088340871053664617081669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26784454494738219489442225 20088340871053664617081669)
                    ·
                      refine ⟨3766563913322562115702813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20088340871053664617081669 3766563913322562115702813)
                      ·
                        rfl

theorem cell23_7335357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_7335357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335357 prefixEnd_7335357 := by exact prefixLift 7335357
  have htrace : WordTrace (prefixWord ++ tailWord_7335357) baseStart_7335357 baseEnd_7335357 := by
    simpa [prefixWord, tailWord_7335357, baseEnd_7335357] using wordTrace_append hprefix tailTrace_7335357
  have hstable : (prefixWord ++ tailWord_7335357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335357).length < 2 ^ (prefixWord ++ tailWord_7335357).sum := by decide
  have hdescent : baseEnd_7335357 < baseStart_7335357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335367 : List Nat := [1, 1, 4, 1, 1, 3, 4, 1, 7]
def baseStart_7335367 : Nat := 118140960795 + 7335367 * 2 ^ 59
def prefixEnd_7335367 : Nat := 4983230072969 + 3 ^ 40 * 7335367 * 2
def baseEnd_7335367 : Nat := 418507672014345230730863

theorem tailTrace_7335367 : CollatzResearch.WordTrace tailWord_7335367 prefixEnd_7335367 418507672014345230730863 := by
  unfold tailWord_7335367
  simp only [CollatzResearch.WordTrace]
  refine ⟨267542814016225614789724355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178361876010817076526482903 267542814016225614789724355)
  ·
    refine ⟨401314221024338422184586533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267542814016225614789724355 401314221024338422184586533)
    ·
      refine ⟨75246416442063454159609975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401314221024338422184586533 75246416442063454159609975)
      ·
        refine ⟨112869624663095181239414963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75246416442063454159609975 112869624663095181239414963)
        ·
          refine ⟨169304436994642771859122445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112869624663095181239414963 169304436994642771859122445)
          ·
            refine ⟨63489163872991039447170917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169304436994642771859122445 63489163872991039447170917)
            ·
              refine ⟨11904218226185819896344547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63489163872991039447170917 11904218226185819896344547)
              ·
                refine ⟨17856327339278729844516821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11904218226185819896344547 17856327339278729844516821)
                ·
                  refine ⟨418507672014345230730863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17856327339278729844516821 418507672014345230730863)
                  ·
                    rfl

theorem cell23_7335367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 4, 1, 7].length) (baseStart_7335367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335367 prefixEnd_7335367 := by exact prefixLift 7335367
  have htrace : WordTrace (prefixWord ++ tailWord_7335367) baseStart_7335367 baseEnd_7335367 := by
    simpa [prefixWord, tailWord_7335367, baseEnd_7335367] using wordTrace_append hprefix tailTrace_7335367
  have hstable : (prefixWord ++ tailWord_7335367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335367).length < 2 ^ (prefixWord ++ tailWord_7335367).sum := by decide
  have hdescent : baseEnd_7335367 < baseStart_7335367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335414 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 4, 5]
def baseStart_7335414 : Nat := 118140960795 + 7335414 * 2 ^ 59
def prefixEnd_7335414 : Nat := 4983230072969 + 3 ^ 40 * 7335414 * 2
def baseEnd_7335414 : Nat := 1255531060573289464230017

theorem tailTrace_7335414 : CollatzResearch.WordTrace tailWord_7335414 prefixEnd_7335414 1255531060573289464230017 := by
  unfold tailWord_7335414
  simp only [CollatzResearch.WordTrace]
  refine ⟨16721533015440958863542831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178363018831370227877790197 16721533015440958863542831)
  ·
    refine ⟨25082299523161438295314247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16721533015440958863542831 25082299523161438295314247)
    ·
      refine ⟨37623449284742157442971371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25082299523161438295314247 37623449284742157442971371)
      ·
        refine ⟨56435173927113236164457057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37623449284742157442971371 56435173927113236164457057)
        ·
          refine ⟨42326380445334927123342793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56435173927113236164457057 42326380445334927123342793)
          ·
            refine ⟨31744785334001195342507095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42326380445334927123342793 31744785334001195342507095)
            ·
              refine ⟨47617178001001793013760643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31744785334001195342507095 47617178001001793013760643)
              ·
                refine ⟨71425767001502689520640965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47617178001001793013760643 71425767001502689520640965)
                ·
                  refine ⟨13392331312781754285120181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71425767001502689520640965 13392331312781754285120181)
                  ·
                    refine ⟨1255531060573289464230017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13392331312781754285120181 1255531060573289464230017)
                    ·
                      rfl

theorem cell23_7335414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_7335414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335414 prefixEnd_7335414 := by exact prefixLift 7335414
  have htrace : WordTrace (prefixWord ++ tailWord_7335414) baseStart_7335414 baseEnd_7335414 := by
    simpa [prefixWord, tailWord_7335414, baseEnd_7335414] using wordTrace_append hprefix tailTrace_7335414
  have hstable : (prefixWord ++ tailWord_7335414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335414).length < 2 ^ (prefixWord ++ tailWord_7335414).sum := by decide
  have hdescent : baseEnd_7335414 < baseStart_7335414 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335461 : List Nat := [1, 3, 1, 2, 2, 1, 1, 7, 1, 4]
def baseStart_7335461 : Nat := 118140960795 + 7335461 * 2 ^ 59
def prefixEnd_7335461 : Nat := 4983230072969 + 3 ^ 40 * 7335461 * 2
def baseEnd_7335461 : Nat := 1255539105103543236267445

theorem tailTrace_7335461 : CollatzResearch.WordTrace tailWord_7335461 prefixEnd_7335461 1255539105103543236267445 := by
  unfold tailWord_7335461
  simp only [CollatzResearch.WordTrace]
  refine ⟨267546242477885068843646237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178364161651923379229097491 267546242477885068843646237)
  ·
    refine ⟨100329840929206900816367339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267546242477885068843646237 100329840929206900816367339)
    ·
      refine ⟨150494761393810351224551009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100329840929206900816367339 150494761393810351224551009)
      ·
        refine ⟨112871071045357763418413257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150494761393810351224551009 112871071045357763418413257)
        ·
          refine ⟨84653303284018322563809943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112871071045357763418413257 84653303284018322563809943)
          ·
            refine ⟨126979954926027483845714915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84653303284018322563809943 126979954926027483845714915)
            ·
              refine ⟨190469932389041225768572373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126979954926027483845714915 190469932389041225768572373)
              ·
                refine ⟨4464139040368153728950915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 190469932389041225768572373 4464139040368153728950915)
                ·
                  refine ⟨6696208560552230593426373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4464139040368153728950915 6696208560552230593426373)
                  ·
                    refine ⟨1255539105103543236267445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6696208560552230593426373 1255539105103543236267445)
                    ·
                      rfl

theorem cell23_7335461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 7, 1, 4].length) (baseStart_7335461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335461 prefixEnd_7335461 := by exact prefixLift 7335461
  have htrace : WordTrace (prefixWord ++ tailWord_7335461) baseStart_7335461 baseEnd_7335461 := by
    simpa [prefixWord, tailWord_7335461, baseEnd_7335461] using wordTrace_append hprefix tailTrace_7335461
  have hstable : (prefixWord ++ tailWord_7335461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335461).length < 2 ^ (prefixWord ++ tailWord_7335461).sum := by decide
  have hdescent : baseEnd_7335461 < baseStart_7335461 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335504 : List Nat := [2, 1, 1, 1, 1, 3, 4, 4, 1, 5]
def baseStart_7335504 : Nat := 118140960795 + 7335504 * 2 ^ 59
def prefixEnd_7335504 : Nat := 4983230072969 + 3 ^ 40 * 7335504 * 2
def baseEnd_7335504 : Nat := 1255546464992924346854879

theorem tailTrace_7335504 : CollatzResearch.WordTrace tailWord_7335504 prefixEnd_7335504 1255546464992924346854879 := by
  unfold tailWord_7335504
  simp only [CollatzResearch.WordTrace]
  refine ⟨133773905408364643593730783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178365207211152858124974377 133773905408364643593730783)
  ·
    refine ⟨200660858112546965390596175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133773905408364643593730783 200660858112546965390596175)
    ·
      refine ⟨300991287168820448085894263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200660858112546965390596175 300991287168820448085894263)
      ·
        refine ⟨451486930753230672128841395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300991287168820448085894263 451486930753230672128841395)
        ·
          refine ⟨677230396129846008193262093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451486930753230672128841395 677230396129846008193262093)
          ·
            refine ⟨253961398548692253072473285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 677230396129846008193262093 253961398548692253072473285)
            ·
              refine ⟨47617762227879797451088741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253961398548692253072473285 47617762227879797451088741)
              ·
                refine ⟨8928330417727462022079139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47617762227879797451088741 8928330417727462022079139)
                ·
                  refine ⟨13392495626591193033118709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8928330417727462022079139 13392495626591193033118709)
                  ·
                    refine ⟨1255546464992924346854879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13392495626591193033118709 1255546464992924346854879)
                    ·
                      rfl

theorem cell23_7335504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 1, 5].length) (baseStart_7335504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335504 prefixEnd_7335504 := by exact prefixLift 7335504
  have htrace : WordTrace (prefixWord ++ tailWord_7335504) baseStart_7335504 baseEnd_7335504 := by
    simpa [prefixWord, tailWord_7335504, baseEnd_7335504] using wordTrace_append hprefix tailTrace_7335504
  have hstable : (prefixWord ++ tailWord_7335504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335504).length < 2 ^ (prefixWord ++ tailWord_7335504).sum := by decide
  have hdescent : baseEnd_7335504 < baseStart_7335504 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335507 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 4]
def baseStart_7335507 : Nat := 118140960795 + 7335507 * 2 ^ 59
def prefixEnd_7335507 : Nat := 4983230072969 + 3 ^ 40 * 7335507 * 2
def baseEnd_7335507 : Nat := 3766640935420736528827123

theorem tailTrace_7335507 : CollatzResearch.WordTrace tailWord_7335507 prefixEnd_7335507 3766640935420736528827123 := by
  unfold tailWord_7335507
  simp only [CollatzResearch.WordTrace]
  refine ⟨267547920235718418699820775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178365280157145612466547183 267547920235718418699820775)
  ·
    refine ⟨401321880353577628049731163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267547920235718418699820775 401321880353577628049731163)
    ·
      refine ⟨601982820530366442074596745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401321880353577628049731163 601982820530366442074596745)
      ·
        refine ⟨451487115397774831555947559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601982820530366442074596745 451487115397774831555947559)
        ·
          refine ⟨677230673096662247333921339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451487115397774831555947559 677230673096662247333921339)
          ·
            refine ⟨1015846009644993371000882009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677230673096662247333921339 1015846009644993371000882009)
            ·
              refine ⟨761884507233745028250661507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015846009644993371000882009 761884507233745028250661507)
              ·
                refine ⟨1142826760850617542375992261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761884507233745028250661507 1142826760850617542375992261)
                ·
                  refine ⟨214280017659490789195498549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1142826760850617542375992261 214280017659490789195498549)
                  ·
                    refine ⟨20088751655577261487077989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 214280017659490789195498549 20088751655577261487077989)
                    ·
                      refine ⟨3766640935420736528827123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20088751655577261487077989 3766640935420736528827123)
                      ·
                        rfl

theorem cell23_7335507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_7335507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335507 prefixEnd_7335507 := by exact prefixLift 7335507
  have htrace : WordTrace (prefixWord ++ tailWord_7335507) baseStart_7335507 baseEnd_7335507 := by
    simpa [prefixWord, tailWord_7335507, baseEnd_7335507] using wordTrace_append hprefix tailTrace_7335507
  have hstable : (prefixWord ++ tailWord_7335507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335507).length < 2 ^ (prefixWord ++ tailWord_7335507).sum := by decide
  have hdescent : baseEnd_7335507 < baseStart_7335507 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335511 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 1, 5, 2]
def baseStart_7335511 : Nat := 118140960795 + 7335511 * 2 ^ 59
def prefixEnd_7335511 : Nat := 4983230072969 + 3 ^ 40 * 7335511 * 2
def baseEnd_7335511 : Nat := 3766642989343354513177105

theorem tailTrace_7335511 : CollatzResearch.WordTrace tailWord_7335511 prefixEnd_7335511 3766642989343354513177105 := by
  unfold tailWord_7335511
  simp only [CollatzResearch.WordTrace]
  refine ⟨267548066127703927382966387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178365377418469284921977591 267548066127703927382966387)
  ·
    refine ⟨401322099191555891074449581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267548066127703927382966387 401322099191555891074449581)
    ·
      refine ⟨150495787196833459152918593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401322099191555891074449581 150495787196833459152918593)
      ·
        refine ⟨112871840397625094364688945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150495787196833459152918593 112871840397625094364688945)
        ·
          refine ⟨84653880298218820773516709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112871840397625094364688945 84653880298218820773516709)
          ·
            refine ⟨15872602555916028895034383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84653880298218820773516709 15872602555916028895034383)
            ·
              refine ⟨23808903833874043342551575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15872602555916028895034383 23808903833874043342551575)
              ·
                refine ⟨35713355750811065013827363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23808903833874043342551575 35713355750811065013827363)
                ·
                  refine ⟨53570033626216597520741045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35713355750811065013827363 53570033626216597520741045)
                  ·
                    refine ⟨5022190652457806017569473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53570033626216597520741045 5022190652457806017569473)
                    ·
                      refine ⟨3766642989343354513177105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5022190652457806017569473 3766642989343354513177105)
                      ·
                        rfl

theorem cell23_7335511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 5, 2].length) (baseStart_7335511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335511 prefixEnd_7335511 := by exact prefixLift 7335511
  have htrace : WordTrace (prefixWord ++ tailWord_7335511) baseStart_7335511 baseEnd_7335511 := by
    simpa [prefixWord, tailWord_7335511, baseEnd_7335511] using wordTrace_append hprefix tailTrace_7335511
  have hstable : (prefixWord ++ tailWord_7335511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335511).length < 2 ^ (prefixWord ++ tailWord_7335511).sum := by decide
  have hdescent : baseEnd_7335511 < baseStart_7335511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335547 : List Nat := [1, 1, 1, 1, 1, 4, 4, 10]
def baseStart_7335547 : Nat := 118140960795 + 7335547 * 2 ^ 59
def prefixEnd_7335547 : Nat := 4983230072969 + 3 ^ 40 * 7335547 * 2
def baseEnd_7335547 : Nat := 139505980542478384160257

theorem tailTrace_7335547 : CollatzResearch.WordTrace tailWord_7335547 prefixEnd_7335547 139505980542478384160257 := by
  unfold tailWord_7335547
  simp only [CollatzResearch.WordTrace]
  refine ⟨267549379155573505531276895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178366252770382337020851263 267549379155573505531276895)
  ·
    refine ⟨401324068733360258296915343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267549379155573505531276895 401324068733360258296915343)
    ·
      refine ⟨601986103100040387445373015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401324068733360258296915343 601986103100040387445373015)
      ·
        refine ⟨902979154650060581168059523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601986103100040387445373015 902979154650060581168059523)
        ·
          refine ⟨1354468731975090871752089285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902979154650060581168059523 1354468731975090871752089285)
          ·
            refine ⟨253962887245329538453516741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1354468731975090871752089285 253962887245329538453516741)
            ·
              refine ⟨47618041358499288460034389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253962887245329538453516741 47618041358499288460034389)
              ·
                refine ⟨139505980542478384160257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47618041358499288460034389 139505980542478384160257)
                ·
                  rfl

theorem cell23_7335547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 10].length) (baseStart_7335547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335547 prefixEnd_7335547 := by exact prefixLift 7335547
  have htrace : WordTrace (prefixWord ++ tailWord_7335547) baseStart_7335547 baseEnd_7335547 := by
    simpa [prefixWord, tailWord_7335547, baseEnd_7335547] using wordTrace_append hprefix tailTrace_7335547
  have hstable : (prefixWord ++ tailWord_7335547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335547).length < 2 ^ (prefixWord ++ tailWord_7335547).sum := by decide
  have hdescent : baseEnd_7335547 < baseStart_7335547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335561 : List Nat := [1, 2, 1, 1, 4, 1, 3, 4, 1, 2, 3]
def baseStart_7335561 : Nat := 118140960795 + 7335561 * 2 ^ 59
def prefixEnd_7335561 : Nat := 4983230072969 + 3 ^ 40 * 7335561 * 2
def baseEnd_7335561 : Nat := 3766668663376079317551875

theorem tailTrace_7335561 : CollatzResearch.WordTrace tailWord_7335561 prefixEnd_7335561 3766668663376079317551875 := by
  unfold tailWord_7335561
  simp only [CollatzResearch.WordTrace]
  refine ⟨267549889777522785922286537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178366593185015190614857691 267549889777522785922286537)
  ·
    refine ⟨200662417333142089441714903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267549889777522785922286537 200662417333142089441714903)
    ·
      refine ⟨300993625999713134162572355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200662417333142089441714903 300993625999713134162572355)
      ·
        refine ⟨451490438999569701243858533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300993625999713134162572355 451490438999569701243858533)
        ·
          refine ⟨84654457312419318983223475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 451490438999569701243858533 84654457312419318983223475)
          ·
            refine ⟨126981685968628978474835213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84654457312419318983223475 126981685968628978474835213)
            ·
              refine ⟨47618132238235866928063205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126981685968628978474835213 47618132238235866928063205)
              ·
                refine ⟨8928399794669225049011851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47618132238235866928063205 8928399794669225049011851)
                ·
                  refine ⟨13392599692003837573517777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8928399794669225049011851 13392599692003837573517777)
                  ·
                    refine ⟨10044449769002878180138333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13392599692003837573517777 10044449769002878180138333)
                    ·
                      refine ⟨3766668663376079317551875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10044449769002878180138333 3766668663376079317551875)
                      ·
                        rfl

theorem cell23_7335561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 2, 3].length) (baseStart_7335561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335561 prefixEnd_7335561 := by exact prefixLift 7335561
  have htrace : WordTrace (prefixWord ++ tailWord_7335561) baseStart_7335561 baseEnd_7335561 := by
    simpa [prefixWord, tailWord_7335561, baseEnd_7335561] using wordTrace_append hprefix tailTrace_7335561
  have hstable : (prefixWord ++ tailWord_7335561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335561).length < 2 ^ (prefixWord ++ tailWord_7335561).sum := by decide
  have hdescent : baseEnd_7335561 < baseStart_7335561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335598 : List Nat := [4, 1, 4, 1, 2, 1, 2, 8]
def baseStart_7335598 : Nat := 118140960795 + 7335598 * 2 ^ 59
def prefixEnd_7335598 : Nat := 4983230072969 + 3 ^ 40 * 7335598 * 2
def baseEnd_7335598 : Nat := 139506950450381321214415

theorem tailTrace_7335598 : CollatzResearch.WordTrace tailWord_7335598 prefixEnd_7335598 139506950450381321214415 := by
  unfold tailWord_7335598
  simp only [CollatzResearch.WordTrace]
  refine ⟨33443904909798592655172931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178367492852259160827588965 33443904909798592655172931)
  ·
    refine ⟨50165857364697888982759397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33443904909798592655172931 50165857364697888982759397)
    ·
      refine ⟨9406098255880854184267387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50165857364697888982759397 9406098255880854184267387)
      ·
        refine ⟨14109147383821281276401081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9406098255880854184267387 14109147383821281276401081)
        ·
          refine ⟨10581860537865960957300811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14109147383821281276401081 10581860537865960957300811)
          ·
            refine ⟨15872790806798941435951217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10581860537865960957300811 15872790806798941435951217)
            ·
              refine ⟨11904593105099206076963413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15872790806798941435951217 11904593105099206076963413)
              ·
                refine ⟨139506950450381321214415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11904593105099206076963413 139506950450381321214415)
                ·
                  rfl

theorem cell23_7335598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 2, 8].length) (baseStart_7335598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335598 prefixEnd_7335598 := by exact prefixLift 7335598
  have htrace : WordTrace (prefixWord ++ tailWord_7335598) baseStart_7335598 baseEnd_7335598 := by
    simpa [prefixWord, tailWord_7335598, baseEnd_7335598] using wordTrace_append hprefix tailTrace_7335598
  have hstable : (prefixWord ++ tailWord_7335598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335598).length < 2 ^ (prefixWord ++ tailWord_7335598).sum := by decide
  have hdescent : baseEnd_7335598 < baseStart_7335598 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335648 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 4, 2, 2]
def baseStart_7335648 : Nat := 118140960795 + 7335648 * 2 ^ 59
def prefixEnd_7335648 : Nat := 4983230072969 + 3 ^ 40 * 7335648 * 2
def baseEnd_7335648 : Nat := 3766713336193020477163975

theorem tailTrace_7335648 : CollatzResearch.WordTrace tailWord_7335648 prefixEnd_7335648 3766713336193020477163975 := by
  unfold tailWord_7335648
  simp only [CollatzResearch.WordTrace]
  refine ⟨133776531464103799890351799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178368708618805066520469065 133776531464103799890351799)
  ·
    refine ⟨200664797196155699835527699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133776531464103799890351799 200664797196155699835527699)
    ·
      refine ⟨300997195794233549753291549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200664797196155699835527699 300997195794233549753291549)
      ·
        refine ⟨112873948422837581157484331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300997195794233549753291549 112873948422837581157484331)
        ·
          refine ⟨169310922634256371736226497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112873948422837581157484331 169310922634256371736226497)
          ·
            refine ⟨126983191975692278802169873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169310922634256371736226497 126983191975692278802169873)
            ·
              refine ⟨95237393981769209101627405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126983191975692278802169873 95237393981769209101627405)
              ·
                refine ⟨35714022743163453413110277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95237393981769209101627405 35714022743163453413110277)
                ·
                  refine ⟨6696379264343147514958177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35714022743163453413110277 6696379264343147514958177)
                  ·
                    refine ⟨5022284448257360636218633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6696379264343147514958177 5022284448257360636218633)
                    ·
                      refine ⟨3766713336193020477163975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5022284448257360636218633 3766713336193020477163975)
                      ·
                        rfl

theorem cell23_7335648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 4, 2, 2].length) (baseStart_7335648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335648 prefixEnd_7335648 := by exact prefixLift 7335648
  have htrace : WordTrace (prefixWord ++ tailWord_7335648) baseStart_7335648 baseEnd_7335648 := by
    simpa [prefixWord, tailWord_7335648, baseEnd_7335648] using wordTrace_append hprefix tailTrace_7335648
  have hstable : (prefixWord ++ tailWord_7335648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335648).length < 2 ^ (prefixWord ++ tailWord_7335648).sum := by decide
  have hdescent : baseEnd_7335648 < baseStart_7335648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335661 : List Nat := [1, 5, 1, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_7335661 : Nat := 118140960795 + 7335661 * 2 ^ 59
def prefixEnd_7335661 : Nat := 4983230072969 + 3 ^ 40 * 7335661 * 2
def baseEnd_7335661 : Nat := 3766720011441528926301415

theorem tailTrace_7335661 : CollatzResearch.WordTrace tailWord_7335661 prefixEnd_7335661 3766720011441528926301415 := by
  unfold tailWord_7335661
  simp only [CollatzResearch.WordTrace]
  refine ⟨267553537077160503000926837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178369024718107002000617891 267553537077160503000926837)
  ·
    refine ⟨25083144100983797156336891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267553537077160503000926837 25083144100983797156336891)
    ·
      refine ⟨37624716151475695734505337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25083144100983797156336891 37624716151475695734505337)
      ·
        refine ⟨28218537113606771800879003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37624716151475695734505337 28218537113606771800879003)
        ·
          refine ⟨42327805670410157701318505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28218537113606771800879003 42327805670410157701318505)
          ·
            refine ⟨31745854252807618275988879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42327805670410157701318505 31745854252807618275988879)
            ·
              refine ⟨47618781379211427413983319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31745854252807618275988879 47618781379211427413983319)
              ·
                refine ⟨71428172068817141120974979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47618781379211427413983319 71428172068817141120974979)
                ·
                  refine ⟨107142258103225711681462469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71428172068817141120974979 107142258103225711681462469)
                  ·
                    refine ⟨20089173394354820940274213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107142258103225711681462469 20089173394354820940274213)
                    ·
                      refine ⟨3766720011441528926301415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20089173394354820940274213 3766720011441528926301415)
                      ·
                        rfl

theorem cell23_7335661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_7335661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335661 prefixEnd_7335661 := by exact prefixLift 7335661
  have htrace : WordTrace (prefixWord ++ tailWord_7335661) baseStart_7335661 baseEnd_7335661 := by
    simpa [prefixWord, tailWord_7335661, baseEnd_7335661] using wordTrace_append hprefix tailTrace_7335661
  have hstable : (prefixWord ++ tailWord_7335661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335661).length < 2 ^ (prefixWord ++ tailWord_7335661).sum := by decide
  have hdescent : baseEnd_7335661 < baseStart_7335661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335665 : List Nat := [1, 2, 2, 2, 2, 3, 2, 3, 2, 2, 2]
def baseStart_7335665 : Nat := 118140960795 + 7335665 * 2 ^ 59
def prefixEnd_7335665 : Nat := 4983230072969 + 3 ^ 40 * 7335665 * 2
def baseEnd_7335665 : Nat := 3766722065364146910651397

theorem tailTrace_7335665 : CollatzResearch.WordTrace tailWord_7335665 prefixEnd_7335665 3766722065364146910651397 := by
  unfold tailWord_7335665
  simp only [CollatzResearch.WordTrace]
  refine ⟨267553682969146011684072449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178369121979430674456048299 267553682969146011684072449)
  ·
    refine ⟨200665262226859508763054337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267553682969146011684072449 200665262226859508763054337)
    ·
      refine ⟨150498946670144631572290753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200665262226859508763054337 150498946670144631572290753)
      ·
        refine ⟨112874210002608473679218065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150498946670144631572290753 112874210002608473679218065)
        ·
          refine ⟨84655657501956355259413549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112874210002608473679218065 84655657501956355259413549)
          ·
            refine ⟨31745871563233633222280081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84655657501956355259413549 31745871563233633222280081)
            ·
              refine ⟨23809403672425224916710061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31745871563233633222280081 23809403672425224916710061)
              ·
                refine ⟨8928526377159459343766273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23809403672425224916710061 8928526377159459343766273)
                ·
                  refine ⟨6696394782869594507824705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8928526377159459343766273 6696394782869594507824705)
                  ·
                    refine ⟨5022296087152195880868529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6696394782869594507824705 5022296087152195880868529)
                    ·
                      refine ⟨3766722065364146910651397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5022296087152195880868529 3766722065364146910651397)
                      ·
                        rfl

theorem cell23_7335665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 2, 2].length) (baseStart_7335665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335665 prefixEnd_7335665 := by exact prefixLift 7335665
  have htrace : WordTrace (prefixWord ++ tailWord_7335665) baseStart_7335665 baseEnd_7335665 := by
    simpa [prefixWord, tailWord_7335665, baseEnd_7335665] using wordTrace_append hprefix tailTrace_7335665
  have hstable : (prefixWord ++ tailWord_7335665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335665).length < 2 ^ (prefixWord ++ tailWord_7335665).sum := by decide
  have hdescent : baseEnd_7335665 < baseStart_7335665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335688 : List Nat := [2, 1, 3, 2, 2, 1, 4, 3, 5]
def baseStart_7335688 : Nat := 118140960795 + 7335688 * 2 ^ 59
def prefixEnd_7335688 : Nat := 4983230072969 + 3 ^ 40 * 7335688 * 2
def baseEnd_7335688 : Nat := 418525986157688924518199

theorem tailTrace_7335688 : CollatzResearch.WordTrace tailWord_7335688 prefixEnd_7335688 418525986157688924518199 := by
  unfold tailWord_7335688
  simp only [CollatzResearch.WordTrace]
  refine ⟨133777260924031343306079859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178369681232041791074773145 133777260924031343306079859)
  ·
    refine ⟨200665891386047014959119789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133777260924031343306079859 200665891386047014959119789)
    ·
      refine ⟨75249709269767630609669921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200665891386047014959119789 75249709269767630609669921)
      ·
        refine ⟨56437281952325722957252441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75249709269767630609669921 56437281952325722957252441)
        ·
          refine ⟨42327961464244292217939331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56437281952325722957252441 42327961464244292217939331)
          ·
            refine ⟨63491942196366438326908997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42327961464244292217939331 63491942196366438326908997)
            ·
              refine ⟨11904739161818707186295437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63491942196366438326908997 11904739161818707186295437)
              ·
                refine ⟨4464277185682015194860789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11904739161818707186295437 4464277185682015194860789)
                ·
                  refine ⟨418525986157688924518199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4464277185682015194860789 418525986157688924518199)
                  ·
                    rfl

theorem cell23_7335688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 4, 3, 5].length) (baseStart_7335688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335688 prefixEnd_7335688 := by exact prefixLift 7335688
  have htrace : WordTrace (prefixWord ++ tailWord_7335688) baseStart_7335688 baseEnd_7335688 := by
    simpa [prefixWord, tailWord_7335688, baseEnd_7335688] using wordTrace_append hprefix tailTrace_7335688
  have hstable : (prefixWord ++ tailWord_7335688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335688).length < 2 ^ (prefixWord ++ tailWord_7335688).sum := by decide
  have hdescent : baseEnd_7335688 < baseStart_7335688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335693 : List Nat := [1, 7, 2, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_7335693 : Nat := 118140960795 + 7335693 * 2 ^ 59
def prefixEnd_7335693 : Nat := 4983230072969 + 3 ^ 40 * 7335693 * 2
def baseEnd_7335693 : Nat := 3766736442822472801101269

theorem tailTrace_7335693 : CollatzResearch.WordTrace tailWord_7335693 prefixEnd_7335693 3766736442822472801101269 := by
  unfold tailWord_7335693
  simp only [CollatzResearch.WordTrace]
  refine ⟨267554704213044572466091733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178369802808696381644061155 267554704213044572466091733)
  ·
    refine ⟨6270813379993232167174025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 267554704213044572466091733 6270813379993232167174025)
    ·
      refine ⟨4703110034994924125380519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6270813379993232167174025 4703110034994924125380519)
      ·
        refine ⟨7054665052492386188070779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4703110034994924125380519 7054665052492386188070779)
        ·
          refine ⟨10581997578738579282106169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7054665052492386188070779 10581997578738579282106169)
          ·
            refine ⟨7936498184053934461579627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10581997578738579282106169 7936498184053934461579627)
            ·
              refine ⟨11904747276080901692369441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7936498184053934461579627 11904747276080901692369441)
              ·
                refine ⟨8928560457060676269277081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11904747276080901692369441 8928560457060676269277081)
                ·
                  refine ⟨6696420342795507201957811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8928560457060676269277081 6696420342795507201957811)
                  ·
                    refine ⟨10044630514193260802936717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6696420342795507201957811 10044630514193260802936717)
                    ·
                      refine ⟨3766736442822472801101269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10044630514193260802936717 3766736442822472801101269)
                      ·
                        rfl

theorem cell23_7335693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_7335693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335693 prefixEnd_7335693 := by exact prefixLift 7335693
  have htrace : WordTrace (prefixWord ++ tailWord_7335693) baseStart_7335693 baseEnd_7335693 := by
    simpa [prefixWord, tailWord_7335693, baseEnd_7335693] using wordTrace_append hprefix tailTrace_7335693
  have hstable : (prefixWord ++ tailWord_7335693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335693).length < 2 ^ (prefixWord ++ tailWord_7335693).sum := by decide
  have hdescent : baseEnd_7335693 < baseStart_7335693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335761 : List Nat := [1, 2, 2, 1, 5, 1, 2, 1, 8]
def baseStart_7335761 : Nat := 118140960795 + 7335761 * 2 ^ 59
def prefixEnd_7335761 : Nat := 4983230072969 + 3 ^ 40 * 7335761 * 2
def baseEnd_7335761 : Nat := 418530151056330948338995

theorem tailTrace_7335761 : CollatzResearch.WordTrace tailWord_7335761 prefixEnd_7335761 418530151056330948338995 := by
  unfold tailWord_7335761
  simp only [CollatzResearch.WordTrace]
  refine ⟨267557184376798220079567137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178371456251198813386378091 267557184376798220079567137)
  ·
    refine ⟨200667888282598665059675353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267557184376798220079567137 200667888282598665059675353)
    ·
      refine ⟨150500916211948998794756515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200667888282598665059675353 150500916211948998794756515)
      ·
        refine ⟨225751374317923498192134773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150500916211948998794756515 225751374317923498192134773)
        ·
          refine ⟨21164191342305327955512635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225751374317923498192134773 21164191342305327955512635)
          ·
            refine ⟨31746287013457991933268953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21164191342305327955512635 31746287013457991933268953)
            ·
              refine ⟨23809715260093493949951715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31746287013457991933268953 23809715260093493949951715)
              ·
                refine ⟨35714572890140240924927573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23809715260093493949951715 35714572890140240924927573)
                ·
                  refine ⟨418530151056330948338995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35714572890140240924927573 418530151056330948338995)
                  ·
                    rfl

theorem cell23_7335761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 8].length) (baseStart_7335761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335761 prefixEnd_7335761 := by exact prefixLift 7335761
  have htrace : WordTrace (prefixWord ++ tailWord_7335761) baseStart_7335761 baseEnd_7335761 := by
    simpa [prefixWord, tailWord_7335761, baseEnd_7335761] using wordTrace_append hprefix tailTrace_7335761
  have hstable : (prefixWord ++ tailWord_7335761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335761).length < 2 ^ (prefixWord ++ tailWord_7335761).sum := by decide
  have hdescent : baseEnd_7335761 < baseStart_7335761 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335765 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 3, 4]
def baseStart_7335765 : Nat := 118140960795 + 7335765 * 2 ^ 59
def prefixEnd_7335765 : Nat := 4983230072969 + 3 ^ 40 * 7335765 * 2
def baseEnd_7335765 : Nat := 1255591137809865506466979

theorem tailTrace_7335765 : CollatzResearch.WordTrace tailWord_7335765 prefixEnd_7335765 1255591137809865506466979 := by
  unfold tailWord_7335765
  simp only [CollatzResearch.WordTrace]
  refine ⟨267557330268783728762712749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178371553512522485841808499 267557330268783728762712749)
  ·
    refine ⟨100333998850793898286017281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267557330268783728762712749 100333998850793898286017281)
    ·
      refine ⟨75250499138095423714512961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100333998850793898286017281 75250499138095423714512961)
      ·
        refine ⟨56437874353571567785884721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75250499138095423714512961 56437874353571567785884721)
        ·
          refine ⟨42328405765178675839413541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56437874353571567785884721 42328405765178675839413541)
          ·
            refine ⟨7936576080971001719890039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42328405765178675839413541 7936576080971001719890039)
            ·
              refine ⟨11904864121456502579835059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7936576080971001719890039 11904864121456502579835059)
              ·
                refine ⟨17857296182184753869752589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11904864121456502579835059 17857296182184753869752589)
                ·
                  refine ⟨6696486068319282701157221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17857296182184753869752589 6696486068319282701157221)
                  ·
                    refine ⟨1255591137809865506466979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6696486068319282701157221 1255591137809865506466979)
                    ·
                      rfl

theorem cell23_7335765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_7335765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335765 prefixEnd_7335765 := by exact prefixLift 7335765
  have htrace : WordTrace (prefixWord ++ tailWord_7335765) baseStart_7335765 baseEnd_7335765 := by
    simpa [prefixWord, tailWord_7335765, baseEnd_7335765] using wordTrace_append hprefix tailTrace_7335765
  have hstable : (prefixWord ++ tailWord_7335765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335765).length < 2 ^ (prefixWord ++ tailWord_7335765).sum := by decide
  have hdescent : baseEnd_7335765 < baseStart_7335765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335816 : List Nat := [2, 1, 3, 3, 4, 1, 2, 2, 1, 4]
def baseStart_7335816 : Nat := 118140960795 + 7335816 * 2 ^ 59
def prefixEnd_7335816 : Nat := 4983230072969 + 3 ^ 40 * 7335816 * 2
def baseEnd_7335816 : Nat := 1255599866980991939954401

theorem tailTrace_7335816 : CollatzResearch.WordTrace tailWord_7335816 prefixEnd_7335816 1255599866980991939954401 := by
  unfold tailWord_7335816
  simp only [CollatzResearch.WordTrace]
  refine ⟨133779595195799482236409651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178372793594399309648546201 133779595195799482236409651)
  ·
    refine ⟨200669392793699223354614477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133779595195799482236409651 200669392793699223354614477)
    ·
      refine ⟨75251022297637208757980429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200669392793699223354614477 75251022297637208757980429)
      ·
        refine ⟨28219133361613953284242661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75251022297637208757980429 28219133361613953284242661)
        ·
          refine ⟨5291087505302616240795499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28219133361613953284242661 5291087505302616240795499)
          ·
            refine ⟨7936631257953924361193249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5291087505302616240795499 7936631257953924361193249)
            ·
              refine ⟨5952473443465443270894937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7936631257953924361193249 5952473443465443270894937)
              ·
                refine ⟨4464355082599082453171203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5952473443465443270894937 4464355082599082453171203)
                ·
                  refine ⟨6696532623898623679756805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4464355082599082453171203 6696532623898623679756805)
                  ·
                    refine ⟨1255599866980991939954401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6696532623898623679756805 1255599866980991939954401)
                    ·
                      rfl

theorem cell23_7335816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 2, 1, 4].length) (baseStart_7335816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335816 prefixEnd_7335816 := by exact prefixLift 7335816
  have htrace : WordTrace (prefixWord ++ tailWord_7335816) baseStart_7335816 baseEnd_7335816 := by
    simpa [prefixWord, tailWord_7335816, baseEnd_7335816] using wordTrace_append hprefix tailTrace_7335816
  have hstable : (prefixWord ++ tailWord_7335816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335816).length < 2 ^ (prefixWord ++ tailWord_7335816).sum := by decide
  have hdescent : baseEnd_7335816 < baseStart_7335816 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335865 : List Nat := [1, 2, 1, 4, 2, 1, 3, 3, 1, 2, 3]
def baseStart_7335865 : Nat := 118140960795 + 7335865 * 2 ^ 59
def prefixEnd_7335865 : Nat := 4983230072969 + 3 ^ 40 * 7335865 * 2
def baseEnd_7335865 : Nat := 3766824761495046128150477

theorem tailTrace_7335865 : CollatzResearch.WordTrace tailWord_7335865 prefixEnd_7335865 3766824761495046128150477 := by
  unfold tailWord_7335865
  simp only [CollatzResearch.WordTrace]
  refine ⟨267560977568421445841353049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178373985045614297227568699 267560977568421445841353049)
  ·
    refine ⟨200670733176316084381014787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267560977568421445841353049 200670733176316084381014787)
    ·
      refine ⟨301006099764474126571522181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200670733176316084381014787 301006099764474126571522181)
      ·
        refine ⟨56438643705838898732160409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301006099764474126571522181 56438643705838898732160409)
        ·
          refine ⟨42328982779379174049120307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56438643705838898732160409 42328982779379174049120307)
          ·
            refine ⟨63493474169068761073680461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42328982779379174049120307 63493474169068761073680461)
            ·
              refine ⟨23810052813400785402630173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63493474169068761073680461 23810052813400785402630173)
              ·
                refine ⟨8928769805025294525986315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23810052813400785402630173 8928769805025294525986315)
                ·
                  refine ⟨13393154707537941788979473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8928769805025294525986315 13393154707537941788979473)
                  ·
                    refine ⟨10044866030653456341734605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13393154707537941788979473 10044866030653456341734605)
                    ·
                      refine ⟨3766824761495046128150477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10044866030653456341734605 3766824761495046128150477)
                      ·
                        rfl

theorem cell23_7335865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_7335865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335865 prefixEnd_7335865 := by exact prefixLift 7335865
  have htrace : WordTrace (prefixWord ++ tailWord_7335865) baseStart_7335865 baseEnd_7335865 := by
    simpa [prefixWord, tailWord_7335865, baseEnd_7335865] using wordTrace_append hprefix tailTrace_7335865
  have hstable : (prefixWord ++ tailWord_7335865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335865).length < 2 ^ (prefixWord ++ tailWord_7335865).sum := by decide
  have hdescent : baseEnd_7335865 < baseStart_7335865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335905 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 3, 3, 2]
def baseStart_7335905 : Nat := 118140960795 + 7335905 * 2 ^ 59
def prefixEnd_7335905 : Nat := 4983230072969 + 3 ^ 40 * 7335905 * 2
def baseEnd_7335905 : Nat := 3766845300721225971650293

theorem tailTrace_7335905 : CollatzResearch.WordTrace tailWord_7335905 prefixEnd_7335905 3766845300721225971650293 := by
  unfold tailWord_7335905
  simp only [CollatzResearch.WordTrace]
  refine ⟨267562436488276532672809169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178374957658851021781872779 267562436488276532672809169)
  ·
    refine ⟨200671827366207399504606877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267562436488276532672809169 200671827366207399504606877)
    ·
      refine ⟨75251935262327774814227579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200671827366207399504606877 75251935262327774814227579)
      ·
        refine ⟨112877902893491662221341369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75251935262327774814227579 112877902893491662221341369)
        ·
          refine ⟨84658427170118746666006027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112877902893491662221341369 84658427170118746666006027)
          ·
            refine ⟨126987640755178119999009041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84658427170118746666006027 126987640755178119999009041)
            ·
              refine ⟨95240730566383589999256781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126987640755178119999009041 95240730566383589999256781)
              ·
                refine ⟨35715273962393846249721293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95240730566383589999256781 35715273962393846249721293)
                ·
                  refine ⟨13393227735897692343645485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35715273962393846249721293 13393227735897692343645485)
                  ·
                    refine ⟨5022460400961634628867057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13393227735897692343645485 5022460400961634628867057)
                    ·
                      refine ⟨3766845300721225971650293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5022460400961634628867057 3766845300721225971650293)
                      ·
                        rfl

theorem cell23_7335905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 3, 3, 2].length) (baseStart_7335905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335905 prefixEnd_7335905 := by exact prefixLift 7335905
  have htrace : WordTrace (prefixWord ++ tailWord_7335905) baseStart_7335905 baseEnd_7335905 := by
    simpa [prefixWord, tailWord_7335905, baseEnd_7335905] using wordTrace_append hprefix tailTrace_7335905
  have hstable : (prefixWord ++ tailWord_7335905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335905).length < 2 ^ (prefixWord ++ tailWord_7335905).sum := by decide
  have hdescent : baseEnd_7335905 < baseStart_7335905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335946 : List Nat := [3, 1, 2, 2, 4, 2, 2, 1, 2, 1, 3]
def baseStart_7335946 : Nat := 118140960795 + 7335946 * 2 ^ 59
def prefixEnd_7335946 : Nat := 4983230072969 + 3 ^ 40 * 7335946 * 2
def baseEnd_7335946 : Nat := 3766866353428060311237605

theorem tailTrace_7335946 : CollatzResearch.WordTrace tailWord_7335946 prefixEnd_7335946 3766866353428060311237605 := by
  unfold tailWord_7335946
  simp only [CollatzResearch.WordTrace]
  refine ⟨66890982970281999168762923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178375954587418664450034461 66890982970281999168762923)
  ·
    refine ⟨100336474455422998753144385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66890982970281999168762923 100336474455422998753144385)
    ·
      refine ⟨75252355841567249064858289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100336474455422998753144385 75252355841567249064858289)
      ·
        refine ⟨56439266881175436798643717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75252355841567249064858289 56439266881175436798643717)
        ·
          refine ⟨10582362540220394399745697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56439266881175436798643717 10582362540220394399745697)
          ·
            refine ⟨7936771905165295799809273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10582362540220394399745697 7936771905165295799809273)
            ·
              refine ⟨5952578928873971849856955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7936771905165295799809273 5952578928873971849856955)
              ·
                refine ⟨8928868393310957774785433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5952578928873971849856955 8928868393310957774785433)
                ·
                  refine ⟨6696651294983218331089075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8928868393310957774785433 6696651294983218331089075)
                  ·
                    refine ⟨10044976942474827496633613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6696651294983218331089075 10044976942474827496633613)
                    ·
                      refine ⟨3766866353428060311237605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10044976942474827496633613 3766866353428060311237605)
                      ·
                        rfl

theorem cell23_7335946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_7335946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335946 prefixEnd_7335946 := by exact prefixLift 7335946
  have htrace : WordTrace (prefixWord ++ tailWord_7335946) baseStart_7335946 baseEnd_7335946 := by
    simpa [prefixWord, tailWord_7335946, baseEnd_7335946] using wordTrace_append hprefix tailTrace_7335946
  have hstable : (prefixWord ++ tailWord_7335946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335946).length < 2 ^ (prefixWord ++ tailWord_7335946).sum := by decide
  have hdescent : baseEnd_7335946 < baseStart_7335946 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335948 : List Nat := [2, 2, 1, 2, 3, 1, 2, 1, 1, 4, 4]
def baseStart_7335948 : Nat := 118140960795 + 7335948 * 2 ^ 59
def prefixEnd_7335948 : Nat := 4983230072969 + 3 ^ 40 * 7335948 * 2
def baseEnd_7335948 : Nat := 3766867380389369303412595

theorem tailTrace_7335948 : CollatzResearch.WordTrace tailWord_7335948 prefixEnd_7335948 3766867380389369303412595 := by
  unfold tailWord_7335948
  simp only [CollatzResearch.WordTrace]
  refine ⟨133782002413560375508312249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178376003218080500677749665 133782002413560375508312249)
  ·
    refine ⟨100336501810170281631234187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133782002413560375508312249 100336501810170281631234187)
    ·
      refine ⟨150504752715255422446851281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100336501810170281631234187 150504752715255422446851281)
      ·
        refine ⟨112878564536441566835138461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150504752715255422446851281 112878564536441566835138461)
        ·
          refine ⟨42329461701165587563176923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112878564536441566835138461 42329461701165587563176923)
          ·
            refine ⟨63494192551748381344765385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42329461701165587563176923 63494192551748381344765385)
            ·
              refine ⟨47620644413811286008574039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63494192551748381344765385 47620644413811286008574039)
              ·
                refine ⟨71430966620716929012861059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47620644413811286008574039 71430966620716929012861059)
                ·
                  refine ⟨107146449931075393519291589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71430966620716929012861059 107146449931075393519291589)
                  ·
                    refine ⟨20089959362076636284867173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107146449931075393519291589 20089959362076636284867173)
                    ·
                      refine ⟨3766867380389369303412595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20089959362076636284867173 3766867380389369303412595)
                      ·
                        rfl

theorem cell23_7335948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_7335948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335948 prefixEnd_7335948 := by exact prefixLift 7335948
  have htrace : WordTrace (prefixWord ++ tailWord_7335948) baseStart_7335948 baseEnd_7335948 := by
    simpa [prefixWord, tailWord_7335948, baseEnd_7335948] using wordTrace_append hprefix tailTrace_7335948
  have hstable : (prefixWord ++ tailWord_7335948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335948).length < 2 ^ (prefixWord ++ tailWord_7335948).sum := by decide
  have hdescent : baseEnd_7335948 < baseStart_7335948 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335952 : List Nat := [2, 1, 1, 1, 1, 1, 1, 9, 2, 2, 2]
def baseStart_7335952 : Nat := 118140960795 + 7335952 * 2 ^ 59
def prefixEnd_7335952 : Nat := 4983230072969 + 3 ^ 40 * 7335952 * 2
def baseEnd_7335952 : Nat := 3766869434311987287762577

theorem tailTrace_7335952 : CollatzResearch.WordTrace tailWord_7335952 prefixEnd_7335952 3766869434311987287762577 := by
  unfold tailWord_7335952
  simp only [CollatzResearch.WordTrace]
  refine ⟨133782075359553129849885055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178376100479404173133180073 133782075359553129849885055)
  ·
    refine ⟨200673113039329694774827583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133782075359553129849885055 200673113039329694774827583)
    ·
      refine ⟨301009669558994542162241375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200673113039329694774827583 301009669558994542162241375)
      ·
        refine ⟨451514504338491813243362063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301009669558994542162241375 451514504338491813243362063)
        ·
          refine ⟨677271756507737719865043095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451514504338491813243362063 677271756507737719865043095)
          ·
            refine ⟨1015907634761606579797564643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677271756507737719865043095 1015907634761606579797564643)
            ·
              refine ⟨1523861452142409869696346965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015907634761606579797564643 1523861452142409869696346965)
              ·
                refine ⟨8928875696146932830252033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1523861452142409869696346965 8928875696146932830252033)
                ·
                  refine ⟨6696656772110199622689025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8928875696146932830252033 6696656772110199622689025)
                  ·
                    refine ⟨5022492579082649717016769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6696656772110199622689025 5022492579082649717016769)
                    ·
                      refine ⟨3766869434311987287762577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5022492579082649717016769 3766869434311987287762577)
                      ·
                        rfl

theorem cell23_7335952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 2, 2, 2].length) (baseStart_7335952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335952 prefixEnd_7335952 := by exact prefixLift 7335952
  have htrace : WordTrace (prefixWord ++ tailWord_7335952) baseStart_7335952 baseEnd_7335952 := by
    simpa [prefixWord, tailWord_7335952, baseEnd_7335952] using wordTrace_append hprefix tailTrace_7335952
  have hstable : (prefixWord ++ tailWord_7335952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335952).length < 2 ^ (prefixWord ++ tailWord_7335952).sum := by decide
  have hdescent : baseEnd_7335952 < baseStart_7335952 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335956 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 3, 3, 2]
def baseStart_7335956 : Nat := 118140960795 + 7335956 * 2 ^ 59
def prefixEnd_7335956 : Nat := 4983230072969 + 3 ^ 40 * 7335956 * 2
def baseEnd_7335956 : Nat := 3766871488234605272112559

theorem tailTrace_7335956 : CollatzResearch.WordTrace tailWord_7335956 prefixEnd_7335956 3766871488234605272112559 := by
  unfold tailWord_7335956
  simp only [CollatzResearch.WordTrace]
  refine ⟨133782148305545884191457861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178376197740727845588610481 133782148305545884191457861)
  ·
    refine ⟨25084152807289853285898349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133782148305545884191457861 25084152807289853285898349)
    ·
      refine ⟨9406557302733694982211881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25084152807289853285898349 9406557302733694982211881)
      ·
        refine ⟨7054917977050271236658911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9406557302733694982211881 7054917977050271236658911)
        ·
          refine ⟨10582376965575406854988367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7054917977050271236658911 10582376965575406854988367)
          ·
            refine ⟨15873565448363110282482551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10582376965575406854988367 15873565448363110282482551)
            ·
              refine ⟨23810348172544665423723827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15873565448363110282482551 23810348172544665423723827)
              ·
                refine ⟨35715522258816998135585741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23810348172544665423723827 35715522258816998135585741)
                ·
                  refine ⟨13393320847056374300844653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35715522258816998135585741 13393320847056374300844653)
                  ·
                    refine ⟨5022495317646140362816745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13393320847056374300844653 5022495317646140362816745)
                    ·
                      refine ⟨3766871488234605272112559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5022495317646140362816745 3766871488234605272112559)
                      ·
                        rfl

theorem cell23_7335956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_7335956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335956 prefixEnd_7335956 := by exact prefixLift 7335956
  have htrace : WordTrace (prefixWord ++ tailWord_7335956) baseStart_7335956 baseEnd_7335956 := by
    simpa [prefixWord, tailWord_7335956, baseEnd_7335956] using wordTrace_append hprefix tailTrace_7335956
  have hstable : (prefixWord ++ tailWord_7335956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335956).length < 2 ^ (prefixWord ++ tailWord_7335956).sum := by decide
  have hdescent : baseEnd_7335956 < baseStart_7335956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7335992 : List Nat := [2, 1, 2, 1, 6, 1, 1, 4, 5]
def baseStart_7335992 : Nat := 118140960795 + 7335992 * 2 ^ 59
def prefixEnd_7335992 : Nat := 4983230072969 + 3 ^ 40 * 7335992 * 2
def baseEnd_7335992 : Nat := 418543330393129681251377

theorem tailTrace_7335992 : CollatzResearch.WordTrace tailWord_7335992 prefixEnd_7335992 418543330393129681251377 := by
  unfold tailWord_7335992
  simp only [CollatzResearch.WordTrace]
  refine ⟨133782804819480673265613115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178377073092640897687484153 133782804819480673265613115)
  ·
    refine ⟨200674207229221009898419673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133782804819480673265613115 200674207229221009898419673)
    ·
      refine ⟨150505655421915757423814755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200674207229221009898419673 150505655421915757423814755)
      ·
        refine ⟨225758483132873636135722133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150505655421915757423814755 225758483132873636135722133)
        ·
          refine ⟨10582428896853451693861975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 225758483132873636135722133 10582428896853451693861975)
          ·
            refine ⟨15873643345280177540792963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10582428896853451693861975 15873643345280177540792963)
            ·
              refine ⟨23810465017920266311189445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15873643345280177540792963 23810465017920266311189445)
              ·
                refine ⟨4464462190860049933348021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23810465017920266311189445 4464462190860049933348021)
                ·
                  refine ⟨418543330393129681251377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4464462190860049933348021 418543330393129681251377)
                  ·
                    rfl

theorem cell23_7335992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 5].length) (baseStart_7335992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7335992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7335992 prefixEnd_7335992 := by exact prefixLift 7335992
  have htrace : WordTrace (prefixWord ++ tailWord_7335992) baseStart_7335992 baseEnd_7335992 := by
    simpa [prefixWord, tailWord_7335992, baseEnd_7335992] using wordTrace_append hprefix tailTrace_7335992
  have hstable : (prefixWord ++ tailWord_7335992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7335992).length < 2 ^ (prefixWord ++ tailWord_7335992).sum := by decide
  have hdescent : baseEnd_7335992 < baseStart_7335992 := by decide
  rcases family_descends (prefixWord ++ tailWord_7335992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336025 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 1, 6, 2]
def baseStart_7336025 : Nat := 118140960795 + 7336025 * 2 ^ 59
def prefixEnd_7336025 : Nat := 4983230072969 + 3 ^ 40 * 7336025 * 2
def baseEnd_7336025 : Nat := 3766906918399765502149741

theorem tailTrace_7336025 : CollatzResearch.WordTrace tailWord_7336025 prefixEnd_7336025 3766906918399765502149741 := by
  unfold tailWord_7336025
  simp only [CollatzResearch.WordTrace]
  refine ⟨267566813247841793167177529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178377875498561195444785019 267566813247841793167177529)
  ·
    refine ⟨200675109935881344875383147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267566813247841793167177529 200675109935881344875383147)
    ·
      refine ⟨301012664903822017313074721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200675109935881344875383147 301012664903822017313074721)
      ·
        refine ⟨225759498677866512984806041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301012664903822017313074721 225759498677866512984806041)
        ·
          refine ⟨169319624008399884738604531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225759498677866512984806041 169319624008399884738604531)
          ·
            refine ⟨253979436012599827107906797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169319624008399884738604531 253979436012599827107906797)
            ·
              refine ⟨95242288504724935165465049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 253979436012599827107906797 95242288504724935165465049)
              ·
                refine ⟨71431716378543701374098787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95242288504724935165465049 71431716378543701374098787)
                ·
                  refine ⟨107147574567815552061148181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71431716378543701374098787 107147574567815552061148181)
                  ·
                    refine ⟨5022542557866354002866321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107147574567815552061148181 5022542557866354002866321)
                    ·
                      refine ⟨3766906918399765502149741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5022542557866354002866321 3766906918399765502149741)
                      ·
                        rfl

theorem cell23_7336025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 1, 6, 2].length) (baseStart_7336025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336025 prefixEnd_7336025 := by exact prefixLift 7336025
  have htrace : WordTrace (prefixWord ++ tailWord_7336025) baseStart_7336025 baseEnd_7336025 := by
    simpa [prefixWord, tailWord_7336025, baseEnd_7336025] using wordTrace_append hprefix tailTrace_7336025
  have hstable : (prefixWord ++ tailWord_7336025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336025).length < 2 ^ (prefixWord ++ tailWord_7336025).sum := by decide
  have hdescent : baseEnd_7336025 < baseStart_7336025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336103 : List Nat := [1, 1, 6, 2, 2, 1, 3, 2, 1, 4]
def baseStart_7336103 : Nat := 118140960795 + 7336103 * 2 ^ 59
def prefixEnd_7336103 : Nat := 4983230072969 + 3 ^ 40 * 7336103 * 2
def baseEnd_7336103 : Nat := 1255648989963605398991461

theorem tailTrace_7336103 : CollatzResearch.WordTrace tailWord_7336103 prefixEnd_7336103 1255648989963605398991461 := by
  unfold tailWord_7336103
  simp only [CollatzResearch.WordTrace]
  refine ⟨267569658141559212488516963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178379772094372808325677975 267569658141559212488516963)
  ·
    refine ⟨401354487212338818732775445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267569658141559212488516963 401354487212338818732775445)
    ·
      refine ⟨18813491588078382128098849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 401354487212338818732775445 18813491588078382128098849)
      ·
        refine ⟨14110118691058786596074137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18813491588078382128098849 14110118691058786596074137)
        ·
          refine ⟨10582589018294089947055603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14110118691058786596074137 10582589018294089947055603)
          ·
            refine ⟨15873883527441134920583405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10582589018294089947055603 15873883527441134920583405)
            ·
              refine ⟨5952706322790425595218777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15873883527441134920583405 5952706322790425595218777)
              ·
                refine ⟨4464529742092819196414083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5952706322790425595218777 4464529742092819196414083)
                ·
                  refine ⟨6696794613139228794621125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4464529742092819196414083 6696794613139228794621125)
                  ·
                    refine ⟨1255648989963605398991461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6696794613139228794621125 1255648989963605398991461)
                    ·
                      rfl

theorem cell23_7336103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_7336103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336103 prefixEnd_7336103 := by exact prefixLift 7336103
  have htrace : WordTrace (prefixWord ++ tailWord_7336103) baseStart_7336103 baseEnd_7336103 := by
    simpa [prefixWord, tailWord_7336103, baseEnd_7336103] using wordTrace_append hprefix tailTrace_7336103
  have hstable : (prefixWord ++ tailWord_7336103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336103).length < 2 ^ (prefixWord ++ tailWord_7336103).sum := by decide
  have hdescent : baseEnd_7336103 < baseStart_7336103 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336115 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 4]
def baseStart_7336115 : Nat := 118140960795 + 7336115 * 2 ^ 59
def prefixEnd_7336115 : Nat := 4983230072969 + 3 ^ 40 * 7336115 * 2
def baseEnd_7336115 : Nat := 3766953131658670150024327

theorem tailTrace_7336115 : CollatzResearch.WordTrace tailWord_7336115 prefixEnd_7336115 3766953131658670150024327 := by
  unfold tailWord_7336115
  simp only [CollatzResearch.WordTrace]
  refine ⟨267570095817515738537953799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178380063878343825691969199 267570095817515738537953799)
  ·
    refine ⟨401355143726273607806930699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267570095817515738537953799 401355143726273607806930699)
    ·
      refine ⟨602032715589410411710396049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401355143726273607806930699 602032715589410411710396049)
      ·
        refine ⟨451524536692057808782797037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602032715589410411710396049 451524536692057808782797037)
        ·
          refine ⟨169321701259521678293548889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451524536692057808782797037 169321701259521678293548889)
          ·
            refine ⟨126991275944641258720161667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169321701259521678293548889 126991275944641258720161667)
            ·
              refine ⟨190486913916961888080242501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126991275944641258720161667 190486913916961888080242501)
              ·
                refine ⟨35716296359430354015045469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190486913916961888080242501 35716296359430354015045469)
                ·
                  refine ⟨13393611134786382755642051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35716296359430354015045469 13393611134786382755642051)
                  ·
                    refine ⟨20090416702179574133463077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13393611134786382755642051 20090416702179574133463077)
                    ·
                      refine ⟨3766953131658670150024327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20090416702179574133463077 3766953131658670150024327)
                      ·
                        rfl

theorem cell23_7336115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 3, 1, 4].length) (baseStart_7336115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336115 prefixEnd_7336115 := by exact prefixLift 7336115
  have htrace : WordTrace (prefixWord ++ tailWord_7336115) baseStart_7336115 baseEnd_7336115 := by
    simpa [prefixWord, tailWord_7336115, baseEnd_7336115] using wordTrace_append hprefix tailTrace_7336115
  have hstable : (prefixWord ++ tailWord_7336115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336115).length < 2 ^ (prefixWord ++ tailWord_7336115).sum := by decide
  have hdescent : baseEnd_7336115 < baseStart_7336115 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336125 : List Nat := [1, 4, 1, 2, 1, 1, 1, 5, 1, 6]
def baseStart_7336125 : Nat := 118140960795 + 7336125 * 2 ^ 59
def prefixEnd_7336125 : Nat := 4983230072969 + 3 ^ 40 * 7336125 * 2
def baseEnd_7336125 : Nat := 1255652755488405036966427

theorem tailTrace_7336125 : CollatzResearch.WordTrace tailWord_7336125 prefixEnd_7336125 1255652755488405036966427 := by
  unfold tailWord_7336125
  simp only [CollatzResearch.WordTrace]
  refine ⟨267570460547479510245817829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178380307031653006830545219 267570460547479510245817829)
  ·
    refine ⟨50169461352652408171090843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267570460547479510245817829 50169461352652408171090843)
    ·
      refine ⟨75254192028978612256636265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50169461352652408171090843 75254192028978612256636265)
      ·
        refine ⟨56440644021733959192477199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75254192028978612256636265 56440644021733959192477199)
        ·
          refine ⟨84660966032600938788715799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56440644021733959192477199 84660966032600938788715799)
          ·
            refine ⟨126991449048901408183073699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84660966032600938788715799 126991449048901408183073699)
            ·
              refine ⟨190487173573352112274610549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126991449048901408183073699 190487173573352112274610549)
              ·
                refine ⟨17858172522501760525744739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190487173573352112274610549 17858172522501760525744739)
                ·
                  refine ⟨26787258783752640788617109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17858172522501760525744739 26787258783752640788617109)
                  ·
                    refine ⟨1255652755488405036966427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26787258783752640788617109 1255652755488405036966427)
                    ·
                      rfl

theorem cell23_7336125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_7336125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336125 prefixEnd_7336125 := by exact prefixLift 7336125
  have htrace : WordTrace (prefixWord ++ tailWord_7336125) baseStart_7336125 baseEnd_7336125 := by
    simpa [prefixWord, tailWord_7336125, baseEnd_7336125] using wordTrace_append hprefix tailTrace_7336125
  have hstable : (prefixWord ++ tailWord_7336125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336125).length < 2 ^ (prefixWord ++ tailWord_7336125).sum := by decide
  have hdescent : baseEnd_7336125 < baseStart_7336125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336129 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 3, 5]
def baseStart_7336129 : Nat := 118140960795 + 7336129 * 2 ^ 59
def prefixEnd_7336129 : Nat := 4983230072969 + 3 ^ 40 * 7336129 * 2
def baseEnd_7336129 : Nat := 1255653440129277698416421

theorem tailTrace_7336129 : CollatzResearch.WordTrace tailWord_7336129 prefixEnd_7336129 1255653440129277698416421 := by
  unfold tailWord_7336129
  simp only [CollatzResearch.WordTrace]
  refine ⟨267570606439465018928963441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178380404292976679285975627 267570606439465018928963441)
  ·
    refine ⟨200677954829598764196722581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267570606439465018928963441 200677954829598764196722581)
    ·
      refine ⟨9406779132637442071721371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 200677954829598764196722581 9406779132637442071721371)
      ·
        refine ⟨14110168698956163107582057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9406779132637442071721371 14110168698956163107582057)
        ·
          refine ⟨10582626524217122330686543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14110168698956163107582057 10582626524217122330686543)
          ·
            refine ⟨15873939786325683496029815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10582626524217122330686543 15873939786325683496029815)
            ·
              refine ⟨23810909679488525244044723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15873939786325683496029815 23810909679488525244044723)
              ·
                refine ⟨35716364519232787866067085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23810909679488525244044723 35716364519232787866067085)
                ·
                  refine ⟨13393636694712295449775157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35716364519232787866067085 13393636694712295449775157)
                  ·
                    refine ⟨1255653440129277698416421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13393636694712295449775157 1255653440129277698416421)
                    ·
                      rfl

theorem cell23_7336129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_7336129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336129 prefixEnd_7336129 := by exact prefixLift 7336129
  have htrace : WordTrace (prefixWord ++ tailWord_7336129) baseStart_7336129 baseEnd_7336129 := by
    simpa [prefixWord, tailWord_7336129, baseEnd_7336129] using wordTrace_append hprefix tailTrace_7336129
  have hstable : (prefixWord ++ tailWord_7336129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336129).length < 2 ^ (prefixWord ++ tailWord_7336129).sum := by decide
  have hdescent : baseEnd_7336129 < baseStart_7336129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336142 : List Nat := [4, 1, 1, 1, 4, 2, 1, 2, 1, 6]
def baseStart_7336142 : Nat := 118140960795 + 7336142 * 2 ^ 59
def prefixEnd_7336142 : Nat := 4983230072969 + 3 ^ 40 * 7336142 * 2
def baseEnd_7336142 : Nat := 1255655665212113848128901

theorem tailTrace_7336142 : CollatzResearch.WordTrace tailWord_7336142 prefixEnd_7336142 1255655665212113848128901 := by
  unfold tailWord_7336142
  simp only [CollatzResearch.WordTrace]
  refine ⟨33446385073552240268648335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178380720392278614766124453 33446385073552240268648335)
  ·
    refine ⟨50169577610328360402972503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33446385073552240268648335 50169577610328360402972503)
    ·
      refine ⟨75254366415492540604458755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50169577610328360402972503 75254366415492540604458755)
      ·
        refine ⟨112881549623238810906688133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75254366415492540604458755 112881549623238810906688133)
        ·
          refine ⟨21165290554357277045004025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112881549623238810906688133 21165290554357277045004025)
          ·
            refine ⟨15873967915767957783753019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21165290554357277045004025 15873967915767957783753019)
            ·
              refine ⟨23810951873651936675629529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15873967915767957783753019 23810951873651936675629529)
              ·
                refine ⟨17858213905238952506722147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23810951873651936675629529 17858213905238952506722147)
                ·
                  refine ⟨26787320857858428760083221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17858213905238952506722147 26787320857858428760083221)
                  ·
                    refine ⟨1255655665212113848128901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26787320857858428760083221 1255655665212113848128901)
                    ·
                      rfl

theorem cell23_7336142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_7336142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336142 prefixEnd_7336142 := by exact prefixLift 7336142
  have htrace : WordTrace (prefixWord ++ tailWord_7336142) baseStart_7336142 baseEnd_7336142 := by
    simpa [prefixWord, tailWord_7336142, baseEnd_7336142] using wordTrace_append hprefix tailTrace_7336142
  have hstable : (prefixWord ++ tailWord_7336142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336142).length < 2 ^ (prefixWord ++ tailWord_7336142).sum := by decide
  have hdescent : baseEnd_7336142 < baseStart_7336142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336145 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 3, 2, 4]
def baseStart_7336145 : Nat := 118140960795 + 7336145 * 2 ^ 59
def prefixEnd_7336145 : Nat := 4983230072969 + 3 ^ 40 * 7336145 * 2
def baseEnd_7336145 : Nat := 3766968536078305032649189

theorem tailTrace_7336145 : CollatzResearch.WordTrace tailWord_7336145 prefixEnd_7336145 3766968536078305032649189 := by
  unfold tailWord_7336145
  simp only [CollatzResearch.WordTrace]
  refine ⟨267571190007407053661545889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178380793338271369107697259 267571190007407053661545889)
  ·
    refine ⟨200678392505555290246159417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267571190007407053661545889 200678392505555290246159417)
    ·
      refine ⟨150508794379166467684619563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200678392505555290246159417 150508794379166467684619563)
      ·
        refine ⟨225763191568749701526929345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150508794379166467684619563 225763191568749701526929345)
        ·
          refine ⟨169322393676562276145197009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225763191568749701526929345 169322393676562276145197009)
          ·
            refine ⟨126991795257421707108897757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169322393676562276145197009 126991795257421707108897757)
            ·
              refine ⟨47621923221533140165836659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126991795257421707108897757 47621923221533140165836659)
              ·
                refine ⟨71432884832299710248754989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47621923221533140165836659 71432884832299710248754989)
                ·
                  refine ⟨26787331812112391343283121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71432884832299710248754989 26787331812112391343283121)
                  ·
                    refine ⟨20090498859084293507462341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26787331812112391343283121 20090498859084293507462341)
                    ·
                      refine ⟨3766968536078305032649189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20090498859084293507462341 3766968536078305032649189)
                      ·
                        rfl

theorem cell23_7336145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_7336145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336145 prefixEnd_7336145 := by exact prefixLift 7336145
  have htrace : WordTrace (prefixWord ++ tailWord_7336145) baseStart_7336145 baseEnd_7336145 := by
    simpa [prefixWord, tailWord_7336145, baseEnd_7336145] using wordTrace_append hprefix tailTrace_7336145
  have hstable : (prefixWord ++ tailWord_7336145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336145).length < 2 ^ (prefixWord ++ tailWord_7336145).sum := by decide
  have hdescent : baseEnd_7336145 < baseStart_7336145 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336152 : List Nat := [2, 1, 2, 2, 4, 1, 3, 1, 1, 1, 5]
def baseStart_7336152 : Nat := 118140960795 + 7336152 * 2 ^ 59
def prefixEnd_7336152 : Nat := 4983230072969 + 3 ^ 40 * 7336152 * 2
def baseEnd_7336152 : Nat := 3766972130442886505261657

theorem tailTrace_7336152 : CollatzResearch.WordTrace tailWord_7336152 prefixEnd_7336152 3766972130442886505261657 := by
  unfold tailWord_7336152
  simp only [CollatzResearch.WordTrace]
  refine ⟨133785722659190846928525355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178380963545587795904700473 133785722659190846928525355)
  ·
    refine ⟨200678583988786270392788033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133785722659190846928525355 200678583988786270392788033)
    ·
      refine ⟨150508937991589702794591025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200678583988786270392788033 150508937991589702794591025)
      ·
        refine ⟨112881703493692277095943269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150508937991589702794591025 112881703493692277095943269)
        ·
          refine ⟨21165319405067301955489363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112881703493692277095943269 21165319405067301955489363)
          ·
            refine ⟨31747979107600952933234045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21165319405067301955489363 31747979107600952933234045)
            ·
              refine ⟨11905492165350357349962767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31747979107600952933234045 11905492165350357349962767)
              ·
                refine ⟨17858238248025536024944151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11905492165350357349962767 17858238248025536024944151)
                ·
                  refine ⟨26787357372038304037416227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17858238248025536024944151 26787357372038304037416227)
                  ·
                    refine ⟨40181036058057456056124341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26787357372038304037416227 40181036058057456056124341)
                    ·
                      refine ⟨3766972130442886505261657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40181036058057456056124341 3766972130442886505261657)
                      ·
                        rfl

theorem cell23_7336152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 1, 1, 1, 5].length) (baseStart_7336152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336152 prefixEnd_7336152 := by exact prefixLift 7336152
  have htrace : WordTrace (prefixWord ++ tailWord_7336152) baseStart_7336152 baseEnd_7336152 := by
    simpa [prefixWord, tailWord_7336152, baseEnd_7336152] using wordTrace_append hprefix tailTrace_7336152
  have hstable : (prefixWord ++ tailWord_7336152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336152).length < 2 ^ (prefixWord ++ tailWord_7336152).sum := by decide
  have hdescent : baseEnd_7336152 < baseStart_7336152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336195 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 5]
def baseStart_7336195 : Nat := 118140960795 + 7336195 * 2 ^ 59
def prefixEnd_7336195 : Nat := 4983230072969 + 3 ^ 40 * 7336195 * 2
def baseEnd_7336195 : Nat := 3766994210111029837023959

theorem tailTrace_7336195 : CollatzResearch.WordTrace tailWord_7336195 prefixEnd_7336195 3766994210111029837023959 := by
  unfold tailWord_7336195
  simp only [CollatzResearch.WordTrace]
  refine ⟨267573013657225912200866039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178382009104817274800577359 267573013657225912200866039)
  ·
    refine ⟨401359520485838868301299059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267573013657225912200866039 401359520485838868301299059)
    ·
      refine ⟨602039280728758302451948589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401359520485838868301299059 602039280728758302451948589)
      ·
        refine ⟨225764730273284363419480721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 602039280728758302451948589 225764730273284363419480721)
        ·
          refine ⟨169323547704963272564610541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225764730273284363419480721 169323547704963272564610541)
          ·
            refine ⟨63496330389361227211728953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169323547704963272564610541 63496330389361227211728953)
            ·
              refine ⟨47622247792020920408796715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63496330389361227211728953 47622247792020920408796715)
              ·
                refine ⟨71433371688031380613195073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47622247792020920408796715 71433371688031380613195073)
                ·
                  refine ⟨53575028766023535459896305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71433371688031380613195073 53575028766023535459896305)
                  ·
                    refine ⟨40181271574517651594922229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53575028766023535459896305 40181271574517651594922229)
                    ·
                      refine ⟨3766994210111029837023959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40181271574517651594922229 3766994210111029837023959)
                      ·
                        rfl

theorem cell23_7336195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_7336195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336195 prefixEnd_7336195 := by exact prefixLift 7336195
  have htrace : WordTrace (prefixWord ++ tailWord_7336195) baseStart_7336195 baseEnd_7336195 := by
    simpa [prefixWord, tailWord_7336195, baseEnd_7336195] using wordTrace_append hprefix tailTrace_7336195
  have hstable : (prefixWord ++ tailWord_7336195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336195).length < 2 ^ (prefixWord ++ tailWord_7336195).sum := by decide
  have hdescent : baseEnd_7336195 < baseStart_7336195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336239 : List Nat := [1, 1, 2, 1, 2, 1, 7, 1, 1, 4, 2]
def baseStart_7336239 : Nat := 118140960795 + 7336239 * 2 ^ 59
def prefixEnd_7336239 : Nat := 4983230072969 + 3 ^ 40 * 7336239 * 2
def baseEnd_7336239 : Nat := 3767016803259827664873757

theorem tailTrace_7336239 : CollatzResearch.WordTrace tailWord_7336239 prefixEnd_7336239 3767016803259827664873757 := by
  unfold tailWord_7336239
  simp only [CollatzResearch.WordTrace]
  refine ⟨267574618469066507715467771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178383078979377671810311847 267574618469066507715467771)
  ·
    refine ⟨401361927703599761573201657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267574618469066507715467771 401361927703599761573201657)
    ·
      refine ⟨301021445777699821179901243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401361927703599761573201657 301021445777699821179901243)
      ·
        refine ⟨451532168666549731769851865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301021445777699821179901243 451532168666549731769851865)
        ·
          refine ⟨338649126499912298827388899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451532168666549731769851865 338649126499912298827388899)
          ·
            refine ⟨507973689749868448241083349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338649126499912298827388899 507973689749868448241083349)
            ·
              refine ⟨11905633353512541755650391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 507973689749868448241083349 11905633353512541755650391)
              ·
                refine ⟨17858450030268812633475587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11905633353512541755650391 17858450030268812633475587)
                ·
                  refine ⟨26787675045403218950213381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17858450030268812633475587 26787675045403218950213381)
                  ·
                    refine ⟨5022689071013103553165009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26787675045403218950213381 5022689071013103553165009)
                    ·
                      refine ⟨3767016803259827664873757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5022689071013103553165009 3767016803259827664873757)
                      ·
                        rfl

theorem cell23_7336239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 1, 1, 4, 2].length) (baseStart_7336239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336239 prefixEnd_7336239 := by exact prefixLift 7336239
  have htrace : WordTrace (prefixWord ++ tailWord_7336239) baseStart_7336239 baseEnd_7336239 := by
    simpa [prefixWord, tailWord_7336239, baseEnd_7336239] using wordTrace_append hprefix tailTrace_7336239
  have hstable : (prefixWord ++ tailWord_7336239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336239).length < 2 ^ (prefixWord ++ tailWord_7336239).sum := by decide
  have hdescent : baseEnd_7336239 < baseStart_7336239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336275 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 3, 7]
def baseStart_7336275 : Nat := 118140960795 + 7336275 * 2 ^ 59
def prefixEnd_7336275 : Nat := 4983230072969 + 3 ^ 40 * 7336275 * 2
def baseEnd_7336275 : Nat := 1255678429521129841341197

theorem tailTrace_7336275 : CollatzResearch.WordTrace tailWord_7336275 prefixEnd_7336275 1255678429521129841341197 := by
  unfold tailWord_7336275
  simp only [CollatzResearch.WordTrace]
  refine ⟨267575931496936085863778279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178383954331290723909185519 267575931496936085863778279)
  ·
    refine ⟨401363897245404128795667419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267575931496936085863778279 401363897245404128795667419)
    ·
      refine ⟨602045845868106193193501129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401363897245404128795667419 602045845868106193193501129)
      ·
        refine ⟨451534384401079644895125847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602045845868106193193501129 451534384401079644895125847)
        ·
          refine ⟨677301576601619467342688771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451534384401079644895125847 677301576601619467342688771)
          ·
            refine ⟨1015952364902429201014033157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677301576601619467342688771 1015952364902429201014033157)
            ·
              refine ⟨190491068419205475190131217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1015952364902429201014033157 190491068419205475190131217)
              ·
                refine ⟨142868301314404106392598413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190491068419205475190131217 142868301314404106392598413)
                ·
                  refine ⟨53575612992901539897224405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142868301314404106392598413 53575612992901539897224405)
                  ·
                    refine ⟨1255678429521129841341197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53575612992901539897224405 1255678429521129841341197)
                    ·
                      rfl

theorem cell23_7336275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 7].length) (baseStart_7336275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336275 prefixEnd_7336275 := by exact prefixLift 7336275
  have htrace : WordTrace (prefixWord ++ tailWord_7336275) baseStart_7336275 baseEnd_7336275 := by
    simpa [prefixWord, tailWord_7336275, baseEnd_7336275] using wordTrace_append hprefix tailTrace_7336275
  have hstable : (prefixWord ++ tailWord_7336275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336275).length < 2 ^ (prefixWord ++ tailWord_7336275).sum := by decide
  have hdescent : baseEnd_7336275 < baseStart_7336275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336290 : List Nat := [3, 3, 2, 1, 1, 2, 4, 1, 2, 2, 2]
def baseStart_7336290 : Nat := 118140960795 + 7336290 * 2 ^ 59
def prefixEnd_7336290 : Nat := 4983230072969 + 3 ^ 40 * 7336290 * 2
def baseEnd_7336290 : Nat := 3767042990773206965336023

theorem tailTrace_7336290 : CollatzResearch.WordTrace tailWord_7336290 prefixEnd_7336290 3767042990773206965336023 := by
  unfold tailWord_7336290
  simp only [CollatzResearch.WordTrace]
  refine ⟨66894119647970435856393581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178384319061254495617049549 66894119647970435856393581)
  ·
    refine ⟨25085294867988913446147593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66894119647970435856393581 25085294867988913446147593)
    ·
      refine ⟨18813971150991685084610695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25085294867988913446147593 18813971150991685084610695)
      ·
        refine ⟨28220956726487527626916043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18813971150991685084610695 28220956726487527626916043)
        ·
          refine ⟨42331435089731291440374065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28220956726487527626916043 42331435089731291440374065)
          ·
            refine ⟨31748576317298468580280549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42331435089731291440374065 31748576317298468580280549)
            ·
              refine ⟨5952858059493462858802603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31748576317298468580280549 5952858059493462858802603)
              ·
                refine ⟨8929287089240194288203905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5952858059493462858802603 8929287089240194288203905)
                ·
                  refine ⟨6696965316930145716152929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8929287089240194288203905 6696965316930145716152929)
                  ·
                    refine ⟨5022723987697609287114697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6696965316930145716152929 5022723987697609287114697)
                    ·
                      refine ⟨3767042990773206965336023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5022723987697609287114697 3767042990773206965336023)
                      ·
                        rfl

theorem cell23_7336290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_7336290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336290 prefixEnd_7336290 := by exact prefixLift 7336290
  have htrace : WordTrace (prefixWord ++ tailWord_7336290) baseStart_7336290 baseEnd_7336290 := by
    simpa [prefixWord, tailWord_7336290, baseEnd_7336290] using wordTrace_append hprefix tailTrace_7336290
  have hstable : (prefixWord ++ tailWord_7336290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336290).length < 2 ^ (prefixWord ++ tailWord_7336290).sum := by decide
  have hdescent : baseEnd_7336290 < baseStart_7336290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336292 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 4, 5]
def baseStart_7336292 : Nat := 118140960795 + 7336292 * 2 ^ 59
def prefixEnd_7336292 : Nat := 4983230072969 + 3 ^ 40 * 7336292 * 2
def baseEnd_7336292 : Nat := 1255681339244838652503671

theorem tailTrace_7336292 : CollatzResearch.WordTrace tailWord_7336292 prefixEnd_7336292 1255681339244838652503671 := by
  unfold tailWord_7336292
  simp only [CollatzResearch.WordTrace]
  refine ⟨133788275768937248883573565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178384367691916331844764753 133788275768937248883573565)
  ·
    refine ⟨50170603413351468331340087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133788275768937248883573565 50170603413351468331340087)
    ·
      refine ⟨75255905120027202497010131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50170603413351468331340087 75255905120027202497010131)
      ·
        refine ⟨112883857680040803745515197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75255905120027202497010131 112883857680040803745515197)
        ·
          refine ⟨42331446630015301404568199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112883857680040803745515197 42331446630015301404568199)
          ·
            refine ⟨63497169945022952106852299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42331446630015301404568199 63497169945022952106852299)
            ·
              refine ⟨95245754917534428160278449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63497169945022952106852299 95245754917534428160278449)
              ·
                refine ⟨71434316188150821120208837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95245754917534428160278449 71434316188150821120208837)
                ·
                  refine ⟨13393934285278278960039157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71434316188150821120208837 13393934285278278960039157)
                  ·
                    refine ⟨1255681339244838652503671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13393934285278278960039157 1255681339244838652503671)
                    ·
                      rfl

theorem cell23_7336292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_7336292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336292 prefixEnd_7336292 := by exact prefixLift 7336292
  have htrace : WordTrace (prefixWord ++ tailWord_7336292) baseStart_7336292 baseEnd_7336292 := by
    simpa [prefixWord, tailWord_7336292, baseEnd_7336292] using wordTrace_append hprefix tailTrace_7336292
  have hstable : (prefixWord ++ tailWord_7336292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336292).length < 2 ^ (prefixWord ++ tailWord_7336292).sum := by decide
  have hdescent : baseEnd_7336292 < baseStart_7336292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336309 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 2, 5]
def baseStart_7336309 : Nat := 118140960795 + 7336309 * 2 ^ 59
def prefixEnd_7336309 : Nat := 4983230072969 + 3 ^ 40 * 7336309 * 2
def baseEnd_7336309 : Nat := 1255684248968547463666145

theorem tailTrace_7336309 : CollatzResearch.WordTrace tailWord_7336309 prefixEnd_7336309 1255684248968547463666145 := by
  unfold tailWord_7336309
  simp only [CollatzResearch.WordTrace]
  refine ⟨267577171578812909670515981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178384781052541939780343987 267577171578812909670515981)
  ·
    refine ⟨100341439342054841126443493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267577171578812909670515981 100341439342054841126443493)
    ·
      refine ⟨18814019876635282711208155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100341439342054841126443493 18814019876635282711208155)
      ·
        refine ⟨28221029814952924066812233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18814019876635282711208155 28221029814952924066812233)
        ·
          refine ⟨21165772361214693050109175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28221029814952924066812233 21165772361214693050109175)
          ·
            refine ⟨31748658541822039575163763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21165772361214693050109175 31748658541822039575163763)
            ·
              refine ⟨47622987812733059362745645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31748658541822039575163763 47622987812733059362745645)
              ·
                refine ⟨17858620429774897261029617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47622987812733059362745645 17858620429774897261029617)
                ·
                  refine ⟨13393965322331172945772213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17858620429774897261029617 13393965322331172945772213)
                  ·
                    refine ⟨1255684248968547463666145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13393965322331172945772213 1255684248968547463666145)
                    ·
                      rfl

theorem cell23_7336309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_7336309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336309 prefixEnd_7336309 := by exact prefixLift 7336309
  have htrace : WordTrace (prefixWord ++ tailWord_7336309) baseStart_7336309 baseEnd_7336309 := by
    simpa [prefixWord, tailWord_7336309, baseEnd_7336309] using wordTrace_append hprefix tailTrace_7336309
  have hstable : (prefixWord ++ tailWord_7336309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336309).length < 2 ^ (prefixWord ++ tailWord_7336309).sum := by decide
  have hdescent : baseEnd_7336309 < baseStart_7336309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336329 : List Nat := [1, 2, 1, 1, 6, 1, 2, 2, 2, 1, 4]
def baseStart_7336329 : Nat := 118140960795 + 7336329 * 2 ^ 59
def prefixEnd_7336329 : Nat := 4983230072969 + 3 ^ 40 * 7336329 * 2
def baseEnd_7336329 : Nat := 3767063016518732312748343

theorem tailTrace_7336329 : CollatzResearch.WordTrace tailWord_7336329 prefixEnd_7336329 3767063016518732312748343 := by
  unfold tailWord_7336329
  simp only [CollatzResearch.WordTrace]
  refine ⟨267577901038740453086244041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178385267359160302057496027 267577901038740453086244041)
  ·
    refine ⟨200683425779055339814683031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267577901038740453086244041 200683425779055339814683031)
    ·
      refine ⟨301025138668583009722024547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200683425779055339814683031 301025138668583009722024547)
      ·
        refine ⟨451537708002874514583036821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301025138668583009722024547 451537708002874514583036821)
        ·
          refine ⟨21165830062634742871079851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 451537708002874514583036821 21165830062634742871079851)
          ·
            refine ⟨31748745093952114306619777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21165830062634742871079851 31748745093952114306619777)
            ·
              refine ⟨23811558820464085729964833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31748745093952114306619777 23811558820464085729964833)
              ·
                refine ⟨17858669115348064297473625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23811558820464085729964833 17858669115348064297473625)
                ·
                  refine ⟨13394001836511048223105219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17858669115348064297473625 13394001836511048223105219)
                  ·
                    refine ⟨20091002754766572334657829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13394001836511048223105219 20091002754766572334657829)
                    ·
                      refine ⟨3767063016518732312748343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20091002754766572334657829 3767063016518732312748343)
                      ·
                        rfl

theorem cell23_7336329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 2, 1, 4].length) (baseStart_7336329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336329 prefixEnd_7336329 := by exact prefixLift 7336329
  have htrace : WordTrace (prefixWord ++ tailWord_7336329) baseStart_7336329 baseEnd_7336329 := by
    simpa [prefixWord, tailWord_7336329, baseEnd_7336329] using wordTrace_append hprefix tailTrace_7336329
  have hstable : (prefixWord ++ tailWord_7336329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336329).length < 2 ^ (prefixWord ++ tailWord_7336329).sum := by decide
  have hdescent : baseEnd_7336329 < baseStart_7336329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336330 : List Nat := [3, 1, 2, 5, 1, 2, 2, 2, 5]
def baseStart_7336330 : Nat := 118140960795 + 7336330 * 2 ^ 59
def prefixEnd_7336330 : Nat := 4983230072969 + 3 ^ 40 * 7336330 * 2
def baseEnd_7336330 : Nat := 418562614444376312092871

theorem tailTrace_7336330 : CollatzResearch.WordTrace tailWord_7336330 prefixEnd_7336330 418562614444376312092871 := by
  unfold tailWord_7336330
  simp only [CollatzResearch.WordTrace]
  refine ⟨66894484377934207564257611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178385291674491220171353629 66894484377934207564257611)
  ·
    refine ⟨100341726566901311346386417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66894484377934207564257611 100341726566901311346386417)
    ·
      refine ⟨75256294925175983509789813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100341726566901311346386417 75256294925175983509789813)
      ·
        refine ⟨7055277649235248454042795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75256294925175983509789813 7055277649235248454042795)
        ·
          refine ⟨10582916473852872681064193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7055277649235248454042795 10582916473852872681064193)
          ·
            refine ⟨7937187355389654510798145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10582916473852872681064193 7937187355389654510798145)
            ·
              refine ⟨5952890516542240883098609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7937187355389654510798145 5952890516542240883098609)
              ·
                refine ⟨4464667887406680662323957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5952890516542240883098609 4464667887406680662323957)
                ·
                  refine ⟨418562614444376312092871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4464667887406680662323957 418562614444376312092871)
                  ·
                    rfl

theorem cell23_7336330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 2, 2, 2, 5].length) (baseStart_7336330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336330 prefixEnd_7336330 := by exact prefixLift 7336330
  have htrace : WordTrace (prefixWord ++ tailWord_7336330) baseStart_7336330 baseEnd_7336330 := by
    simpa [prefixWord, tailWord_7336330, baseEnd_7336330] using wordTrace_append hprefix tailTrace_7336330
  have hstable : (prefixWord ++ tailWord_7336330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336330).length < 2 ^ (prefixWord ++ tailWord_7336330).sum := by decide
  have hdescent : baseEnd_7336330 < baseStart_7336330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336346 : List Nat := [3, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2]
def baseStart_7336346 : Nat := 118140960795 + 7336346 * 2 ^ 59
def prefixEnd_7336346 : Nat := 4983230072969 + 3 ^ 40 * 7336346 * 2
def baseEnd_7336346 : Nat := 3767071745689858746235765

theorem tailTrace_7336346 : CollatzResearch.WordTrace tailWord_7336346 prefixEnd_7336346 3767071745689858746235765 := by
  unfold tailWord_7336346
  simp only [CollatzResearch.WordTrace]
  refine ⟨66894630269919716247403223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178385680719785909993075261 66894630269919716247403223)
  ·
    refine ⟨100341945404879574371104835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66894630269919716247403223 100341945404879574371104835)
    ·
      refine ⟨150512918107319361556657253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100341945404879574371104835 150512918107319361556657253)
      ·
        refine ⟨28221172145122380291873235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150512918107319361556657253 28221172145122380291873235)
        ·
          refine ⟨42331758217683570437809853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28221172145122380291873235 42331758217683570437809853)
          ·
            refine ⟨15874409331631338914178695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42331758217683570437809853 15874409331631338914178695)
            ·
              refine ⟨23811613997447008371268043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15874409331631338914178695 23811613997447008371268043)
              ·
                refine ⟨35717420996170512556902065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23811613997447008371268043 35717420996170512556902065)
                ·
                  refine ⟨26788065747127884417676549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35717420996170512556902065 26788065747127884417676549)
                  ·
                    refine ⟨5022762327586478328314353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26788065747127884417676549 5022762327586478328314353)
                    ·
                      refine ⟨3767071745689858746235765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5022762327586478328314353 3767071745689858746235765)
                      ·
                        rfl

theorem cell23_7336346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 1, 2, 4, 2].length) (baseStart_7336346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336346 prefixEnd_7336346 := by exact prefixLift 7336346
  have htrace : WordTrace (prefixWord ++ tailWord_7336346) baseStart_7336346 baseEnd_7336346 := by
    simpa [prefixWord, tailWord_7336346, baseEnd_7336346] using wordTrace_append hprefix tailTrace_7336346
  have hstable : (prefixWord ++ tailWord_7336346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336346).length < 2 ^ (prefixWord ++ tailWord_7336346).sum := by decide
  have hdescent : baseEnd_7336346 < baseStart_7336346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336430 : List Nat := [4, 1, 2, 1, 2, 2, 3, 3, 1, 1, 3]
def baseStart_7336430 : Nat := 118140960795 + 7336430 * 2 ^ 59
def prefixEnd_7336430 : Nat := 4983230072969 + 3 ^ 40 * 7336430 * 2
def baseEnd_7336430 : Nat := 3767114878064836417585379

theorem tailTrace_7336430 : CollatzResearch.WordTrace tailWord_7336430 prefixEnd_7336430 3767114878064836417585379 := by
  unfold tailWord_7336430
  simp only [CollatzResearch.WordTrace]
  refine ⟨33447698101421818416958843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178387723207583031557113829 33447698101421818416958843)
  ·
    refine ⟨50171547152132727625438265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33447698101421818416958843 50171547152132727625438265)
    ·
      refine ⟨37628660364099545719078699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50171547152132727625438265 37628660364099545719078699)
      ·
        refine ⟨56442990546149318578618049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37628660364099545719078699 56442990546149318578618049)
        ·
          refine ⟨42332242909611988933963537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56442990546149318578618049 42332242909611988933963537)
          ·
            refine ⟨31749182182208991700472653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42332242909611988933963537 31749182182208991700472653)
            ·
              refine ⟨11905943318328371887677245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31749182182208991700472653 11905943318328371887677245)
              ·
                refine ⟨4464728744373139457878967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11905943318328371887677245 4464728744373139457878967)
                ·
                  refine ⟨6697093116559709186818451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4464728744373139457878967 6697093116559709186818451)
                  ·
                    refine ⟨10045639674839563780227677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6697093116559709186818451 10045639674839563780227677)
                    ·
                      refine ⟨3767114878064836417585379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10045639674839563780227677 3767114878064836417585379)
                      ·
                        rfl

theorem cell23_7336430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_7336430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336430 prefixEnd_7336430 := by exact prefixLift 7336430
  have htrace : WordTrace (prefixWord ++ tailWord_7336430) baseStart_7336430 baseEnd_7336430 := by
    simpa [prefixWord, tailWord_7336430, baseEnd_7336430] using wordTrace_append hprefix tailTrace_7336430
  have hstable : (prefixWord ++ tailWord_7336430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336430).length < 2 ^ (prefixWord ++ tailWord_7336430).sum := by decide
  have hdescent : baseEnd_7336430 < baseStart_7336430 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336449 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_7336449 : Nat := 118140960795 + 7336449 * 2 ^ 59
def prefixEnd_7336449 : Nat := 4983230072969 + 3 ^ 40 * 7336449 * 2
def baseEnd_7336449 : Nat := 3767124634197271843247791

theorem tailTrace_7336449 : CollatzResearch.WordTrace tailWord_7336449 prefixEnd_7336449 3767124634197271843247791 := by
  unfold tailWord_7336449
  simp only [CollatzResearch.WordTrace]
  refine ⟨267582277798305713580612401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178388185198870475720408267 267582277798305713580612401)
  ·
    refine ⟨200686708348729285185459301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267582277798305713580612401 200686708348729285185459301)
    ·
      refine ⟨37628757815386740972273619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200686708348729285185459301 37628757815386740972273619)
      ·
        refine ⟨56443136723080111458410429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37628757815386740972273619 56443136723080111458410429)
        ·
          refine ⟨21166176271155041796903911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56443136723080111458410429 21166176271155041796903911)
          ·
            refine ⟨31749264406732562695355867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21166176271155041796903911 31749264406732562695355867)
            ·
              refine ⟨47623896610098844043033801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31749264406732562695355867 47623896610098844043033801)
              ·
                refine ⟨35717922457574133032275351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47623896610098844043033801 35717922457574133032275351)
                ·
                  refine ⟨53576883686361199548413027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35717922457574133032275351 53576883686361199548413027)
                  ·
                    refine ⟨80365325529541799322619541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53576883686361199548413027 80365325529541799322619541)
                    ·
                      refine ⟨3767124634197271843247791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80365325529541799322619541 3767124634197271843247791)
                      ·
                        rfl

theorem cell23_7336449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_7336449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336449 prefixEnd_7336449 := by exact prefixLift 7336449
  have htrace : WordTrace (prefixWord ++ tailWord_7336449) baseStart_7336449 baseEnd_7336449 := by
    simpa [prefixWord, tailWord_7336449, baseEnd_7336449] using wordTrace_append hprefix tailTrace_7336449
  have hstable : (prefixWord ++ tailWord_7336449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336449).length < 2 ^ (prefixWord ++ tailWord_7336449).sum := by decide
  have hdescent : baseEnd_7336449 < baseStart_7336449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336453 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 3, 2, 2]
def baseStart_7336453 : Nat := 118140960795 + 7336453 * 2 ^ 59
def prefixEnd_7336453 : Nat := 4983230072969 + 3 ^ 40 * 7336453 * 2
def baseEnd_7336453 : Nat := 3767126688119889827597773

theorem tailTrace_7336453 : CollatzResearch.WordTrace tailWord_7336453 prefixEnd_7336453 3767126688119889827597773 := by
  unfold tailWord_7336453
  simp only [CollatzResearch.WordTrace]
  refine ⟨267582423690291222263758013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178388282460194148175838675 267582423690291222263758013)
  ·
    refine ⟨100343408883859208348909255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267582423690291222263758013 100343408883859208348909255)
    ·
      refine ⟨150515113325788812523363883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100343408883859208348909255 150515113325788812523363883)
      ·
        refine ⟨225772669988683218785045825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150515113325788812523363883 225772669988683218785045825)
        ·
          refine ⟨169329502491512414088784369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225772669988683218785045825 169329502491512414088784369)
          ·
            refine ⟨126997126868634310566588277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169329502491512414088784369 126997126868634310566588277)
            ·
              refine ⟨11905980643934466615617651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126997126868634310566588277 11905980643934466615617651)
              ·
                refine ⟨17858970965901699923426477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11905980643934466615617651 17858970965901699923426477)
                ·
                  refine ⟨6697114112213137471284929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17858970965901699923426477 6697114112213137471284929)
                  ·
                    refine ⟨5022835584159853103463697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6697114112213137471284929 5022835584159853103463697)
                    ·
                      refine ⟨3767126688119889827597773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5022835584159853103463697 3767126688119889827597773)
                      ·
                        rfl

theorem cell23_7336453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 3, 2, 2].length) (baseStart_7336453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336453 prefixEnd_7336453 := by exact prefixLift 7336453
  have htrace : WordTrace (prefixWord ++ tailWord_7336453) baseStart_7336453 baseEnd_7336453 := by
    simpa [prefixWord, tailWord_7336453, baseEnd_7336453] using wordTrace_append hprefix tailTrace_7336453
  have hstable : (prefixWord ++ tailWord_7336453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336453).length < 2 ^ (prefixWord ++ tailWord_7336453).sum := by decide
  have hdescent : baseEnd_7336453 < baseStart_7336453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336459 : List Nat := [1, 1, 1, 1, 7, 2, 2, 8]
def baseStart_7336459 : Nat := 118140960795 + 7336459 * 2 ^ 59
def prefixEnd_7336459 : Nat := 4983230072969 + 3 ^ 40 * 7336459 * 2
def baseEnd_7336459 : Nat := 139523324777919140893435

theorem tailTrace_7336459 : CollatzResearch.WordTrace tailWord_7336459 prefixEnd_7336459 139523324777919140893435 := by
  unfold tailWord_7336459
  simp only [CollatzResearch.WordTrace]
  refine ⟨267582642528269485288476431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178388428352179656858984287 267582642528269485288476431)
  ·
    refine ⟨401373963792404227932714647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267582642528269485288476431 401373963792404227932714647)
    ·
      refine ⟨602060945688606341899071971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401373963792404227932714647 602060945688606341899071971)
      ·
        refine ⟨903091418532909512848607957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602060945688606341899071971 903091418532909512848607957)
        ·
          refine ⟨21166205121865066707389249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 903091418532909512848607957 21166205121865066707389249)
          ·
            refine ⟨15874653841398800030541937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21166205121865066707389249 15874653841398800030541937)
            ·
              refine ⟨11905990381049100022906453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15874653841398800030541937 11905990381049100022906453)
              ·
                refine ⟨139523324777919140893435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11905990381049100022906453 139523324777919140893435)
                ·
                  rfl

theorem cell23_7336459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 2, 8].length) (baseStart_7336459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336459 prefixEnd_7336459 := by exact prefixLift 7336459
  have htrace : WordTrace (prefixWord ++ tailWord_7336459) baseStart_7336459 baseEnd_7336459 := by
    simpa [prefixWord, tailWord_7336459, baseEnd_7336459] using wordTrace_append hprefix tailTrace_7336459
  have hstable : (prefixWord ++ tailWord_7336459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336459).length < 2 ^ (prefixWord ++ tailWord_7336459).sum := by decide
  have hdescent : baseEnd_7336459 < baseStart_7336459 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336487 : List Nat := [1, 1, 7, 2, 1, 1, 3, 1, 1, 1, 4]
def baseStart_7336487 : Nat := 118140960795 + 7336487 * 2 ^ 59
def prefixEnd_7336487 : Nat := 4983230072969 + 3 ^ 40 * 7336487 * 2
def baseEnd_7336487 : Nat := 3767144146462142694572617

theorem tailTrace_7336487 : CollatzResearch.WordTrace tailWord_7336487 prefixEnd_7336487 3767144146462142694572617 := by
  unfold tailWord_7336487
  simp only [CollatzResearch.WordTrace]
  refine ⟨267583663772168046070495715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178389109181445364046997143 267583663772168046070495715)
  ·
    refine ⟨401375495658252069105743573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267583663772168046070495715 401375495658252069105743573)
    ·
      refine ⟨9407238179490282869665865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 401375495658252069105743573 9407238179490282869665865)
      ·
        refine ⟨7055428634617712152249399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9407238179490282869665865 7055428634617712152249399)
        ·
          refine ⟨10583142951926568228374099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7055428634617712152249399 10583142951926568228374099)
          ·
            refine ⟨15874714427889852342561149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10583142951926568228374099 15874714427889852342561149)
            ·
              refine ⟨5953017910458694628460431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15874714427889852342561149 5953017910458694628460431)
              ·
                refine ⟨8929526865688041942690647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5953017910458694628460431 8929526865688041942690647)
                ·
                  refine ⟨13394290298532062914035971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8929526865688041942690647 13394290298532062914035971)
                  ·
                    refine ⟨20091435447798094371053957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13394290298532062914035971 20091435447798094371053957)
                    ·
                      refine ⟨3767144146462142694572617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20091435447798094371053957 3767144146462142694572617)
                      ·
                        rfl

theorem cell23_7336487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_7336487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336487 prefixEnd_7336487 := by exact prefixLift 7336487
  have htrace : WordTrace (prefixWord ++ tailWord_7336487) baseStart_7336487 baseEnd_7336487 := by
    simpa [prefixWord, tailWord_7336487, baseEnd_7336487] using wordTrace_append hprefix tailTrace_7336487
  have hstable : (prefixWord ++ tailWord_7336487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336487).length < 2 ^ (prefixWord ++ tailWord_7336487).sum := by decide
  have hdescent : baseEnd_7336487 < baseStart_7336487 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336490 : List Nat := [3, 1, 4, 1, 1, 3, 3, 1, 1, 2, 3]
def baseStart_7336490 : Nat := 118140960795 + 7336490 * 2 ^ 59
def prefixEnd_7336490 : Nat := 4983230072969 + 3 ^ 40 * 7336490 * 2
def baseEnd_7336490 : Nat := 3767145686904106182835103

theorem tailTrace_7336490 : CollatzResearch.WordTrace tailWord_7336490 prefixEnd_7336490 3767145686904106182835103 := by
  unfold tailWord_7336490
  simp only [CollatzResearch.WordTrace]
  refine ⟨66895943297789294395713731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178389182127438118388569949 66895943297789294395713731)
  ·
    refine ⟨100343914946683941593570597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66895943297789294395713731 100343914946683941593570597)
    ·
      refine ⟨18814484052503239048794487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100343914946683941593570597 18814484052503239048794487)
      ·
        refine ⟨28221726078754858573191731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18814484052503239048794487 28221726078754858573191731)
        ·
          refine ⟨42332589118132287859787597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28221726078754858573191731 42332589118132287859787597)
          ·
            refine ⟨15874720919299607947420349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42332589118132287859787597 15874720919299607947420349)
            ·
              refine ⟨5953020344737352980282631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15874720919299607947420349 5953020344737352980282631)
              ·
                refine ⟨8929530517106029470423947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5953020344737352980282631 8929530517106029470423947)
                ·
                  refine ⟨13394295775659044205635921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8929530517106029470423947 13394295775659044205635921)
                  ·
                    refine ⟨10045721831744283154226941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13394295775659044205635921 10045721831744283154226941)
                    ·
                      refine ⟨3767145686904106182835103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10045721831744283154226941 3767145686904106182835103)
                      ·
                        rfl

theorem cell23_7336490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_7336490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336490 prefixEnd_7336490 := by exact prefixLift 7336490
  have htrace : WordTrace (prefixWord ++ tailWord_7336490) baseStart_7336490 baseEnd_7336490 := by
    simpa [prefixWord, tailWord_7336490, baseEnd_7336490] using wordTrace_append hprefix tailTrace_7336490
  have hstable : (prefixWord ++ tailWord_7336490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336490).length < 2 ^ (prefixWord ++ tailWord_7336490).sum := by decide
  have hdescent : baseEnd_7336490 < baseStart_7336490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336493 : List Nat := [1, 5, 4, 1, 1, 11]
def baseStart_7336493 : Nat := 118140960795 + 7336493 * 2 ^ 59
def prefixEnd_7336493 : Nat := 4983230072969 + 3 ^ 40 * 7336493 * 2
def baseEnd_7336493 : Nat := 15502663487020862844023

theorem tailTrace_7336493 : CollatzResearch.WordTrace tailWord_7336493 prefixEnd_7336493 15502663487020862844023 := by
  unfold tailWord_7336493
  simp only [CollatzResearch.WordTrace]
  refine ⟨267583882610146309095214133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178389255073430872730142755 267583882610146309095214133)
  ·
    refine ⟨25085988994701216477676325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267583882610146309095214133 25085988994701216477676325)
    ·
      refine ⟨4703622936506478089564311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25085988994701216477676325 4703622936506478089564311)
      ·
        refine ⟨7055434404759717134346467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4703622936506478089564311 7055434404759717134346467)
        ·
          refine ⟨10583151607139575701519701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7055434404759717134346467 10583151607139575701519701)
          ·
            refine ⟨15502663487020862844023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10583151607139575701519701 15502663487020862844023)
            ·
              rfl

theorem cell23_7336493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 11].length) (baseStart_7336493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336493 prefixEnd_7336493 := by exact prefixLift 7336493
  have htrace : WordTrace (prefixWord ++ tailWord_7336493) baseStart_7336493 baseEnd_7336493 := by
    simpa [prefixWord, tailWord_7336493, baseEnd_7336493] using wordTrace_append hprefix tailTrace_7336493
  have hstable : (prefixWord ++ tailWord_7336493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336493).length < 2 ^ (prefixWord ++ tailWord_7336493).sum := by decide
  have hdescent : baseEnd_7336493 < baseStart_7336493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336503 : List Nat := [1, 1, 3, 1, 2, 3, 4, 2, 2, 1, 3]
def baseStart_7336503 : Nat := 118140960795 + 7336503 * 2 ^ 59
def prefixEnd_7336503 : Nat := 4983230072969 + 3 ^ 40 * 7336503 * 2
def baseEnd_7336503 : Nat := 3767152362152614631972543

theorem tailTrace_7336503 : CollatzResearch.WordTrace tailWord_7336503 prefixEnd_7336503 3767152362152614631972543 := by
  unfold tailWord_7336503
  simp only [CollatzResearch.WordTrace]
  refine ⟨267584247340110080803078163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178389498226740053868718775 267584247340110080803078163)
  ·
    refine ⟨401376371010165121204617245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267584247340110080803078163 401376371010165121204617245)
    ·
      refine ⟨150516139128811920451731467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401376371010165121204617245 150516139128811920451731467)
      ·
        refine ⟨225774208693217880677597201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150516139128811920451731467 225774208693217880677597201)
        ·
          refine ⟨169330656519913410508197901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225774208693217880677597201 169330656519913410508197901)
          ·
            refine ⟨63498996194967528940574213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169330656519913410508197901 63498996194967528940574213)
            ·
              refine ⟨11906061786556411676357665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63498996194967528940574213 11906061786556411676357665)
              ·
                refine ⟨8929546339917308757268249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11906061786556411676357665 8929546339917308757268249)
                ·
                  refine ⟨6697159754937981567951187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8929546339917308757268249 6697159754937981567951187)
                  ·
                    refine ⟨10045739632406972351926781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6697159754937981567951187 10045739632406972351926781)
                    ·
                      refine ⟨3767152362152614631972543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10045739632406972351926781 3767152362152614631972543)
                      ·
                        rfl

theorem cell23_7336503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_7336503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336503 prefixEnd_7336503 := by exact prefixLift 7336503
  have htrace : WordTrace (prefixWord ++ tailWord_7336503) baseStart_7336503 baseEnd_7336503 := by
    simpa [prefixWord, tailWord_7336503, baseEnd_7336503] using wordTrace_append hprefix tailTrace_7336503
  have hstable : (prefixWord ++ tailWord_7336503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336503).length < 2 ^ (prefixWord ++ tailWord_7336503).sum := by decide
  have hdescent : baseEnd_7336503 < baseStart_7336503 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336510 : List Nat := [4, 2, 1, 4, 2, 1, 1, 8]
def baseStart_7336510 : Nat := 118140960795 + 7336510 * 2 ^ 59
def prefixEnd_7336510 : Nat := 4983230072969 + 3 ^ 40 * 7336510 * 2
def baseEnd_7336510 : Nat := 139524294685822077947593

theorem tailTrace_7336510 : CollatzResearch.WordTrace tailWord_7336510 prefixEnd_7336510 139524294685822077947593 := by
  unfold tailWord_7336510
  simp only [CollatzResearch.WordTrace]
  refine ⟨33448062831385590124822873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178389668434056480665721989 33448062831385590124822873)
  ·
    refine ⟨25086047123539192593617155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33448062831385590124822873 25086047123539192593617155)
    ·
      refine ⟨37629070685308788890425733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25086047123539192593617155 37629070685308788890425733)
      ·
        refine ⟨7055450753495397916954825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37629070685308788890425733 7055450753495397916954825)
        ·
          refine ⟨5291588065121548437716119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7055450753495397916954825 5291588065121548437716119)
          ·
            refine ⟨7937382097682322656574179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5291588065121548437716119 7937382097682322656574179)
            ·
              refine ⟨11906073146523483984861269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7937382097682322656574179 11906073146523483984861269)
              ·
                refine ⟨139524294685822077947593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11906073146523483984861269 139524294685822077947593)
                ·
                  rfl

theorem cell23_7336510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 2, 1, 1, 8].length) (baseStart_7336510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336510 prefixEnd_7336510 := by exact prefixLift 7336510
  have htrace : WordTrace (prefixWord ++ tailWord_7336510) baseStart_7336510 baseEnd_7336510 := by
    simpa [prefixWord, tailWord_7336510, baseEnd_7336510] using wordTrace_append hprefix tailTrace_7336510
  have hstable : (prefixWord ++ tailWord_7336510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336510).length < 2 ^ (prefixWord ++ tailWord_7336510).sum := by decide
  have hdescent : baseEnd_7336510 < baseStart_7336510 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336513 : List Nat := [1, 2, 5, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_7336513 : Nat := 118140960795 + 7336513 * 2 ^ 59
def prefixEnd_7336513 : Nat := 4983230072969 + 3 ^ 40 * 7336513 * 2
def baseEnd_7336513 : Nat := 3767157496959159592847497

theorem tailTrace_7336513 : CollatzResearch.WordTrace tailWord_7336513 prefixEnd_7336513 3767157496959159592847497 := by
  unfold tailWord_7336513
  simp only [CollatzResearch.WordTrace]
  refine ⟨267584612070073852510942193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178389741380049235007294795 267584612070073852510942193)
  ·
    refine ⟨200688459052555389383206645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267584612070073852510942193 200688459052555389383206645)
    ·
      refine ⟨18814543036177067754675623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200688459052555389383206645 18814543036177067754675623)
      ·
        refine ⟨28221814554265601632013435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18814543036177067754675623 28221814554265601632013435)
        ·
          refine ⟨42332721831398402448020153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28221814554265601632013435 42332721831398402448020153)
          ·
            refine ⟨31749541373548801836015115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42332721831398402448020153 31749541373548801836015115)
            ·
              refine ⟨47624312060323202754022673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31749541373548801836015115 47624312060323202754022673)
              ·
                refine ⟨35718234045242402065517005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47624312060323202754022673 35718234045242402065517005)
                ·
                  refine ⟨13394337766965900774568877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35718234045242402065517005 13394337766965900774568877)
                  ·
                    refine ⟨5022876662612212790463329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13394337766965900774568877 5022876662612212790463329)
                    ·
                      refine ⟨3767157496959159592847497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5022876662612212790463329 3767157496959159592847497)
                      ·
                        rfl

theorem cell23_7336513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_7336513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336513 prefixEnd_7336513 := by exact prefixLift 7336513
  have htrace : WordTrace (prefixWord ++ tailWord_7336513) baseStart_7336513 baseEnd_7336513 := by
    simpa [prefixWord, tailWord_7336513, baseEnd_7336513] using wordTrace_append hprefix tailTrace_7336513
  have hstable : (prefixWord ++ tailWord_7336513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336513).length < 2 ^ (prefixWord ++ tailWord_7336513).sum := by decide
  have hdescent : baseEnd_7336513 < baseStart_7336513 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336519 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 1, 8]
def baseStart_7336519 : Nat := 118140960795 + 7336519 * 2 ^ 59
def prefixEnd_7336519 : Nat := 4983230072969 + 3 ^ 40 * 7336519 * 2
def baseEnd_7336519 : Nat := 1255720192614362189790823

theorem tailTrace_7336519 : CollatzResearch.WordTrace tailWord_7336519 prefixEnd_7336519 1255720192614362189790823 := by
  unfold tailWord_7336519
  simp only [CollatzResearch.WordTrace]
  refine ⟨267584830908052115535660611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178389887272034743690440407 267584830908052115535660611)
  ·
    refine ⟨401377246362078173303490917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267584830908052115535660611 401377246362078173303490917)
    ·
      refine ⟨75258233692889657494404547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401377246362078173303490917 75258233692889657494404547)
      ·
        refine ⟨112887350539334486241606821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75258233692889657494404547 112887350539334486241606821)
        ·
          refine ⟨21166378226125216170301279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112887350539334486241606821 21166378226125216170301279)
          ·
            refine ⟨31749567339187824255451919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21166378226125216170301279 31749567339187824255451919)
            ·
              refine ⟨47624351008781736383177879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31749567339187824255451919 47624351008781736383177879)
              ·
                refine ⟨71436526513172604574766819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47624351008781736383177879 71436526513172604574766819)
                ·
                  refine ⟨107154789769758906862150229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71436526513172604574766819 107154789769758906862150229)
                  ·
                    refine ⟨1255720192614362189790823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107154789769758906862150229 1255720192614362189790823)
                    ·
                      rfl

theorem cell23_7336519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_7336519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336519 prefixEnd_7336519 := by exact prefixLift 7336519
  have htrace : WordTrace (prefixWord ++ tailWord_7336519) baseStart_7336519 baseEnd_7336519 := by
    simpa [prefixWord, tailWord_7336519, baseEnd_7336519] using wordTrace_append hprefix tailTrace_7336519
  have hstable : (prefixWord ++ tailWord_7336519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336519).length < 2 ^ (prefixWord ++ tailWord_7336519).sum := by decide
  have hdescent : baseEnd_7336519 < baseStart_7336519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336560 : List Nat := [2, 1, 1, 1, 7, 1, 1, 1, 4, 2, 2]
def baseStart_7336560 : Nat := 118140960795 + 7336560 * 2 ^ 59
def prefixEnd_7336560 : Nat := 4983230072969 + 3 ^ 40 * 7336560 * 2
def baseEnd_7336560 : Nat := 3767181630549920908959781

theorem tailTrace_7336560 : CollatzResearch.WordTrace tailWord_7336560 prefixEnd_7336560 3767181630549920908959781 := by
  unfold tailWord_7336560
  simp only [CollatzResearch.WordTrace]
  refine ⟨133793163150451789768951567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178390884200602386358602089 133793163150451789768951567)
  ·
    refine ⟨200689744725677684653427351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133793163150451789768951567 200689744725677684653427351)
    ·
      refine ⟨301034617088516526980141027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200689744725677684653427351 301034617088516526980141027)
      ·
        refine ⟨451551925632774790470211541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301034617088516526980141027 451551925632774790470211541)
        ·
          refine ⟨10583248257018159151645583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 451551925632774790470211541 10583248257018159151645583)
          ·
            refine ⟨15874872385527238727468375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10583248257018159151645583 15874872385527238727468375)
            ·
              refine ⟨23812308578290858091202563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15874872385527238727468375 23812308578290858091202563)
              ·
                refine ⟨35718462867436287136803845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23812308578290858091202563 35718462867436287136803845)
                ·
                  refine ⟨6697211787644303838150721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35718462867436287136803845 6697211787644303838150721)
                  ·
                    refine ⟨5022908840733227878613041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6697211787644303838150721 5022908840733227878613041)
                    ·
                      refine ⟨3767181630549920908959781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5022908840733227878613041 3767181630549920908959781)
                      ·
                        rfl

theorem cell23_7336560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 1, 4, 2, 2].length) (baseStart_7336560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336560 prefixEnd_7336560 := by exact prefixLift 7336560
  have htrace : WordTrace (prefixWord ++ tailWord_7336560) baseStart_7336560 baseEnd_7336560 := by
    simpa [prefixWord, tailWord_7336560, baseEnd_7336560] using wordTrace_append hprefix tailTrace_7336560
  have hstable : (prefixWord ++ tailWord_7336560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336560).length < 2 ^ (prefixWord ++ tailWord_7336560).sum := by decide
  have hdescent : baseEnd_7336560 < baseStart_7336560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336576 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 3]
def baseStart_7336576 : Nat := 118140960795 + 7336576 * 2 ^ 59
def prefixEnd_7336576 : Nat := 4983230072969 + 3 ^ 40 * 7336576 * 2
def baseEnd_7336576 : Nat := 3767189846240392846359707

theorem tailTrace_7336576 : CollatzResearch.WordTrace tailWord_7336576 prefixEnd_7336576 3767189846240392846359707 := by
  unfold tailWord_7336576
  simp only [CollatzResearch.WordTrace]
  refine ⟨133793454934422807135242791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178391273245897076180323721 133793454934422807135242791)
  ·
    refine ⟨200690182401634210702864187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133793454934422807135242791 200690182401634210702864187)
    ·
      refine ⟨301035273602451316054296281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200690182401634210702864187 301035273602451316054296281)
      ·
        refine ⟨225776455201838487040722211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301035273602451316054296281 225776455201838487040722211)
        ·
          refine ⟨338664682802757730561083317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225776455201838487040722211 338664682802757730561083317)
          ·
            refine ⟨31749814012758537240101561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 338664682802757730561083317 31749814012758537240101561)
            ·
              refine ⟨23812360509568902930076171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31749814012758537240101561 23812360509568902930076171)
              ·
                refine ⟨35718540764353354395114257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23812360509568902930076171 35718540764353354395114257)
                ·
                  refine ⟨26788905573265015796335693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35718540764353354395114257 26788905573265015796335693)
                  ·
                    refine ⟨10045839589974380923625885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26788905573265015796335693 10045839589974380923625885)
                    ·
                      refine ⟨3767189846240392846359707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10045839589974380923625885 3767189846240392846359707)
                      ·
                        rfl

theorem cell23_7336576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_7336576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336576 prefixEnd_7336576 := by exact prefixLift 7336576
  have htrace : WordTrace (prefixWord ++ tailWord_7336576) baseStart_7336576 baseEnd_7336576 := by
    simpa [prefixWord, tailWord_7336576, baseEnd_7336576] using wordTrace_append hprefix tailTrace_7336576
  have hstable : (prefixWord ++ tailWord_7336576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336576).length < 2 ^ (prefixWord ++ tailWord_7336576).sum := by decide
  have hdescent : baseEnd_7336576 < baseStart_7336576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336577 : List Nat := [1, 2, 4, 2, 1, 1, 5, 1, 2, 2, 2]
def baseStart_7336577 : Nat := 118140960795 + 7336577 * 2 ^ 59
def prefixEnd_7336577 : Nat := 4983230072969 + 3 ^ 40 * 7336577 * 2
def baseEnd_7336577 : Nat := 3767190359721047342447203

theorem tailTrace_7336577 : CollatzResearch.WordTrace tailWord_7336577 prefixEnd_7336577 3767190359721047342447203 := by
  unfold tailWord_7336577
  simp only [CollatzResearch.WordTrace]
  refine ⟨267586946341841991441271985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178391297561227994294181323 267586946341841991441271985)
  ·
    refine ⟨200690209756381493580953989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267586946341841991441271985 200690209756381493580953989)
    ·
      refine ⟨37629414329321530046428873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200690209756381493580953989 37629414329321530046428873)
      ·
        refine ⟨28222060746991147534821655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37629414329321530046428873 28222060746991147534821655)
        ·
          refine ⟨42333091120486721302232483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28222060746991147534821655 42333091120486721302232483)
          ·
            refine ⟨63499636680730081953348725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42333091120486721302232483 63499636680730081953348725)
            ·
              refine ⟨5953090938818445183126443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63499636680730081953348725 5953090938818445183126443)
              ·
                refine ⟨8929636408227667774689665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5953090938818445183126443 8929636408227667774689665)
                ·
                  refine ⟨6697227306170750831017249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8929636408227667774689665 6697227306170750831017249)
                  ·
                    refine ⟨5022920479628063123262937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6697227306170750831017249 5022920479628063123262937)
                    ·
                      refine ⟨3767190359721047342447203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5022920479628063123262937 3767190359721047342447203)
                      ·
                        rfl

theorem cell23_7336577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_7336577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336577 prefixEnd_7336577 := by exact prefixLift 7336577
  have htrace : WordTrace (prefixWord ++ tailWord_7336577) baseStart_7336577 baseEnd_7336577 := by
    simpa [prefixWord, tailWord_7336577, baseEnd_7336577] using wordTrace_append hprefix tailTrace_7336577
  have hstable : (prefixWord ++ tailWord_7336577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336577).length < 2 ^ (prefixWord ++ tailWord_7336577).sum := by decide
  have hdescent : baseEnd_7336577 < baseStart_7336577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336579 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 1, 7]
def baseStart_7336579 : Nat := 118140960795 + 7336579 * 2 ^ 59
def prefixEnd_7336579 : Nat := 4983230072969 + 3 ^ 40 * 7336579 * 2
def baseEnd_7336579 : Nat := 1255730462227452111540731

theorem tailTrace_7336579 : CollatzResearch.WordTrace tailWord_7336579 prefixEnd_7336579 1255730462227452111540731 := by
  unfold tailWord_7336579
  simp only [CollatzResearch.WordTrace]
  refine ⟨267587019287834745782844791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178391346191889830521896527 267587019287834745782844791)
  ·
    refine ⟨401380528931752118674267187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267587019287834745782844791 401380528931752118674267187)
    ·
      refine ⟨602070793397628178011400781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401380528931752118674267187 602070793397628178011400781)
      ·
        refine ⟨225776547524110566754275293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 602070793397628178011400781 225776547524110566754275293)
        ·
          refine ⟨84666205321541462532853235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225776547524110566754275293 84666205321541462532853235)
          ·
            refine ⟨126999307982312193799279853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84666205321541462532853235 126999307982312193799279853)
            ·
              refine ⟨47624740493367072674729945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126999307982312193799279853 47624740493367072674729945)
              ·
                refine ⟨35718555370025304506047459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47624740493367072674729945 35718555370025304506047459)
                ·
                  refine ⟨53577833055037956759071189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35718555370025304506047459 53577833055037956759071189)
                  ·
                    refine ⟨1255730462227452111540731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53577833055037956759071189 1255730462227452111540731)
                    ·
                      rfl

theorem cell23_7336579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 7].length) (baseStart_7336579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336579 prefixEnd_7336579 := by exact prefixLift 7336579
  have htrace : WordTrace (prefixWord ++ tailWord_7336579) baseStart_7336579 baseEnd_7336579 := by
    simpa [prefixWord, tailWord_7336579, baseEnd_7336579] using wordTrace_append hprefix tailTrace_7336579
  have hstable : (prefixWord ++ tailWord_7336579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336579).length < 2 ^ (prefixWord ++ tailWord_7336579).sum := by decide
  have hdescent : baseEnd_7336579 < baseStart_7336579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336673 : List Nat := [1, 2, 3, 1, 4, 2, 2, 2, 6]
def baseStart_7336673 : Nat := 118140960795 + 7336673 * 2 ^ 59
def prefixEnd_7336673 : Nat := 4983230072969 + 3 ^ 40 * 7336673 * 2
def baseEnd_7336673 : Nat := 418582183762653218538529

theorem tailTrace_7336673 : CollatzResearch.WordTrace tailWord_7336673 prefixEnd_7336673 418582183762653218538529 := by
  unfold tailWord_7336673
  simp only [CollatzResearch.WordTrace]
  refine ⟨267590447749494199836766673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178393631832996133224511115 267590447749494199836766673)
  ·
    refine ⟨200692835812120649877575005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267590447749494199836766673 200692835812120649877575005)
    ·
      refine ⟨75259813429545243704090627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200692835812120649877575005 75259813429545243704090627)
      ·
        refine ⟨112889720144317865556135941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75259813429545243704090627 112889720144317865556135941)
        ·
          refine ⟨21166822527059599791775489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112889720144317865556135941 21166822527059599791775489)
          ·
            refine ⟨15875116895294699843831617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21166822527059599791775489 15875116895294699843831617)
            ·
              refine ⟨11906337671471024882873713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15875116895294699843831617 11906337671471024882873713)
              ·
                refine ⟨8929753253603268662155285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11906337671471024882873713 8929753253603268662155285)
                ·
                  refine ⟨418582183762653218538529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8929753253603268662155285 418582183762653218538529)
                  ·
                    rfl

theorem cell23_7336673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 6].length) (baseStart_7336673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336673 prefixEnd_7336673 := by exact prefixLift 7336673
  have htrace : WordTrace (prefixWord ++ tailWord_7336673) baseStart_7336673 baseEnd_7336673 := by
    simpa [prefixWord, tailWord_7336673, baseEnd_7336673] using wordTrace_append hprefix tailTrace_7336673
  have hstable : (prefixWord ++ tailWord_7336673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336673).length < 2 ^ (prefixWord ++ tailWord_7336673).sum := by decide
  have hdescent : baseEnd_7336673 < baseStart_7336673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336677 : List Nat := [1, 3, 1, 4, 1, 2, 4, 2, 1, 4]
def baseStart_7336677 : Nat := 118140960795 + 7336677 * 2 ^ 59
def prefixEnd_7336677 : Nat := 4983230072969 + 3 ^ 40 * 7336677 * 2
def baseEnd_7336677 : Nat := 1255747235928832317065581

theorem tailTrace_7336677 : CollatzResearch.WordTrace tailWord_7336677 prefixEnd_7336677 1255747235928832317065581 := by
  unfold tailWord_7336677
  simp only [CollatzResearch.WordTrace]
  refine ⟨267590593641479708519912285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178393729094319805679941523 267590593641479708519912285)
  ·
    refine ⟨100346472615554890694967107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267590593641479708519912285 100346472615554890694967107)
    ·
      refine ⟨150519708923332336042450661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100346472615554890694967107 150519708923332336042450661)
      ·
        refine ⟨28222445423124813007959499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150519708923332336042450661 28222445423124813007959499)
        ·
          refine ⟨42333668134687219511939249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28222445423124813007959499 42333668134687219511939249)
          ·
            refine ⟨31750251101015414633954437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42333668134687219511939249 31750251101015414633954437)
            ·
              refine ⟨5953172081440390243866457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31750251101015414633954437 5953172081440390243866457)
              ·
                refine ⟨4464879061080292682899843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5953172081440390243866457 4464879061080292682899843)
                ·
                  refine ⟨6697318591620439024349765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4464879061080292682899843 6697318591620439024349765)
                  ·
                    refine ⟨1255747235928832317065581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6697318591620439024349765 1255747235928832317065581)
                    ·
                      rfl

theorem cell23_7336677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 1, 4].length) (baseStart_7336677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336677 prefixEnd_7336677 := by exact prefixLift 7336677
  have htrace : WordTrace (prefixWord ++ tailWord_7336677) baseStart_7336677 baseEnd_7336677 := by
    simpa [prefixWord, tailWord_7336677, baseEnd_7336677] using wordTrace_append hprefix tailTrace_7336677
  have hstable : (prefixWord ++ tailWord_7336677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336677).length < 2 ^ (prefixWord ++ tailWord_7336677).sum := by decide
  have hdescent : baseEnd_7336677 < baseStart_7336677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336683 : List Nat := [1, 1, 1, 1, 2, 4, 1, 5, 3, 1, 3]
def baseStart_7336683 : Nat := 118140960795 + 7336683 * 2 ^ 59
def prefixEnd_7336683 : Nat := 4983230072969 + 3 ^ 40 * 7336683 * 2
def baseEnd_7336683 : Nat := 3767244788670423927721715

theorem tailTrace_7336683 : CollatzResearch.WordTrace tailWord_7336683 prefixEnd_7336683 3767244788670423927721715 := by
  unfold tailWord_7336683
  simp only [CollatzResearch.WordTrace]
  refine ⟨267590812479457971544630703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178393874986305314363087135 267590812479457971544630703)
  ·
    refine ⟨401386218719186957316946055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267590812479457971544630703 401386218719186957316946055)
    ·
      refine ⟨602079328078780435975419083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401386218719186957316946055 602079328078780435975419083)
      ·
        refine ⟨903118992118170653963128625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602079328078780435975419083 903118992118170653963128625)
        ·
          refine ⟨677339244088627990472346469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903118992118170653963128625 677339244088627990472346469)
          ·
            refine ⟨127001108266617748213564963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 677339244088627990472346469 127001108266617748213564963)
            ·
              refine ⟨190501662399926622320347445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127001108266617748213564963 190501662399926622320347445)
              ·
                refine ⟨17859530849993120842532573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190501662399926622320347445 17859530849993120842532573)
                ·
                  refine ⟨6697324068747420315949715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17859530849993120842532573 6697324068747420315949715)
                  ·
                    refine ⟨10045986103121130473924573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6697324068747420315949715 10045986103121130473924573)
                    ·
                      refine ⟨3767244788670423927721715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10045986103121130473924573 3767244788670423927721715)
                      ·
                        rfl

theorem cell23_7336683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 1, 3].length) (baseStart_7336683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336683 prefixEnd_7336683 := by exact prefixLift 7336683
  have htrace : WordTrace (prefixWord ++ tailWord_7336683) baseStart_7336683 baseEnd_7336683 := by
    simpa [prefixWord, tailWord_7336683, baseEnd_7336683] using wordTrace_append hprefix tailTrace_7336683
  have hstable : (prefixWord ++ tailWord_7336683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336683).length < 2 ^ (prefixWord ++ tailWord_7336683).sum := by decide
  have hdescent : baseEnd_7336683 < baseStart_7336683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336700 : List Nat := [2, 2, 2, 1, 3, 3, 1, 2, 3, 1, 3]
def baseStart_7336700 : Nat := 118140960795 + 7336700 * 2 ^ 59
def prefixEnd_7336700 : Nat := 4983230072969 + 3 ^ 40 * 7336700 * 2
def baseEnd_7336700 : Nat := 3767253517841550361209137

theorem tailTrace_7336700 : CollatzResearch.WordTrace tailWord_7336700 prefixEnd_7336700 3767253517841550361209137 := by
  unfold tailWord_7336700
  simp only [CollatzResearch.WordTrace]
  refine ⟨133795716260198191723999777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178394288346930922298666369 133795716260198191723999777)
  ·
    refine ⟨100346787195148643792999833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133795716260198191723999777 100346787195148643792999833)
    ·
      refine ⟨75260090396361482844749875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100346787195148643792999833 75260090396361482844749875)
      ·
        refine ⟨112890135594542224267124813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75260090396361482844749875 112890135594542224267124813)
        ·
          refine ⟨42333800847953334100171805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112890135594542224267124813 42333800847953334100171805)
          ·
            refine ⟨15875175317982500287564427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42333800847953334100171805 15875175317982500287564427)
            ·
              refine ⟨23812762976973750431346641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15875175317982500287564427 23812762976973750431346641)
              ·
                refine ⟨17859572232730312823509981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23812762976973750431346641 17859572232730312823509981)
                ·
                  refine ⟨6697339587273867308816243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17859572232730312823509981 6697339587273867308816243)
                  ·
                    refine ⟨10046009380910800963224365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6697339587273867308816243 10046009380910800963224365)
                    ·
                      refine ⟨3767253517841550361209137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10046009380910800963224365 3767253517841550361209137)
                      ·
                        rfl

theorem cell23_7336700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 2, 3, 1, 3].length) (baseStart_7336700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336700 prefixEnd_7336700 := by exact prefixLift 7336700
  have htrace : WordTrace (prefixWord ++ tailWord_7336700) baseStart_7336700 baseEnd_7336700 := by
    simpa [prefixWord, tailWord_7336700, baseEnd_7336700] using wordTrace_append hprefix tailTrace_7336700
  have hstable : (prefixWord ++ tailWord_7336700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336700).length < 2 ^ (prefixWord ++ tailWord_7336700).sum := by decide
  have hdescent : baseEnd_7336700 < baseStart_7336700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336723 : List Nat := [1, 1, 1, 2, 1, 3, 5, 3, 1, 1, 4]
def baseStart_7336723 : Nat := 118140960795 + 7336723 * 2 ^ 59
def prefixEnd_7336723 : Nat := 4983230072969 + 3 ^ 40 * 7336723 * 2
def baseEnd_7336723 : Nat := 3767265327896603771221531

theorem tailTrace_7336723 : CollatzResearch.WordTrace tailWord_7336723 prefixEnd_7336723 3767265327896603771221531 := by
  unfold tailWord_7336723
  simp only [CollatzResearch.WordTrace]
  refine ⟨267592271399313058376086823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178394847599542038917391215 267592271399313058376086823)
  ·
    refine ⟨401388407098969587564130235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267592271399313058376086823 401388407098969587564130235)
    ·
      refine ⟨602082610648454381346195353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401388407098969587564130235 602082610648454381346195353)
      ·
        refine ⟨451561957986340786009646515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602082610648454381346195353 451561957986340786009646515)
        ·
          refine ⟨677342936979511179014469773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451561957986340786009646515 677342936979511179014469773)
          ·
            refine ⟨254003601367316692130426165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 677342936979511179014469773 254003601367316692130426165)
            ·
              refine ⟨23812837628185939887227453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 254003601367316692130426165 23812837628185939887227453)
              ·
                refine ⟨8929814110569727457710295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23812837628185939887227453 8929814110569727457710295)
                ·
                  refine ⟨13394721165854591186565443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8929814110569727457710295 13394721165854591186565443)
                  ·
                    refine ⟨20092081748781886779848165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13394721165854591186565443 20092081748781886779848165)
                    ·
                      refine ⟨3767265327896603771221531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20092081748781886779848165 3767265327896603771221531)
                      ·
                        rfl

theorem cell23_7336723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 1, 4].length) (baseStart_7336723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336723 prefixEnd_7336723 := by exact prefixLift 7336723
  have htrace : WordTrace (prefixWord ++ tailWord_7336723) baseStart_7336723 baseEnd_7336723 := by
    simpa [prefixWord, tailWord_7336723, baseEnd_7336723] using wordTrace_append hprefix tailTrace_7336723
  have hstable : (prefixWord ++ tailWord_7336723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336723).length < 2 ^ (prefixWord ++ tailWord_7336723).sum := by decide
  have hdescent : baseEnd_7336723 < baseStart_7336723 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336750 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 1, 6]
def baseStart_7336750 : Nat := 118140960795 + 7336750 * 2 ^ 59
def prefixEnd_7336750 : Nat := 4983230072969 + 3 ^ 40 * 7336750 * 2
def baseEnd_7336750 : Nat := 1255759730624758388527969

theorem tailTrace_7336750 : CollatzResearch.WordTrace tailWord_7336750 prefixEnd_7336750 1255759730624758388527969 := by
  unfold tailWord_7336750
  simp only [CollatzResearch.WordTrace]
  refine ⟨33449157021276905248414963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178395504113476827991546469 33449157021276905248414963)
  ·
    refine ⟨50173735531915357872622445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33449157021276905248414963 50173735531915357872622445)
    ·
      refine ⟨18815150824468259202233417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50173735531915357872622445 18815150824468259202233417)
      ·
        refine ⟨14111363118351194401675063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18815150824468259202233417 14111363118351194401675063)
        ·
          refine ⟨21167044677526791602512595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14111363118351194401675063 21167044677526791602512595)
          ·
            refine ⟨31750567016290187403768893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21167044677526791602512595 31750567016290187403768893)
            ·
              refine ⟨11906462631108820276413335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31750567016290187403768893 11906462631108820276413335)
              ·
                refine ⟨17859693946663230414620003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11906462631108820276413335 17859693946663230414620003)
                ·
                  refine ⟨26789540919994845621930005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17859693946663230414620003 26789540919994845621930005)
                  ·
                    refine ⟨1255759730624758388527969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26789540919994845621930005 1255759730624758388527969)
                    ·
                      rfl

theorem cell23_7336750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_7336750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336750 prefixEnd_7336750 := by exact prefixLift 7336750
  have htrace : WordTrace (prefixWord ++ tailWord_7336750) baseStart_7336750 baseEnd_7336750 := by
    simpa [prefixWord, tailWord_7336750, baseEnd_7336750] using wordTrace_append hprefix tailTrace_7336750
  have hstable : (prefixWord ++ tailWord_7336750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336750).length < 2 ^ (prefixWord ++ tailWord_7336750).sum := by decide
  have hdescent : baseEnd_7336750 < baseStart_7336750 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336757 : List Nat := [1, 3, 3, 1, 3, 1, 2, 2, 3, 2, 2]
def baseStart_7336757 : Nat := 118140960795 + 7336757 * 2 ^ 59
def prefixEnd_7336757 : Nat := 4983230072969 + 3 ^ 40 * 7336757 * 2
def baseEnd_7336757 : Nat := 3767282786238856638196375

theorem tailTrace_7336757 : CollatzResearch.WordTrace tailWord_7336757 prefixEnd_7336757 3767282786238856638196375 := by
  unfold tailWord_7336757
  simp only [CollatzResearch.WordTrace]
  refine ⟨267593511481189882182824525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178395674320793254788549683 267593511481189882182824525)
  ·
    refine ⟨100347566805446205818559197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267593511481189882182824525 100347566805446205818559197)
    ·
      refine ⟨37630337552042327181959699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100347566805446205818559197 37630337552042327181959699)
      ·
        refine ⟨56445506328063490772939549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37630337552042327181959699 56445506328063490772939549)
        ·
          refine ⟨21167064873023809039852331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56445506328063490772939549 21167064873023809039852331)
          ·
            refine ⟨31750597309535713559778497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21167064873023809039852331 31750597309535713559778497)
            ·
              refine ⟨23812947982151785169833873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31750597309535713559778497 23812947982151785169833873)
              ·
                refine ⟨17859710986613838877375405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23812947982151785169833873 17859710986613838877375405)
                ·
                  refine ⟨6697391619980189579015777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17859710986613838877375405 6697391619980189579015777)
                  ·
                    refine ⟨5023043714985142184261833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6697391619980189579015777 5023043714985142184261833)
                    ·
                      refine ⟨3767282786238856638196375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5023043714985142184261833 3767282786238856638196375)
                      ·
                        rfl

theorem cell23_7336757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_7336757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336757 prefixEnd_7336757 := by exact prefixLift 7336757
  have htrace : WordTrace (prefixWord ++ tailWord_7336757) baseStart_7336757 baseEnd_7336757 := by
    simpa [prefixWord, tailWord_7336757, baseEnd_7336757] using wordTrace_append hprefix tailTrace_7336757
  have hstable : (prefixWord ++ tailWord_7336757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336757).length < 2 ^ (prefixWord ++ tailWord_7336757).sum := by decide
  have hdescent : baseEnd_7336757 < baseStart_7336757 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336760 : List Nat := [2, 1, 2, 1, 3, 2, 4, 2, 1, 2, 3]
def baseStart_7336760 : Nat := 118140960795 + 7336760 * 2 ^ 59
def prefixEnd_7336760 : Nat := 4983230072969 + 3 ^ 40 * 7336760 * 2
def baseEnd_7336760 : Nat := 3767284326680820126458861

theorem tailTrace_7336760 : CollatzResearch.WordTrace tailWord_7336760 prefixEnd_7336760 3767284326680820126458861 := by
  unfold tailWord_7336760
  simp only [CollatzResearch.WordTrace]
  refine ⟨133796810450089506847591867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178395747266786009130122489 133796810450089506847591867)
  ·
    refine ⟨200695215675134260271387801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133796810450089506847591867 200695215675134260271387801)
    ·
      refine ⟨150521411756350695203540851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200695215675134260271387801 150521411756350695203540851)
      ·
        refine ⟨225782117634526042805311277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150521411756350695203540851 225782117634526042805311277)
        ·
          refine ⟨84668294112947266051991729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225782117634526042805311277 84668294112947266051991729)
          ·
            refine ⟨63501220584710449538993797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84668294112947266051991729 63501220584710449538993797)
            ·
              refine ⟨11906478859633209288561337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63501220584710449538993797 11906478859633209288561337)
              ·
                refine ⟨8929859144724906966421003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11906478859633209288561337 8929859144724906966421003)
                ·
                  refine ⟨13394788717087360449631505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8929859144724906966421003 13394788717087360449631505)
                  ·
                    refine ⟨10046091537815520337223629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13394788717087360449631505 10046091537815520337223629)
                    ·
                      refine ⟨3767284326680820126458861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10046091537815520337223629 3767284326680820126458861)
                      ·
                        rfl

theorem cell23_7336760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 4, 2, 1, 2, 3].length) (baseStart_7336760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336760 prefixEnd_7336760 := by exact prefixLift 7336760
  have htrace : WordTrace (prefixWord ++ tailWord_7336760) baseStart_7336760 baseEnd_7336760 := by
    simpa [prefixWord, tailWord_7336760, baseEnd_7336760] using wordTrace_append hprefix tailTrace_7336760
  have hstable : (prefixWord ++ tailWord_7336760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336760).length < 2 ^ (prefixWord ++ tailWord_7336760).sum := by decide
  have hdescent : baseEnd_7336760 < baseStart_7336760 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336791 : List Nat := [1, 1, 3, 2, 4, 2, 3, 2, 1, 2, 2]
def baseStart_7336791 : Nat := 118140960795 + 7336791 * 2 ^ 59
def prefixEnd_7336791 : Nat := 4983230072969 + 3 ^ 40 * 7336791 * 2
def baseEnd_7336791 : Nat := 3767300244581109505171219

theorem tailTrace_7336791 : CollatzResearch.WordTrace tailWord_7336791 prefixEnd_7336791 3767300244581109505171219 := by
  unfold tailWord_7336791
  simp only [CollatzResearch.WordTrace]
  refine ⟨267594751563066705989562227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178396501042044470659708151 267594751563066705989562227)
  ·
    refine ⟨401392127344600058984343341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267594751563066705989562227 401392127344600058984343341)
    ·
      refine ⟨150522047754225022119128753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401392127344600058984343341 150522047754225022119128753)
      ·
        refine ⟨112891535815668766589346565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150522047754225022119128753 112891535815668766589346565)
        ·
          refine ⟨21167162965437893735502481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112891535815668766589346565 21167162965437893735502481)
          ·
            refine ⟨15875372224078420301626861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21167162965437893735502481 15875372224078420301626861)
            ·
              refine ⟨5953264584029407613110073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15875372224078420301626861 5953264584029407613110073)
              ·
                refine ⟨4464948438022055709832555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5953264584029407613110073 4464948438022055709832555)
                ·
                  refine ⟨6697422657033083564748833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4464948438022055709832555 6697422657033083564748833)
                  ·
                    refine ⟨5023066992774812673561625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6697422657033083564748833 5023066992774812673561625)
                    ·
                      refine ⟨3767300244581109505171219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5023066992774812673561625 3767300244581109505171219)
                      ·
                        rfl

theorem cell23_7336791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 2, 1, 2, 2].length) (baseStart_7336791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336791 prefixEnd_7336791 := by exact prefixLift 7336791
  have htrace : WordTrace (prefixWord ++ tailWord_7336791) baseStart_7336791 baseEnd_7336791 := by
    simpa [prefixWord, tailWord_7336791, baseEnd_7336791] using wordTrace_append hprefix tailTrace_7336791
  have hstable : (prefixWord ++ tailWord_7336791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336791).length < 2 ^ (prefixWord ++ tailWord_7336791).sum := by decide
  have hdescent : baseEnd_7336791 < baseStart_7336791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336800 : List Nat := [2, 1, 1, 3, 3, 1, 2, 2, 3, 3, 2]
def baseStart_7336800 : Nat := 118140960795 + 7336800 * 2 ^ 59
def prefixEnd_7336800 : Nat := 4983230072969 + 3 ^ 40 * 7336800 * 2
def baseEnd_7336800 : Nat := 3767304865906999969958677

theorem tailTrace_7336800 : CollatzResearch.WordTrace tailWord_7336800 prefixEnd_7336800 3767304865906999969958677 := by
  unfold tailWord_7336800
  simp only [CollatzResearch.WordTrace]
  refine ⟨133797539910017050263319927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178396719880022733684426569 133797539910017050263319927)
  ·
    refine ⟨200696309865025575394979891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133797539910017050263319927 200696309865025575394979891)
    ·
      refine ⟨301044464797538363092469837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200696309865025575394979891 301044464797538363092469837)
      ·
        refine ⟨112891674299076886159676189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301044464797538363092469837 112891674299076886159676189)
        ·
          refine ⟨42334377862153832309878571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112891674299076886159676189 42334377862153832309878571)
          ·
            refine ⟨63501566793230748464817857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42334377862153832309878571 63501566793230748464817857)
            ·
              refine ⟨47626175094923061348613393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63501566793230748464817857 47626175094923061348613393)
              ·
                refine ⟨35719631321192296011460045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47626175094923061348613393 35719631321192296011460045)
                ·
                  refine ⟨13394861745447111004297517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35719631321192296011460045 13394861745447111004297517)
                  ·
                    refine ⟨5023073154542666626611569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13394861745447111004297517 5023073154542666626611569)
                    ·
                      refine ⟨3767304865906999969958677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5023073154542666626611569 3767304865906999969958677)
                      ·
                        rfl

theorem cell23_7336800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2, 3, 3, 2].length) (baseStart_7336800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336800 prefixEnd_7336800 := by exact prefixLift 7336800
  have htrace : WordTrace (prefixWord ++ tailWord_7336800) baseStart_7336800 baseEnd_7336800 := by
    simpa [prefixWord, tailWord_7336800, baseEnd_7336800] using wordTrace_append hprefix tailTrace_7336800
  have hstable : (prefixWord ++ tailWord_7336800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336800).length < 2 ^ (prefixWord ++ tailWord_7336800).sum := by decide
  have hdescent : baseEnd_7336800 < baseStart_7336800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336807 : List Nat := [1, 1, 5, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_7336807 : Nat := 118140960795 + 7336807 * 2 ^ 59
def prefixEnd_7336807 : Nat := 4983230072969 + 3 ^ 40 * 7336807 * 2
def baseEnd_7336807 : Nat := 3767308460271581442571145

theorem tailTrace_7336807 : CollatzResearch.WordTrace tailWord_7336807 prefixEnd_7336807 3767308460271581442571145 := by
  unfold tailWord_7336807
  simp only [CollatzResearch.WordTrace]
  refine ⟨267595335131008740722144675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178396890087339160481429783 267595335131008740722144675)
  ·
    refine ⟨401393002696513111083217013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267595335131008740722144675 401393002696513111083217013)
    ·
      refine ⟨37630594002798104164051595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 401393002696513111083217013 37630594002798104164051595)
      ·
        refine ⟨56445891004197156246077393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37630594002798104164051595 56445891004197156246077393)
        ·
          refine ⟨42334418253147867184558045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56445891004197156246077393 42334418253147867184558045)
          ·
            refine ⟨15875406844930450194209267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42334418253147867184558045 15875406844930450194209267)
            ·
              refine ⟨23813110267395675291313901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15875406844930450194209267 23813110267395675291313901)
              ·
                refine ⟨8929916350273378234242713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23813110267395675291313901 8929916350273378234242713)
                ·
                  refine ⟨6697437262705033675682035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8929916350273378234242713 6697437262705033675682035)
                  ·
                    refine ⟨10046155894057550513523053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6697437262705033675682035 10046155894057550513523053)
                    ·
                      refine ⟨3767308460271581442571145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10046155894057550513523053 3767308460271581442571145)
                      ·
                        rfl

theorem cell23_7336807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_7336807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336807 prefixEnd_7336807 := by exact prefixLift 7336807
  have htrace : WordTrace (prefixWord ++ tailWord_7336807) baseStart_7336807 baseEnd_7336807 := by
    simpa [prefixWord, tailWord_7336807, baseEnd_7336807] using wordTrace_append hprefix tailTrace_7336807
  have hstable : (prefixWord ++ tailWord_7336807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336807).length < 2 ^ (prefixWord ++ tailWord_7336807).sum := by decide
  have hdescent : baseEnd_7336807 < baseStart_7336807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336817 : List Nat := [1, 2, 2, 2, 1, 4, 3, 2, 1, 3, 2]
def baseStart_7336817 : Nat := 118140960795 + 7336817 * 2 ^ 59
def prefixEnd_7336817 : Nat := 4983230072969 + 3 ^ 40 * 7336817 * 2
def baseEnd_7336817 : Nat := 3767313595078126403446099

theorem tailTrace_7336817 : CollatzResearch.WordTrace tailWord_7336817 prefixEnd_7336817 3767313595078126403446099 := by
  unfold tailWord_7336817
  simp only [CollatzResearch.WordTrace]
  refine ⟨267595699860972512430008705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178397133240648341620005803 267595699860972512430008705)
  ·
    refine ⟨200696774895729384322506529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267595699860972512430008705 200696774895729384322506529)
    ·
      refine ⟨150522581171797038241879897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200696774895729384322506529 150522581171797038241879897)
      ·
        refine ⟨112891935878847778681409923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150522581171797038241879897 112891935878847778681409923)
        ·
          refine ⟨169337903818271668022114885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112891935878847778681409923 169337903818271668022114885)
          ·
            refine ⟨31750856965925937754146541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169337903818271668022114885 31750856965925937754146541)
            ·
              refine ⟨11906571362222226657804953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31750856965925937754146541 11906571362222226657804953)
              ·
                refine ⟨8929928521666669993353715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11906571362222226657804953 8929928521666669993353715)
                ·
                  refine ⟨13394892782500004990030573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8929928521666669993353715 13394892782500004990030573)
                  ·
                    refine ⟨5023084793437501871261465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13394892782500004990030573 5023084793437501871261465)
                    ·
                      refine ⟨3767313595078126403446099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5023084793437501871261465 3767313595078126403446099)
                      ·
                        rfl

theorem cell23_7336817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 2, 1, 3, 2].length) (baseStart_7336817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336817 prefixEnd_7336817 := by exact prefixLift 7336817
  have htrace : WordTrace (prefixWord ++ tailWord_7336817) baseStart_7336817 baseEnd_7336817 := by
    simpa [prefixWord, tailWord_7336817, baseEnd_7336817] using wordTrace_append hprefix tailTrace_7336817
  have hstable : (prefixWord ++ tailWord_7336817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336817).length < 2 ^ (prefixWord ++ tailWord_7336817).sum := by decide
  have hdescent : baseEnd_7336817 < baseStart_7336817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336883 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 2, 5]
def baseStart_7336883 : Nat := 118140960795 + 7336883 * 2 ^ 59
def prefixEnd_7336883 : Nat := 4983230072969 + 3 ^ 40 * 7336883 * 2
def baseEnd_7336883 : Nat := 1255782494933774381740265

theorem tailTrace_7336883 : CollatzResearch.WordTrace tailWord_7336883 prefixEnd_7336883 1255782494933774381740265 := by
  unfold tailWord_7336883
  simp only [CollatzResearch.WordTrace]
  refine ⟨267598107078733405701911303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178398738052488937134607535 267598107078733405701911303)
  ·
    refine ⟨401397160618100108552866955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267598107078733405701911303 401397160618100108552866955)
    ·
      refine ⟨602095740927150162829300433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401397160618100108552866955 602095740927150162829300433)
      ·
        refine ⟨451571805695362622121975325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602095740927150162829300433 451571805695362622121975325)
        ·
          refine ⟨169339427135760983295740747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451571805695362622121975325 169339427135760983295740747)
          ·
            refine ⟨254009140703641474943611121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169339427135760983295740747 254009140703641474943611121)
            ·
              refine ⟨190506855527731106207708341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254009140703641474943611121 190506855527731106207708341)
              ·
                refine ⟨17860017705724791206972657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190506855527731106207708341 17860017705724791206972657)
                ·
                  refine ⟨13395013279293593405229493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17860017705724791206972657 13395013279293593405229493)
                  ·
                    refine ⟨1255782494933774381740265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13395013279293593405229493 1255782494933774381740265)
                    ·
                      rfl

theorem cell23_7336883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 5].length) (baseStart_7336883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336883 prefixEnd_7336883 := by exact prefixLift 7336883
  have htrace : WordTrace (prefixWord ++ tailWord_7336883) baseStart_7336883 baseEnd_7336883 := by
    simpa [prefixWord, tailWord_7336883, baseEnd_7336883] using wordTrace_append hprefix tailTrace_7336883
  have hstable : (prefixWord ++ tailWord_7336883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336883).length < 2 ^ (prefixWord ++ tailWord_7336883).sum := by decide
  have hdescent : baseEnd_7336883 < baseStart_7336883 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7336943 : List Nat := [1, 1, 2, 1, 4, 3, 1, 2, 8]
def baseStart_7336943 : Nat := 118140960795 + 7336943 * 2 ^ 59
def prefixEnd_7336943 : Nat := 4983230072969 + 3 ^ 40 * 7336943 * 2
def baseEnd_7336943 : Nat := 418597588182288101163391

theorem tailTrace_7336943 : CollatzResearch.WordTrace tailWord_7336943 prefixEnd_7336943 418597588182288101163391 := by
  unfold tailWord_7336943
  simp only [CollatzResearch.WordTrace]
  refine ⟨267600295458516035949095483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178400196972344023966063655 267600295458516035949095483)
  ·
    refine ⟨401400443187774053923643225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267600295458516035949095483 401400443187774053923643225)
    ·
      refine ⟨301050332390830540442732419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401400443187774053923643225 301050332390830540442732419)
      ·
        refine ⟨451575498586245810664098629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301050332390830540442732419 451575498586245810664098629)
        ·
          refine ⟨84670405984921089499518493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 451575498586245810664098629 84670405984921089499518493)
          ·
            refine ⟨31751402244345408562319435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84670405984921089499518493 31751402244345408562319435)
            ·
              refine ⟨47627103366518112843479153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31751402244345408562319435 47627103366518112843479153)
              ·
                refine ⟨35720327524888584632609365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47627103366518112843479153 35720327524888584632609365)
                ·
                  refine ⟨418597588182288101163391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35720327524888584632609365 418597588182288101163391)
                  ·
                    rfl

theorem cell23_7336943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 8].length) (baseStart_7336943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7336943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7336943 prefixEnd_7336943 := by exact prefixLift 7336943
  have htrace : WordTrace (prefixWord ++ tailWord_7336943) baseStart_7336943 baseEnd_7336943 := by
    simpa [prefixWord, tailWord_7336943, baseEnd_7336943] using wordTrace_append hprefix tailTrace_7336943
  have hstable : (prefixWord ++ tailWord_7336943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7336943).length < 2 ^ (prefixWord ++ tailWord_7336943).sum := by decide
  have hdescent : baseEnd_7336943 < baseStart_7336943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7336943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337004 : List Nat := [2, 2, 1, 1, 1, 2, 4, 5, 1, 1, 3]
def baseStart_7337004 : Nat := 118140960795 + 7337004 * 2 ^ 59
def prefixEnd_7337004 : Nat := 4983230072969 + 3 ^ 40 * 7337004 * 2
def baseEnd_7337004 : Nat := 3767409615960517171807739

theorem tailTrace_7337004 : CollatzResearch.WordTrace tailWord_7337004 prefixEnd_7337004 3767409615960517171807739 := by
  unfold tailWord_7337004
  simp only [CollatzResearch.WordTrace]
  refine ⟨133801260155647521683533033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178401680207530028911377377 133801260155647521683533033)
  ·
    refine ⟨100350945116735641262649775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133801260155647521683533033 100350945116735641262649775)
    ·
      refine ⟨150526417675103461893974663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100350945116735641262649775 150526417675103461893974663)
      ·
        refine ⟨225789626512655192840961995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150526417675103461893974663 225789626512655192840961995)
        ·
          refine ⟨338684439768982789261442993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225789626512655192840961995 338684439768982789261442993)
          ·
            refine ⟨254013329826737091946082245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338684439768982789261442993 254013329826737091946082245)
            ·
              refine ⟨47627499342513204739890421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254013329826737091946082245 47627499342513204739890421)
              ·
                refine ⟨4465078063360612944364727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47627499342513204739890421 4465078063360612944364727)
                ·
                  refine ⟨6697617095040919416547091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4465078063360612944364727 6697617095040919416547091)
                  ·
                    refine ⟨10046425642561379124820637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6697617095040919416547091 10046425642561379124820637)
                    ·
                      refine ⟨3767409615960517171807739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10046425642561379124820637 3767409615960517171807739)
                      ·
                        rfl

theorem cell23_7337004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 5, 1, 1, 3].length) (baseStart_7337004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337004 prefixEnd_7337004 := by exact prefixLift 7337004
  have htrace : WordTrace (prefixWord ++ tailWord_7337004) baseStart_7337004 baseEnd_7337004 := by
    simpa [prefixWord, tailWord_7337004, baseEnd_7337004] using wordTrace_append hprefix tailTrace_7337004
  have hstable : (prefixWord ++ tailWord_7337004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337004).length < 2 ^ (prefixWord ++ tailWord_7337004).sum := by decide
  have hdescent : baseEnd_7337004 < baseStart_7337004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337021 : List Nat := [1, 4, 1, 3, 1, 3, 1, 4, 1, 1, 3]
def baseStart_7337021 : Nat := 118140960795 + 7337021 * 2 ^ 59
def prefixEnd_7337021 : Nat := 4983230072969 + 3 ^ 40 * 7337021 * 2
def baseEnd_7337021 : Nat := 3767418345131643605295161

theorem tailTrace_7337021 : CollatzResearch.WordTrace tailWord_7337021 prefixEnd_7337021 3767418345131643605295161 := by
  unfold tailWord_7337021
  simp only [CollatzResearch.WordTrace]
  refine ⟨267603140352233455270434917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178402093568155636846956611 267603140352233455270434917)
  ·
    refine ⟨50175588816043772863206547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267603140352233455270434917 50175588816043772863206547)
    ·
      refine ⟨75263383224065659294809821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50175588816043772863206547 75263383224065659294809821)
      ·
        refine ⟨28223768709024622235553683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75263383224065659294809821 28223768709024622235553683)
        ·
          refine ⟨42335653063536933353330525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28223768709024622235553683 42335653063536933353330525)
          ·
            refine ⟨15875869898826350007498947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42335653063536933353330525 15875869898826350007498947)
            ·
              refine ⟨23813804848239525011248421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15875869898826350007498947 23813804848239525011248421)
              ·
                refine ⟨4465088409044910939609079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23813804848239525011248421 4465088409044910939609079)
                ·
                  refine ⟨6697632613567366409413619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4465088409044910939609079 6697632613567366409413619)
                  ·
                    refine ⟨10046448920351049614120429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6697632613567366409413619 10046448920351049614120429)
                    ·
                      refine ⟨3767418345131643605295161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10046448920351049614120429 3767418345131643605295161)
                      ·
                        rfl

theorem cell23_7337021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_7337021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337021 prefixEnd_7337021 := by exact prefixLift 7337021
  have htrace : WordTrace (prefixWord ++ tailWord_7337021) baseStart_7337021 baseEnd_7337021 := by
    simpa [prefixWord, tailWord_7337021, baseEnd_7337021] using wordTrace_append hprefix tailTrace_7337021
  have hstable : (prefixWord ++ tailWord_7337021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337021).length < 2 ^ (prefixWord ++ tailWord_7337021).sum := by decide
  have hdescent : baseEnd_7337021 < baseStart_7337021 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337033 : List Nat := [1, 2, 1, 1, 2, 2, 2, 12]
def baseStart_7337033 : Nat := 118140960795 + 7337033 * 2 ^ 59
def prefixEnd_7337033 : Nat := 4983230072969 + 3 ^ 40 * 7337033 * 2
def baseEnd_7337033 : Nat := 139534240996277687346115

theorem tailTrace_7337033 : CollatzResearch.WordTrace tailWord_7337033 prefixEnd_7337033 139534240996277687346115 := by
  unfold tailWord_7337033
  simp only [CollatzResearch.WordTrace]
  refine ⟨267603578028189981319871753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178402385352126654213247835 267603578028189981319871753)
  ·
    refine ⟨200702683521142485989903815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267603578028189981319871753 200702683521142485989903815)
    ·
      refine ⟨301054025281713728984855723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200702683521142485989903815 301054025281713728984855723)
      ·
        refine ⟨451581037922570593477283585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301054025281713728984855723 451581037922570593477283585)
        ·
          refine ⟨338685778441927945107962689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451581037922570593477283585 338685778441927945107962689)
          ·
            refine ⟨254014333831445958830972017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338685778441927945107962689 254014333831445958830972017)
            ·
              refine ⟨190510750373584469123229013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254014333831445958830972017 190510750373584469123229013)
              ·
                refine ⟨139534240996277687346115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 190510750373584469123229013 139534240996277687346115)
                ·
                  rfl

theorem cell23_7337033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 12].length) (baseStart_7337033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337033 prefixEnd_7337033 := by exact prefixLift 7337033
  have htrace : WordTrace (prefixWord ++ tailWord_7337033) baseStart_7337033 baseEnd_7337033 := by
    simpa [prefixWord, tailWord_7337033, baseEnd_7337033] using wordTrace_append hprefix tailTrace_7337033
  have hstable : (prefixWord ++ tailWord_7337033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337033).length < 2 ^ (prefixWord ++ tailWord_7337033).sum := by decide
  have hdescent : baseEnd_7337033 < baseStart_7337033 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337037 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_7337037 : Nat := 118140960795 + 7337037 * 2 ^ 59
def prefixEnd_7337037 : Nat := 4983230072969 + 3 ^ 40 * 7337037 * 2
def baseEnd_7337037 : Nat := 1255808853607371847565029

theorem tailTrace_7337037 : CollatzResearch.WordTrace tailWord_7337037 prefixEnd_7337037 1255808853607371847565029 := by
  unfold tailWord_7337037
  simp only [CollatzResearch.WordTrace]
  refine ⟨267603723920175490003017365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178402482613450326668678243 267603723920175490003017365)
  ·
    refine ⟨12543924558758226093891439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 267603723920175490003017365 12543924558758226093891439)
    ·
      refine ⟨18815886838137339140837159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12543924558758226093891439 18815886838137339140837159)
      ·
        refine ⟨28223830257206008711255739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18815886838137339140837159 28223830257206008711255739)
        ·
          refine ⟨42335745385809013066883609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28223830257206008711255739 42335745385809013066883609)
          ·
            refine ⟨31751809039356759800162707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42335745385809013066883609 31751809039356759800162707)
            ·
              refine ⟨47627713559035139700244061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31751809039356759800162707 47627713559035139700244061)
              ·
                refine ⟨17860392584638177387591523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47627713559035139700244061 17860392584638177387591523)
                ·
                  refine ⟨26790588876957266081387285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17860392584638177387591523 26790588876957266081387285)
                  ·
                    refine ⟨1255808853607371847565029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26790588876957266081387285 1255808853607371847565029)
                    ·
                      rfl

theorem cell23_7337037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_7337037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337037 prefixEnd_7337037 := by exact prefixLift 7337037
  have htrace : WordTrace (prefixWord ++ tailWord_7337037) baseStart_7337037 baseEnd_7337037 := by
    simpa [prefixWord, tailWord_7337037, baseEnd_7337037] using wordTrace_append hprefix tailTrace_7337037
  have hstable : (prefixWord ++ tailWord_7337037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337037).length < 2 ^ (prefixWord ++ tailWord_7337037).sum := by decide
  have hdescent : baseEnd_7337037 < baseStart_7337037 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337044 : List Nat := [2, 4, 1, 1, 1, 1, 3, 1, 5, 2, 2]
def baseStart_7337044 : Nat := 118140960795 + 7337044 * 2 ^ 59
def prefixEnd_7337044 : Nat := 4983230072969 + 3 ^ 40 * 7337044 * 2
def baseEnd_7337044 : Nat := 3767430155186697015307555

theorem tailTrace_7337044 : CollatzResearch.WordTrace tailWord_7337044 prefixEnd_7337044 3767430155186697015307555 := by
  unfold tailWord_7337044
  simp only [CollatzResearch.WordTrace]
  refine ⟨133801989615575065099261093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178402652820766753465681457 133801989615575065099261093)
  ·
    refine ⟨25087873052920324706111455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133801989615575065099261093 25087873052920324706111455)
    ·
      refine ⟨37631809579380487059167183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25087873052920324706111455 37631809579380487059167183)
      ·
        refine ⟨56447714369070730588750775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37631809579380487059167183 56447714369070730588750775)
        ·
          refine ⟨84671571553606095883126163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56447714369070730588750775 84671571553606095883126163)
          ·
            refine ⟨127007357330409143824689245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84671571553606095883126163 127007357330409143824689245)
            ·
              refine ⟨47627758998903428934258467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127007357330409143824689245 47627758998903428934258467)
              ·
                refine ⟨71441638498355143401387701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47627758998903428934258467 71441638498355143401387701)
                ·
                  refine ⟨6697653609220794693880097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71441638498355143401387701 6697653609220794693880097)
                  ·
                    refine ⟨5023240206915596020410073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6697653609220794693880097 5023240206915596020410073)
                    ·
                      refine ⟨3767430155186697015307555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5023240206915596020410073 3767430155186697015307555)
                      ·
                        rfl

theorem cell23_7337044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 5, 2, 2].length) (baseStart_7337044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337044 prefixEnd_7337044 := by exact prefixLift 7337044
  have htrace : WordTrace (prefixWord ++ tailWord_7337044) baseStart_7337044 baseEnd_7337044 := by
    simpa [prefixWord, tailWord_7337044, baseEnd_7337044] using wordTrace_append hprefix tailTrace_7337044
  have hstable : (prefixWord ++ tailWord_7337044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337044).length < 2 ^ (prefixWord ++ tailWord_7337044).sum := by decide
  have hdescent : baseEnd_7337044 < baseStart_7337044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337047 : List Nat := [1, 1, 3, 2, 2, 1, 1, 6, 1, 2, 3]
def baseStart_7337047 : Nat := 118140960795 + 7337047 * 2 ^ 59
def prefixEnd_7337047 : Nat := 4983230072969 + 3 ^ 40 * 7337047 * 2
def baseEnd_7337047 : Nat := 3767431695628660503570041

theorem tailTrace_7337047 : CollatzResearch.WordTrace tailWord_7337047 prefixEnd_7337047 3767431695628660503570041 := by
  unfold tailWord_7337047
  simp only [CollatzResearch.WordTrace]
  refine ⟨267604088650139261710881395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178402725766759507807254263 267604088650139261710881395)
  ·
    refine ⟨401406132975208892566322093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267604088650139261710881395 401406132975208892566322093)
    ·
      refine ⟨150527299865703334712370785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401406132975208892566322093 150527299865703334712370785)
      ·
        refine ⟨112895474899277501034278089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150527299865703334712370785 112895474899277501034278089)
        ·
          refine ⟨84671606174458125775708567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112895474899277501034278089 84671606174458125775708567)
          ·
            refine ⟨127007409261687188663562851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84671606174458125775708567 127007409261687188663562851)
            ·
              refine ⟨190511113892530782995344277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127007409261687188663562851 190511113892530782995344277)
              ·
                refine ⟨8930208463712380452906763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 190511113892530782995344277 8930208463712380452906763)
                ·
                  refine ⟨13395312695568570679360145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8930208463712380452906763 13395312695568570679360145)
                  ·
                    refine ⟨10046484521676428009520109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13395312695568570679360145 10046484521676428009520109)
                    ·
                      refine ⟨3767431695628660503570041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10046484521676428009520109 3767431695628660503570041)
                      ·
                        rfl

theorem cell23_7337047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_7337047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337047 prefixEnd_7337047 := by exact prefixLift 7337047
  have htrace : WordTrace (prefixWord ++ tailWord_7337047) baseStart_7337047 baseEnd_7337047 := by
    simpa [prefixWord, tailWord_7337047, baseEnd_7337047] using wordTrace_append hprefix tailTrace_7337047
  have hstable : (prefixWord ++ tailWord_7337047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337047).length < 2 ^ (prefixWord ++ tailWord_7337047).sum := by decide
  have hdescent : baseEnd_7337047 < baseStart_7337047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337078 : List Nat := [5, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2]
def baseStart_7337078 : Nat := 118140960795 + 7337078 * 2 ^ 59
def prefixEnd_7337078 : Nat := 4983230072969 + 3 ^ 40 * 7337078 * 2
def baseEnd_7337078 : Nat := 3767447613528949882282399

theorem tailTrace_7337078 : CollatzResearch.WordTrace tailWord_7337078 prefixEnd_7337078 3767447613528949882282399 := by
  unfold tailWord_7337078
  simp only [CollatzResearch.WordTrace]
  refine ⟨16725326207064184625328743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178403479542017969336839925 16725326207064184625328743)
  ·
    refine ⟨25087989310596276937993115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16725326207064184625328743 25087989310596276937993115)
    ·
      refine ⟨37631983965894415406989673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25087989310596276937993115 37631983965894415406989673)
      ·
        refine ⟨28223987974420811555242255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37631983965894415406989673 28223987974420811555242255)
        ·
          refine ⟨42335981961631217332863383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28223987974420811555242255 42335981961631217332863383)
          ·
            refine ⟨63503972942446825999295075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42335981961631217332863383 63503972942446825999295075)
            ·
              refine ⟨95255959413670238998942613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63503972942446825999295075 95255959413670238998942613)
              ·
                refine ⟨4465123097515792453075435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95255959413670238998942613 4465123097515792453075435)
                ·
                  refine ⟨6697684646273688679613153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4465123097515792453075435 6697684646273688679613153)
                  ·
                    refine ⟨5023263484705266509709865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6697684646273688679613153 5023263484705266509709865)
                    ·
                      refine ⟨3767447613528949882282399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5023263484705266509709865 3767447613528949882282399)
                      ·
                        rfl

theorem cell23_7337078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_7337078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337078 prefixEnd_7337078 := by exact prefixLift 7337078
  have htrace : WordTrace (prefixWord ++ tailWord_7337078) baseStart_7337078 baseEnd_7337078 := by
    simpa [prefixWord, tailWord_7337078, baseEnd_7337078] using wordTrace_append hprefix tailTrace_7337078
  have hstable : (prefixWord ++ tailWord_7337078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337078).length < 2 ^ (prefixWord ++ tailWord_7337078).sum := by decide
  have hdescent : baseEnd_7337078 < baseStart_7337078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337100 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 2, 3, 4]
def baseStart_7337100 : Nat := 118140960795 + 7337100 * 2 ^ 59
def prefixEnd_7337100 : Nat := 4983230072969 + 3 ^ 40 * 7337100 * 2
def baseEnd_7337100 : Nat := 3767458910103348796207297

theorem tailTrace_7337100 : CollatzResearch.WordTrace tailWord_7337100 prefixEnd_7337100 3767458910103348796207297 := by
  unfold tailWord_7337100
  simp only [CollatzResearch.WordTrace]
  refine ⟨133803010859473625881280377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178404014479298167841707169 133803010859473625881280377)
  ·
    refine ⟨100352258144605219410960283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133803010859473625881280377 100352258144605219410960283)
    ·
      refine ⟨150528387216907829116440425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100352258144605219410960283 150528387216907829116440425)
      ·
        refine ⟨112896290412680871837330319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150528387216907829116440425 112896290412680871837330319)
        ·
          refine ⟨169344435619021307755995479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112896290412680871837330319 169344435619021307755995479)
          ·
            refine ⟨254016653428531961633993219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169344435619021307755995479 254016653428531961633993219)
            ·
              refine ⟨381024980142797942450989829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254016653428531961633993219 381024980142797942450989829)
              ·
                refine ⟨71442183776774614209560593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 381024980142797942450989829 71442183776774614209560593)
                ·
                  refine ⟨53581637832580960657170445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71442183776774614209560593 53581637832580960657170445)
                  ·
                    refine ⟨20093114187217860246438917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53581637832580960657170445 20093114187217860246438917)
                    ·
                      refine ⟨3767458910103348796207297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20093114187217860246438917 3767458910103348796207297)
                      ·
                        rfl

theorem cell23_7337100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_7337100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337100 prefixEnd_7337100 := by exact prefixLift 7337100
  have htrace : WordTrace (prefixWord ++ tailWord_7337100) baseStart_7337100 baseEnd_7337100 := by
    simpa [prefixWord, tailWord_7337100, baseEnd_7337100] using wordTrace_append hprefix tailTrace_7337100
  have hstable : (prefixWord ++ tailWord_7337100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337100).length < 2 ^ (prefixWord ++ tailWord_7337100).sum := by decide
  have hdescent : baseEnd_7337100 < baseStart_7337100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337191 : List Nat := [1, 1, 5, 3, 2, 1, 1, 4, 5]
def baseStart_7337191 : Nat := 118140960795 + 7337191 * 2 ^ 59
def prefixEnd_7337191 : Nat := 4983230072969 + 3 ^ 40 * 7337191 * 2
def baseEnd_7337191 : Nat := 418611737426989771129931

theorem tailTrace_7337191 : CollatzResearch.WordTrace tailWord_7337191 prefixEnd_7337191 418611737426989771129931 := by
  unfold tailWord_7337191
  simp only [CollatzResearch.WordTrace]
  refine ⟨267609340761617574304123427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178406227174411716202748951 267609340761617574304123427)
  ·
    refine ⟨401414011142426361456185141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267609340761617574304123427 401414011142426361456185141)
    ·
      refine ⟨37632563544602471386517357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 401414011142426361456185141 37632563544602471386517357)
      ·
        refine ⟨14112211329225926769944009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37632563544602471386517357 14112211329225926769944009)
        ·
          refine ⟨10584158496919445077458007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14112211329225926769944009 10584158496919445077458007)
          ·
            refine ⟨15876237745379167616187011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10584158496919445077458007 15876237745379167616187011)
            ·
              refine ⟨23814356618068751424280517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15876237745379167616187011 23814356618068751424280517)
              ·
                refine ⟨4465191865887890892052597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23814356618068751424280517 4465191865887890892052597)
                ·
                  refine ⟨418611737426989771129931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4465191865887890892052597 418611737426989771129931)
                  ·
                    rfl

theorem cell23_7337191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 4, 5].length) (baseStart_7337191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337191 prefixEnd_7337191 := by exact prefixLift 7337191
  have htrace : WordTrace (prefixWord ++ tailWord_7337191) baseStart_7337191 baseEnd_7337191 := by
    simpa [prefixWord, tailWord_7337191, baseEnd_7337191] using wordTrace_append hprefix tailTrace_7337191
  have hstable : (prefixWord ++ tailWord_7337191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337191).length < 2 ^ (prefixWord ++ tailWord_7337191).sum := by decide
  have hdescent : baseEnd_7337191 < baseStart_7337191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337194 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 2, 5, 2]
def baseStart_7337194 : Nat := 118140960795 + 7337194 * 2 ^ 59
def prefixEnd_7337194 : Nat := 4983230072969 + 3 ^ 40 * 7337194 * 2
def baseEnd_7337194 : Nat := 3767507177284871428431865

theorem tailTrace_7337194 : CollatzResearch.WordTrace tailWord_7337194 prefixEnd_7337194 3767507177284871428431865 := by
  unfold tailWord_7337194
  simp only [CollatzResearch.WordTrace]
  refine ⟨66902362545151676454120659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178406300120404470544321757 66902362545151676454120659)
  ·
    refine ⟨100353543817727514681180989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66902362545151676454120659 100353543817727514681180989)
    ·
      refine ⟨37632578931647818005442871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100353543817727514681180989 37632578931647818005442871)
      ·
        refine ⟨56448868397471727008164307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37632578931647818005442871 56448868397471727008164307)
        ·
          refine ⟨84673302596207590512246461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56448868397471727008164307 84673302596207590512246461)
          ·
            refine ⟨31752488473577846442092423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84673302596207590512246461 31752488473577846442092423)
            ·
              refine ⟨47628732710366769663138635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31752488473577846442092423 47628732710366769663138635)
              ·
                refine ⟨71443099065550154494707953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47628732710366769663138635 71443099065550154494707953)
                ·
                  refine ⟨53582324299162615871030965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71443099065550154494707953 53582324299162615871030965)
                  ·
                    refine ⟨5023342903046495237909153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53582324299162615871030965 5023342903046495237909153)
                    ·
                      refine ⟨3767507177284871428431865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5023342903046495237909153 3767507177284871428431865)
                      ·
                        rfl

theorem cell23_7337194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_7337194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337194 prefixEnd_7337194 := by exact prefixLift 7337194
  have htrace : WordTrace (prefixWord ++ tailWord_7337194) baseStart_7337194 baseEnd_7337194 := by
    simpa [prefixWord, tailWord_7337194, baseEnd_7337194] using wordTrace_append hprefix tailTrace_7337194
  have hstable : (prefixWord ++ tailWord_7337194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337194).length < 2 ^ (prefixWord ++ tailWord_7337194).sum := by decide
  have hdescent : baseEnd_7337194 < baseStart_7337194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337200 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 4, 8]
def baseStart_7337200 : Nat := 118140960795 + 7337200 * 2 ^ 59
def prefixEnd_7337200 : Nat := 4983230072969 + 3 ^ 40 * 7337200 * 2
def baseEnd_7337200 : Nat := 1255836752722932801652279

theorem tailTrace_7337200 : CollatzResearch.WordTrace tailWord_7337200 prefixEnd_7337200 1255836752722932801652279 := by
  unfold tailWord_7337200
  simp only [CollatzResearch.WordTrace]
  refine ⟨133804834509292484420600527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178406446012389979227467369 133804834509292484420600527)
  ·
    refine ⟨200707251763938726630900791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133804834509292484420600527 200707251763938726630900791)
    ·
      refine ⟨301060877645908089946351187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200707251763938726630900791 301060877645908089946351187)
      ·
        refine ⟨451591316468862134919526781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301060877645908089946351187 451591316468862134919526781)
        ·
          refine ⟨169346743675823300594822543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451591316468862134919526781 169346743675823300594822543)
          ·
            refine ⟨254020115513734950892233815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169346743675823300594822543 254020115513734950892233815)
            ·
              refine ⟨381030173270602426338350723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254020115513734950892233815 381030173270602426338350723)
              ·
                refine ⟨571545259905903639507526085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 381030173270602426338350723 571545259905903639507526085)
                ·
                  refine ⟨107164736232356932407661141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 571545259905903639507526085 107164736232356932407661141)
                  ·
                    refine ⟨1255836752722932801652279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107164736232356932407661141 1255836752722932801652279)
                    ·
                      rfl

theorem cell23_7337200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 8].length) (baseStart_7337200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337200 prefixEnd_7337200 := by exact prefixLift 7337200
  have htrace : WordTrace (prefixWord ++ tailWord_7337200) baseStart_7337200 baseEnd_7337200 := by
    simpa [prefixWord, tailWord_7337200, baseEnd_7337200] using wordTrace_append hprefix tailTrace_7337200
  have hstable : (prefixWord ++ tailWord_7337200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337200).length < 2 ^ (prefixWord ++ tailWord_7337200).sum := by decide
  have hdescent : baseEnd_7337200 < baseStart_7337200 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337224 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 1, 3, 4]
def baseStart_7337224 : Nat := 118140960795 + 7337224 * 2 ^ 59
def prefixEnd_7337224 : Nat := 4983230072969 + 3 ^ 40 * 7337224 * 2
def baseEnd_7337224 : Nat := 3767522581704506311056727

theorem tailTrace_7337224 : CollatzResearch.WordTrace tailWord_7337224 prefixEnd_7337224 3767522581704506311056727 := by
  unfold tailWord_7337224
  simp only [CollatzResearch.WordTrace]
  refine ⟨133805272185249010470037363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178407029580332013960049817 133805272185249010470037363)
  ·
    refine ⟨200707908277873515705056045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133805272185249010470037363 200707908277873515705056045)
    ·
      refine ⟨75265465604202568389396017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200707908277873515705056045 75265465604202568389396017)
      ·
        refine ⟨56449099203151926292047013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75265465604202568389396017 56449099203151926292047013)
        ·
          refine ⟨10584206100590986179758815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56449099203151926292047013 10584206100590986179758815)
          ·
            refine ⟨15876309150886479269638223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10584206100590986179758815 15876309150886479269638223)
            ·
              refine ⟨23814463726329718904457335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15876309150886479269638223 23814463726329718904457335)
              ·
                refine ⟨35721695589494578356686003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23814463726329718904457335 35721695589494578356686003)
                ·
                  refine ⟨53582543384241867535029005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35721695589494578356686003 53582543384241867535029005)
                  ·
                    refine ⟨20093453769090700325635877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53582543384241867535029005 20093453769090700325635877)
                    ·
                      refine ⟨3767522581704506311056727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20093453769090700325635877 3767522581704506311056727)
                      ·
                        rfl

theorem cell23_7337224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_7337224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337224 prefixEnd_7337224 := by exact prefixLift 7337224
  have htrace : WordTrace (prefixWord ++ tailWord_7337224) baseStart_7337224 baseEnd_7337224 := by
    simpa [prefixWord, tailWord_7337224, baseEnd_7337224] using wordTrace_append hprefix tailTrace_7337224
  have hstable : (prefixWord ++ tailWord_7337224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337224).length < 2 ^ (prefixWord ++ tailWord_7337224).sum := by decide
  have hdescent : baseEnd_7337224 < baseStart_7337224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337244 : List Nat := [2, 2, 3, 1, 1, 1, 2, 4, 2, 2, 3]
def baseStart_7337244 : Nat := 118140960795 + 7337244 * 2 ^ 59
def prefixEnd_7337244 : Nat := 4983230072969 + 3 ^ 40 * 7337244 * 2
def baseEnd_7337244 : Nat := 3767532851317596232806635

theorem tailTrace_7337244 : CollatzResearch.WordTrace tailWord_7337244 prefixEnd_7337244 3767532851317596232806635 := by
  unfold tailWord_7337244
  simp only [CollatzResearch.WordTrace]
  refine ⟨133805636915212782177901393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178407515886950376237201857 133805636915212782177901393)
  ·
    refine ⟨100354227686409586633426045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133805636915212782177901393 100354227686409586633426045)
    ·
      refine ⟨37632835382403594987534767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100354227686409586633426045 37632835382403594987534767)
      ·
        refine ⟨56449253073605392481302151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37632835382403594987534767 56449253073605392481302151)
        ·
          refine ⟨84673879610408088721953227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56449253073605392481302151 84673879610408088721953227)
          ·
            refine ⟨127010819415612133082929841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84673879610408088721953227 127010819415612133082929841)
            ·
              refine ⟨95258114561709099812197381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127010819415612133082929841 95258114561709099812197381)
              ·
                refine ⟨17860896480320456214787009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95258114561709099812197381 17860896480320456214787009)
                ·
                  refine ⟨13395672360240342161090257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17860896480320456214787009 13395672360240342161090257)
                  ·
                    refine ⟨10046754270180256620817693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13395672360240342161090257 10046754270180256620817693)
                    ·
                      refine ⟨3767532851317596232806635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10046754270180256620817693 3767532851317596232806635)
                      ·
                        rfl

theorem cell23_7337244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_7337244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337244 prefixEnd_7337244 := by exact prefixLift 7337244
  have htrace : WordTrace (prefixWord ++ tailWord_7337244) baseStart_7337244 baseEnd_7337244 := by
    simpa [prefixWord, tailWord_7337244, baseEnd_7337244] using wordTrace_append hprefix tailTrace_7337244
  have hstable : (prefixWord ++ tailWord_7337244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337244).length < 2 ^ (prefixWord ++ tailWord_7337244).sum := by decide
  have hdescent : baseEnd_7337244 < baseStart_7337244 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337251 : List Nat := [1, 1, 1, 4, 2, 3, 2, 4, 1, 4]
def baseStart_7337251 : Nat := 118140960795 + 7337251 * 2 ^ 59
def prefixEnd_7337251 : Nat := 4983230072969 + 3 ^ 40 * 7337251 * 2
def baseEnd_7337251 : Nat := 1255845481894059235139701

theorem tailTrace_7337251 : CollatzResearch.WordTrace tailWord_7337251 prefixEnd_7337251 1255845481894059235139701 := by
  unfold tailWord_7337251
  simp only [CollatzResearch.WordTrace]
  refine ⟨267611529141400204551307607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178407686094266803034205071 267611529141400204551307607)
  ·
    refine ⟨401417293712100306826961411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267611529141400204551307607 401417293712100306826961411)
    ·
      refine ⟨602125940568150460240442117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401417293712100306826961411 602125940568150460240442117)
      ·
        refine ⟨112898613856528211295082897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 602125940568150460240442117 112898613856528211295082897)
        ·
          refine ⟨84673960392396158471312173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112898613856528211295082897 84673960392396158471312173)
          ·
            refine ⟨31752735147148559426742065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84673960392396158471312173 31752735147148559426742065)
            ·
              refine ⟨23814551360361419570056549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31752735147148559426742065 23814551360361419570056549)
              ·
                refine ⟨4465228380067766169385603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23814551360361419570056549 4465228380067766169385603)
                ·
                  refine ⟨6697842570101649254078405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4465228380067766169385603 6697842570101649254078405)
                  ·
                    refine ⟨1255845481894059235139701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6697842570101649254078405 1255845481894059235139701)
                    ·
                      rfl

theorem cell23_7337251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 1, 4].length) (baseStart_7337251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337251 prefixEnd_7337251 := by exact prefixLift 7337251
  have htrace : WordTrace (prefixWord ++ tailWord_7337251) baseStart_7337251 baseEnd_7337251 := by
    simpa [prefixWord, tailWord_7337251, baseEnd_7337251] using wordTrace_append hprefix tailTrace_7337251
  have hstable : (prefixWord ++ tailWord_7337251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337251).length < 2 ^ (prefixWord ++ tailWord_7337251).sum := by decide
  have hdescent : baseEnd_7337251 < baseStart_7337251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337261 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_7337261 : Nat := 118140960795 + 7337261 * 2 ^ 59
def prefixEnd_7337261 : Nat := 4983230072969 + 3 ^ 40 * 7337261 * 2
def baseEnd_7337261 : Nat := 3767541580488722666294057

theorem tailTrace_7337261 : CollatzResearch.WordTrace tailWord_7337261 prefixEnd_7337261 3767541580488722666294057 := by
  unfold tailWord_7337261
  simp only [CollatzResearch.WordTrace]
  refine ⟨267611893871363976259171637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178407929247575984172781091 267611893871363976259171637)
  ·
    refine ⟨25088615050440372774297341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267611893871363976259171637 25088615050440372774297341)
    ·
      refine ⟨9408230643915139790361503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25088615050440372774297341 9408230643915139790361503)
      ·
        refine ⟨14112345965872709685542255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9408230643915139790361503 14112345965872709685542255)
        ·
          refine ⟨21168518948809064528313383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14112345965872709685542255 21168518948809064528313383)
          ·
            refine ⟨31752778423213596792470075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21168518948809064528313383 31752778423213596792470075)
            ·
              refine ⟨47629167634820395188705113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31752778423213596792470075 47629167634820395188705113)
              ·
                refine ⟨35721875726115296391528835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47629167634820395188705113 35721875726115296391528835)
                ·
                  refine ⟨53582813589172944587293253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35721875726115296391528835 53582813589172944587293253)
                  ·
                    refine ⟨10046777547969927110117485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53582813589172944587293253 10046777547969927110117485)
                    ·
                      refine ⟨3767541580488722666294057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10046777547969927110117485 3767541580488722666294057)
                      ·
                        rfl

theorem cell23_7337261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_7337261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337261 prefixEnd_7337261 := by exact prefixLift 7337261
  have htrace : WordTrace (prefixWord ++ tailWord_7337261) baseStart_7337261 baseEnd_7337261 := by
    simpa [prefixWord, tailWord_7337261, baseEnd_7337261] using wordTrace_append hprefix tailTrace_7337261
  have hstable : (prefixWord ++ tailWord_7337261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337261).length < 2 ^ (prefixWord ++ tailWord_7337261).sum := by decide
  have hdescent : baseEnd_7337261 < baseStart_7337261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337264 : List Nat := [2, 1, 1, 1, 2, 2, 7, 1, 6]
def baseStart_7337264 : Nat := 118140960795 + 7337264 * 2 ^ 59
def prefixEnd_7337264 : Nat := 4983230072969 + 3 ^ 40 * 7337264 * 2
def baseEnd_7337264 : Nat := 418615902325631794950727

theorem tailTrace_7337264 : CollatzResearch.WordTrace tailWord_7337264 prefixEnd_7337264 418615902325631794950727 := by
  unfold tailWord_7337264
  simp only [CollatzResearch.WordTrace]
  refine ⟨133806001645176553885765423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178408002193568738514353897 133806001645176553885765423)
  ·
    refine ⟨200709002467764830828648135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133806001645176553885765423 200709002467764830828648135)
    ·
      refine ⟨301063503701647246242972203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200709002467764830828648135 301063503701647246242972203)
      ·
        refine ⟨451595255552470869364458305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301063503701647246242972203 451595255552470869364458305)
        ·
          refine ⟨338696441664353152023343729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451595255552470869364458305 338696441664353152023343729)
          ·
            refine ⟨254022331248264864017507797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338696441664353152023343729 254022331248264864017507797)
            ·
              refine ⟨5953648388631207750410339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 254022331248264864017507797 5953648388631207750410339)
              ·
                refine ⟨8930472582946811625615509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5953648388631207750410339 8930472582946811625615509)
                ·
                  refine ⟨418615902325631794950727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8930472582946811625615509 418615902325631794950727)
                  ·
                    rfl

theorem cell23_7337264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 6].length) (baseStart_7337264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337264 prefixEnd_7337264 := by exact prefixLift 7337264
  have htrace : WordTrace (prefixWord ++ tailWord_7337264) baseStart_7337264 baseEnd_7337264 := by
    simpa [prefixWord, tailWord_7337264, baseEnd_7337264] using wordTrace_append hprefix tailTrace_7337264
  have hstable : (prefixWord ++ tailWord_7337264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337264).length < 2 ^ (prefixWord ++ tailWord_7337264).sum := by decide
  have hdescent : baseEnd_7337264 < baseStart_7337264 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337294 : List Nat := [4, 1, 1, 1, 1, 1, 3, 5, 1, 5]
def baseStart_7337294 : Nat := 118140960795 + 7337294 * 2 ^ 59
def prefixEnd_7337294 : Nat := 4983230072969 + 3 ^ 40 * 7337294 * 2
def baseEnd_7337294 : Nat := 1255852841783440345727135

theorem tailTrace_7337294 : CollatzResearch.WordTrace tailWord_7337294 prefixEnd_7337294 1255852841783440345727135 := by
  unfold tailWord_7337294
  simp only [CollatzResearch.WordTrace]
  refine ⟨33451637185030552861890367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178408731653496281930081957 33451637185030552861890367)
  ·
    refine ⟨50177455777545829292835551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33451637185030552861890367 50177455777545829292835551)
    ·
      refine ⟨75266183666318743939253327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50177455777545829292835551 75266183666318743939253327)
      ·
        refine ⟨112899275499478115908879991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75266183666318743939253327 112899275499478115908879991)
        ·
          refine ⟨169348913249217173863319987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112899275499478115908879991 169348913249217173863319987)
          ·
            refine ⟨254023369873825760794979981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169348913249217173863319987 254023369873825760794979981)
            ·
              refine ⟨95258763702684660298117493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254023369873825760794979981 95258763702684660298117493)
              ·
                refine ⟨8930509097126686902948515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95258763702684660298117493 8930509097126686902948515)
                ·
                  refine ⟨13395763645690030354422773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8930509097126686902948515 13395763645690030354422773)
                  ·
                    refine ⟨1255852841783440345727135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13395763645690030354422773 1255852841783440345727135)
                    ·
                      rfl

theorem cell23_7337294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_7337294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337294 prefixEnd_7337294 := by exact prefixLift 7337294
  have htrace : WordTrace (prefixWord ++ tailWord_7337294) baseStart_7337294 baseEnd_7337294 := by
    simpa [prefixWord, tailWord_7337294, baseEnd_7337294] using wordTrace_append hprefix tailTrace_7337294
  have hstable : (prefixWord ++ tailWord_7337294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337294).length < 2 ^ (prefixWord ++ tailWord_7337294).sum := by decide
  have hdescent : baseEnd_7337294 < baseStart_7337294 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337301 : List Nat := [1, 3, 2, 2, 3, 1, 1, 1, 4, 3, 2]
def baseStart_7337301 : Nat := 118140960795 + 7337301 * 2 ^ 59
def prefixEnd_7337301 : Nat := 4983230072969 + 3 ^ 40 * 7337301 * 2
def baseEnd_7337301 : Nat := 3767562119714902509793873

theorem tailTrace_7337301 : CollatzResearch.WordTrace tailWord_7337301 prefixEnd_7337301 3767562119714902509793873 := by
  unfold tailWord_7337301
  simp only [CollatzResearch.WordTrace]
  refine ⟨267613352791219063090627757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178408901860812708727085171 267613352791219063090627757)
  ·
    refine ⟨100355007296707148658985409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267613352791219063090627757 100355007296707148658985409)
    ·
      refine ⟨75266255472530361494239057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100355007296707148658985409 75266255472530361494239057)
      ·
        refine ⟨56449691604397771120679293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75266255472530361494239057 56449691604397771120679293)
        ·
          refine ⟨21168634351649164170254735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56449691604397771120679293 21168634351649164170254735)
          ·
            refine ⟨31752951527473746255382103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21168634351649164170254735 31752951527473746255382103)
            ·
              refine ⟨47629427291210619383073155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31752951527473746255382103 47629427291210619383073155)
              ·
                refine ⟨71444140936815929074609733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47629427291210619383073155 71444140936815929074609733)
                ·
                  refine ⟨13395776425652986701489325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71444140936815929074609733 13395776425652986701489325)
                  ·
                    refine ⟨5023416159619870013058497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13395776425652986701489325 5023416159619870013058497)
                    ·
                      refine ⟨3767562119714902509793873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5023416159619870013058497 3767562119714902509793873)
                      ·
                        rfl

theorem cell23_7337301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 4, 3, 2].length) (baseStart_7337301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337301 prefixEnd_7337301 := by exact prefixLift 7337301
  have htrace : WordTrace (prefixWord ++ tailWord_7337301) baseStart_7337301 baseEnd_7337301 := by
    simpa [prefixWord, tailWord_7337301, baseEnd_7337301] using wordTrace_append hprefix tailTrace_7337301
  have hstable : (prefixWord ++ tailWord_7337301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337301).length < 2 ^ (prefixWord ++ tailWord_7337301).sum := by decide
  have hdescent : baseEnd_7337301 < baseStart_7337301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337327 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 6]
def baseStart_7337327 : Nat := 118140960795 + 7337327 * 2 ^ 59
def prefixEnd_7337327 : Nat := 4983230072969 + 3 ^ 40 * 7337327 * 2
def baseEnd_7337327 : Nat := 3767575470211919408068753

theorem tailTrace_7337327 : CollatzResearch.WordTrace tailWord_7337327 prefixEnd_7337327 3767575470211919408068753 := by
  unfold tailWord_7337327
  simp only [CollatzResearch.WordTrace]
  refine ⟨267614301089124869531074235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178409534059416579687382823 267614301089124869531074235)
  ·
    refine ⟨401421451633687304296611353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267614301089124869531074235 401421451633687304296611353)
    ·
      refine ⟨301066088725265478222458515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401421451633687304296611353 301066088725265478222458515)
      ·
        refine ⟨451599133087898217333687773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301066088725265478222458515 451599133087898217333687773)
        ·
          refine ⟨169349674907961831500132915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451599133087898217333687773 169349674907961831500132915)
          ·
            refine ⟨254024512361942747250199373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169349674907961831500132915 254024512361942747250199373)
            ·
              refine ⟨95259192135728530218824765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254024512361942747250199373 95259192135728530218824765)
              ·
                refine ⟨35722197050898198832059287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95259192135728530218824765 35722197050898198832059287)
                ·
                  refine ⟨53583295576347298248088931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35722197050898198832059287 53583295576347298248088931)
                  ·
                    refine ⟨80374943364520947372133397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53583295576347298248088931 80374943364520947372133397)
                    ·
                      refine ⟨3767575470211919408068753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80374943364520947372133397 3767575470211919408068753)
                      ·
                        rfl

theorem cell23_7337327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_7337327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337327 prefixEnd_7337327 := by exact prefixLift 7337327
  have htrace : WordTrace (prefixWord ++ tailWord_7337327) baseStart_7337327 baseEnd_7337327 := by
    simpa [prefixWord, tailWord_7337327, baseEnd_7337327] using wordTrace_append hprefix tailTrace_7337327
  have hstable : (prefixWord ++ tailWord_7337327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337327).length < 2 ^ (prefixWord ++ tailWord_7337327).sum := by decide
  have hdescent : baseEnd_7337327 < baseStart_7337327 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337337 : List Nat := [1, 2, 1, 3, 2, 1, 4, 9]
def baseStart_7337337 : Nat := 118140960795 + 7337337 * 2 ^ 59
def prefixEnd_7337337 : Nat := 4983230072969 + 3 ^ 40 * 7337337 * 2
def baseEnd_7337337 : Nat := 139540022408091272923841

theorem tailTrace_7337337 : CollatzResearch.WordTrace tailWord_7337337 prefixEnd_7337337 139540022408091272923841 := by
  unfold tailWord_7337337
  simp only [CollatzResearch.WordTrace]
  refine ⟨267614665819088641238938265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178409777212725760825958843 267614665819088641238938265)
  ·
    refine ⟨200710999364316480929203699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267614665819088641238938265 200710999364316480929203699)
    ·
      refine ⟨301066499046474721393805549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200710999364316480929203699 301066499046474721393805549)
      ·
        refine ⟨112899937142428020522677081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301066499046474721393805549 112899937142428020522677081)
        ·
          refine ⟨84674952856821015392007811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112899937142428020522677081 84674952856821015392007811)
          ·
            refine ⟨127012429285231523088011717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84674952856821015392007811 127012429285231523088011717)
            ·
              refine ⟨23814830490980910579002197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127012429285231523088011717 23814830490980910579002197)
              ·
                refine ⟨139540022408091272923841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23814830490980910579002197 139540022408091272923841)
                ·
                  rfl

theorem cell23_7337337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 9].length) (baseStart_7337337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337337 prefixEnd_7337337 := by exact prefixLift 7337337
  have htrace : WordTrace (prefixWord ++ tailWord_7337337) baseStart_7337337 baseEnd_7337337 := by
    simpa [prefixWord, tailWord_7337337, baseEnd_7337337] using wordTrace_append hprefix tailTrace_7337337
  have hstable : (prefixWord ++ tailWord_7337337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337337).length < 2 ^ (prefixWord ++ tailWord_7337337).sum := by decide
  have hdescent : baseEnd_7337337 < baseStart_7337337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337348 : List Nat := [2, 3, 2, 1, 1, 4, 3, 1, 1, 1, 4]
def baseStart_7337348 : Nat := 118140960795 + 7337348 * 2 ^ 59
def prefixEnd_7337348 : Nat := 4983230072969 + 3 ^ 40 * 7337348 * 2
def baseEnd_7337348 : Nat := 3767586253305663825906157

theorem tailTrace_7337348 : CollatzResearch.WordTrace tailWord_7337348 prefixEnd_7337348 3767586253305663825906157 := by
  unfold tailWord_7337348
  simp only [CollatzResearch.WordTrace]
  refine ⟨133807533511024395058794349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178410044681365860078392465 133807533511024395058794349)
  ·
    refine ⟨50177825066634148147047881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133807533511024395058794349 50177825066634148147047881)
    ·
      refine ⟨37633368799975611110285911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50177825066634148147047881 37633368799975611110285911)
      ·
        refine ⟨56450053199963416665428867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37633368799975611110285911 56450053199963416665428867)
        ·
          refine ⟨84675079799945124998143301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56450053199963416665428867 84675079799945124998143301)
          ·
            refine ⟨15876577462489710937151869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84675079799945124998143301 15876577462489710937151869)
            ·
              refine ⟨5953716548433641601431951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15876577462489710937151869 5953716548433641601431951)
              ·
                refine ⟨8930574822650462402147927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5953716548433641601431951 8930574822650462402147927)
                ·
                  refine ⟨13395862233975693603221891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8930574822650462402147927 13395862233975693603221891)
                  ·
                    refine ⟨20093793350963540404832837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13395862233975693603221891 20093793350963540404832837)
                    ·
                      refine ⟨3767586253305663825906157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20093793350963540404832837 3767586253305663825906157)
                      ·
                        rfl

theorem cell23_7337348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 1, 1, 4].length) (baseStart_7337348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337348 prefixEnd_7337348 := by exact prefixLift 7337348
  have htrace : WordTrace (prefixWord ++ tailWord_7337348) baseStart_7337348 baseEnd_7337348 := by
    simpa [prefixWord, tailWord_7337348, baseEnd_7337348] using wordTrace_append hprefix tailTrace_7337348
  have hstable : (prefixWord ++ tailWord_7337348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337348).length < 2 ^ (prefixWord ++ tailWord_7337348).sum := by decide
  have hdescent : baseEnd_7337348 < baseStart_7337348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337351 : List Nat := [1, 1, 4, 2, 2, 4, 1, 1, 1, 1, 5]
def baseStart_7337351 : Nat := 118140960795 + 7337351 * 2 ^ 59
def prefixEnd_7337351 : Nat := 4983230072969 + 3 ^ 40 * 7337351 * 2
def baseEnd_7337351 : Nat := 3767587793747627314168643

theorem tailTrace_7337351 : CollatzResearch.WordTrace tailWord_7337351 prefixEnd_7337351 3767587793747627314168643 := by
  unfold tailWord_7337351
  simp only [CollatzResearch.WordTrace]
  refine ⟨267615176441037921629947907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178410117627358614419965271 267615176441037921629947907)
  ·
    refine ⟨401422764661556882444921861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267615176441037921629947907 401422764661556882444921861)
    ·
      refine ⟨75266768374041915458422849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401422764661556882444921861 75266768374041915458422849)
      ·
        refine ⟨56450076280531436593817137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75266768374041915458422849 56450076280531436593817137)
        ·
          refine ⟨42337557210398577445362853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56450076280531436593817137 42337557210398577445362853)
          ·
            refine ⟨7938291976949733271005535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42337557210398577445362853 7938291976949733271005535)
            ·
              refine ⟨11907437965424599906508303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7938291976949733271005535 11907437965424599906508303)
              ·
                refine ⟨17861156948136899859762455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11907437965424599906508303 17861156948136899859762455)
                ·
                  refine ⟨26791735422205349789643683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17861156948136899859762455 26791735422205349789643683)
                  ·
                    refine ⟨40187603133308024684465525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26791735422205349789643683 40187603133308024684465525)
                    ·
                      refine ⟨3767587793747627314168643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40187603133308024684465525 3767587793747627314168643)
                      ·
                        rfl

theorem cell23_7337351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_7337351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337351 prefixEnd_7337351 := by exact prefixLift 7337351
  have htrace : WordTrace (prefixWord ++ tailWord_7337351) baseStart_7337351 baseEnd_7337351 := by
    simpa [prefixWord, tailWord_7337351, baseEnd_7337351] using wordTrace_append hprefix tailTrace_7337351
  have hstable : (prefixWord ++ tailWord_7337351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337351).length < 2 ^ (prefixWord ++ tailWord_7337351).sum := by decide
  have hdescent : baseEnd_7337351 < baseStart_7337351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337481 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 2, 5, 2]
def baseStart_7337481 : Nat := 118140960795 + 7337481 * 2 ^ 59
def prefixEnd_7337481 : Nat := 4983230072969 + 3 ^ 40 * 7337481 * 2
def baseEnd_7337481 : Nat := 3767654546232711805543045

theorem tailTrace_7337481 : CollatzResearch.WordTrace tailWord_7337481 prefixEnd_7337481 3767654546232711805543045 := by
  unfold tailWord_7337481
  simp only [CollatzResearch.WordTrace]
  refine ⟨267619917930566953832180297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178413278620377969221453531 267619917930566953832180297)
  ·
    refine ⟨200714938447925215374135223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267619917930566953832180297 200714938447925215374135223)
    ·
      refine ⟨301072407671887823061202835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200714938447925215374135223 301072407671887823061202835)
      ·
        refine ⟨451608611507831734591804253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301072407671887823061202835 451608611507831734591804253)
        ·
          refine ⟨169353229315436900471926595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451608611507831734591804253 169353229315436900471926595)
          ·
            refine ⟨254029843973155350707889893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169353229315436900471926595 254029843973155350707889893)
            ·
              refine ⟨47630595744966628257729355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254029843973155350707889893 47630595744966628257729355)
              ·
                refine ⟨71445893617449942386594033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47630595744966628257729355 71445893617449942386594033)
                ·
                  refine ⟨53584420213087456789945525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71445893617449942386594033 53584420213087456789945525)
                  ·
                    refine ⟨5023539394976949074057393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53584420213087456789945525 5023539394976949074057393)
                    ·
                      refine ⟨3767654546232711805543045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5023539394976949074057393 3767654546232711805543045)
                      ·
                        rfl

theorem cell23_7337481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 2, 5, 2].length) (baseStart_7337481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337481 prefixEnd_7337481 := by exact prefixLift 7337481
  have htrace : WordTrace (prefixWord ++ tailWord_7337481) baseStart_7337481 baseEnd_7337481 := by
    simpa [prefixWord, tailWord_7337481, baseEnd_7337481] using wordTrace_append hprefix tailTrace_7337481
  have hstable : (prefixWord ++ tailWord_7337481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337481).length < 2 ^ (prefixWord ++ tailWord_7337481).sum := by decide
  have hdescent : baseEnd_7337481 < baseStart_7337481 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337595 : List Nat := [1, 1, 1, 1, 1, 4, 3, 6, 1, 1, 3]
def baseStart_7337595 : Nat := 118140960795 + 7337595 * 2 ^ 59
def prefixEnd_7337595 : Nat := 4983230072969 + 3 ^ 40 * 7337595 * 2
def baseEnd_7337595 : Nat := 3767713083027324359517521

theorem tailTrace_7337595 : CollatzResearch.WordTrace tailWord_7337595 prefixEnd_7337595 3767713083027324359517521 := by
  unfold tailWord_7337595
  simp only [CollatzResearch.WordTrace]
  refine ⟨267624075852153951301830239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178416050568102634201220159 267624075852153951301830239)
  ·
    refine ⟨401436113778230926952745359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267624075852153951301830239 401436113778230926952745359)
    ·
      refine ⟨602154170667346390429118039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401436113778230926952745359 602154170667346390429118039)
      ·
        refine ⟨903231256001019585643677059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602154170667346390429118039 903231256001019585643677059)
        ·
          refine ⟨1354846884001529378465515589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903231256001019585643677059 1354846884001529378465515589)
          ·
            refine ⟨254033790750286758462284173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1354846884001529378465515589 254033790750286758462284173)
            ·
              refine ⟨95262671531357534423356565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254033790750286758462284173 95262671531357534423356565)
              ·
                refine ⟨4465437728032384426094839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95262671531357534423356565 4465437728032384426094839)
                ·
                  refine ⟨6698156592048576639142259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4465437728032384426094839 6698156592048576639142259)
                  ·
                    refine ⟨10047234888072864958713389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6698156592048576639142259 10047234888072864958713389)
                    ·
                      refine ⟨3767713083027324359517521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10047234888072864958713389 3767713083027324359517521)
                      ·
                        rfl

theorem cell23_7337595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 6, 1, 1, 3].length) (baseStart_7337595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337595 prefixEnd_7337595 := by exact prefixLift 7337595
  have htrace : WordTrace (prefixWord ++ tailWord_7337595) baseStart_7337595 baseEnd_7337595 := by
    simpa [prefixWord, tailWord_7337595, baseEnd_7337595] using wordTrace_append hprefix tailTrace_7337595
  have hstable : (prefixWord ++ tailWord_7337595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337595).length < 2 ^ (prefixWord ++ tailWord_7337595).sum := by decide
  have hdescent : baseEnd_7337595 < baseStart_7337595 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337621 : List Nat := [1, 3, 2, 1, 1, 1, 1, 2, 2, 6, 3]
def baseStart_7337621 : Nat := 118140960795 + 7337621 * 2 ^ 59
def prefixEnd_7337621 : Nat := 4983230072969 + 3 ^ 40 * 7337621 * 2
def baseEnd_7337621 : Nat := 3767726433524341257792401

theorem tailTrace_7337621 : CollatzResearch.WordTrace tailWord_7337621 prefixEnd_7337621 3767726433524341257792401 := by
  unfold tailWord_7337621
  simp only [CollatzResearch.WordTrace]
  refine ⟨267625024150059757742276717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178416682766706505161517811 267625024150059757742276717)
  ·
    refine ⟨100359384056272409153353769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267625024150059757742276717 100359384056272409153353769)
    ·
      refine ⟨75269538042204306865015327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100359384056272409153353769 75269538042204306865015327)
      ·
        refine ⟨112904307063306460297522991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75269538042204306865015327 112904307063306460297522991)
        ·
          refine ⟨169356460594959690446284487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112904307063306460297522991 169356460594959690446284487)
          ·
            refine ⟨254034690892439535669426731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169356460594959690446284487 254034690892439535669426731)
            ·
              refine ⟨381052036338659303504140097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254034690892439535669426731 381052036338659303504140097)
              ·
                refine ⟨285789027253994477628105073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381052036338659303504140097 285789027253994477628105073)
                ·
                  refine ⟨214341770440495858221078805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285789027253994477628105073 214341770440495858221078805)
                  ·
                    refine ⟨10047270489398243354113069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 214341770440495858221078805 10047270489398243354113069)
                    ·
                      refine ⟨3767726433524341257792401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10047270489398243354113069 3767726433524341257792401)
                      ·
                        rfl

theorem cell23_7337621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 6, 3].length) (baseStart_7337621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337621 prefixEnd_7337621 := by exact prefixLift 7337621
  have htrace : WordTrace (prefixWord ++ tailWord_7337621) baseStart_7337621 baseEnd_7337621 := by
    simpa [prefixWord, tailWord_7337621, baseEnd_7337621] using wordTrace_append hprefix tailTrace_7337621
  have hstable : (prefixWord ++ tailWord_7337621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337621).length < 2 ^ (prefixWord ++ tailWord_7337621).sum := by decide
  have hdescent : baseEnd_7337621 < baseStart_7337621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337645 : List Nat := [1, 5, 2, 1, 1, 1, 2, 4, 2, 4]
def baseStart_7337645 : Nat := 118140960795 + 7337645 * 2 ^ 59
def prefixEnd_7337645 : Nat := 4983230072969 + 3 ^ 40 * 7337645 * 2
def baseEnd_7337645 : Nat := 1255912919020016387964097

theorem tailTrace_7337645 : CollatzResearch.WordTrace tailWord_7337645 prefixEnd_7337645 1255912919020016387964097 := by
  unfold tailWord_7337645
  simp only [CollatzResearch.WordTrace]
  refine ⟨267625899501972809841150389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178417266334648539894100259 267625899501972809841150389)
  ·
    refine ⟨25089928078309950922607849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267625899501972809841150389 25089928078309950922607849)
    ·
      refine ⟨18817446058732463191955887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25089928078309950922607849 18817446058732463191955887)
      ·
        refine ⟨28226169088098694787933831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18817446058732463191955887 28226169088098694787933831)
        ·
          refine ⟨42339253632148042181900747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28226169088098694787933831 42339253632148042181900747)
          ·
            refine ⟨63508880448222063272851121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42339253632148042181900747 63508880448222063272851121)
            ·
              refine ⟨47631660336166547454638341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63508880448222063272851121 47631660336166547454638341)
              ·
                refine ⟨8930936313031227647744689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47631660336166547454638341 8930936313031227647744689)
                ·
                  refine ⟨6698202234773420735808517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8930936313031227647744689 6698202234773420735808517)
                  ·
                    refine ⟨1255912919020016387964097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6698202234773420735808517 1255912919020016387964097)
                    ·
                      rfl

theorem cell23_7337645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_7337645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337645 prefixEnd_7337645 := by exact prefixLift 7337645
  have htrace : WordTrace (prefixWord ++ tailWord_7337645) baseStart_7337645 baseEnd_7337645 := by
    simpa [prefixWord, tailWord_7337645, baseEnd_7337645] using wordTrace_append hprefix tailTrace_7337645
  have hstable : (prefixWord ++ tailWord_7337645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337645).length < 2 ^ (prefixWord ++ tailWord_7337645).sum := by decide
  have hdescent : baseEnd_7337645 < baseStart_7337645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337646 : List Nat := [4, 1, 4, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_7337646 : Nat := 118140960795 + 7337646 * 2 ^ 59
def prefixEnd_7337646 : Nat := 4983230072969 + 3 ^ 40 * 7337646 * 2
def baseEnd_7337646 : Nat := 3767739270540703659979787

theorem tailTrace_7337646 : CollatzResearch.WordTrace tailWord_7337646 prefixEnd_7337646 3767739270540703659979787 := by
  unfold tailWord_7337646
  simp only [CollatzResearch.WordTrace]
  refine ⟨33453241996871148376492099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178417290649979458007957861 33453241996871148376492099)
  ·
    refine ⟨50179862995306722564738149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33453241996871148376492099 50179862995306722564738149)
    ·
      refine ⟨9408724311620010480888403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50179862995306722564738149 9408724311620010480888403)
      ·
        refine ⟨14113086467430015721332605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9408724311620010480888403 14113086467430015721332605)
        ·
          refine ⟨5292407425286255895499727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14113086467430015721332605 5292407425286255895499727)
          ·
            refine ⟨7938611137929383843249591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5292407425286255895499727 7938611137929383843249591)
            ·
              refine ⟨11907916706894075764874387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7938611137929383843249591 11907916706894075764874387)
              ·
                refine ⟨17861875060341113647311581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11907916706894075764874387 17861875060341113647311581)
                ·
                  refine ⟨6698203147627917617741843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17861875060341113647311581 6698203147627917617741843)
                  ·
                    refine ⟨10047304721441876426612765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6698203147627917617741843 10047304721441876426612765)
                    ·
                      refine ⟨3767739270540703659979787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10047304721441876426612765 3767739270540703659979787)
                      ·
                        rfl

theorem cell23_7337646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_7337646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337646 prefixEnd_7337646 := by exact prefixLift 7337646
  have htrace : WordTrace (prefixWord ++ tailWord_7337646) baseStart_7337646 baseEnd_7337646 := by
    simpa [prefixWord, tailWord_7337646, baseEnd_7337646] using wordTrace_append hprefix tailTrace_7337646
  have hstable : (prefixWord ++ tailWord_7337646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337646).length < 2 ^ (prefixWord ++ tailWord_7337646).sum := by decide
  have hdescent : baseEnd_7337646 < baseStart_7337646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337661 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 2, 2, 6]
def baseStart_7337661 : Nat := 118140960795 + 7337661 * 2 ^ 59
def prefixEnd_7337661 : Nat := 4983230072969 + 3 ^ 40 * 7337661 * 2
def baseEnd_7337661 : Nat := 3767746972750521101292217

theorem tailTrace_7337661 : CollatzResearch.WordTrace tailWord_7337661 prefixEnd_7337661 3767746972750521101292217 := by
  unfold tailWord_7337661
  simp only [CollatzResearch.WordTrace]
  refine ⟨267626483069914844573732837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178417655379943229715821891 267626483069914844573732837)
  ·
    refine ⟨50179965575609033357574907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267626483069914844573732837 50179965575609033357574907)
    ·
      refine ⟨75269948363413550036362361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50179965575609033357574907 75269948363413550036362361)
      ·
        refine ⟨56452461272560162527271771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75269948363413550036362361 56452461272560162527271771)
        ·
          refine ⟨84678691908840243790907657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56452461272560162527271771 84678691908840243790907657)
          ·
            refine ⟨63509018931630182843180743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84678691908840243790907657 63509018931630182843180743)
            ·
              refine ⟨95263528397445274264771115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63509018931630182843180743 95263528397445274264771115)
              ·
                refine ⟨142895292596167911397156673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95263528397445274264771115 142895292596167911397156673)
                ·
                  refine ⟨107171469447125933547867505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142895292596167911397156673 107171469447125933547867505)
                  ·
                    refine ⟨80378602085344450160900629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107171469447125933547867505 80378602085344450160900629)
                    ·
                      refine ⟨3767746972750521101292217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80378602085344450160900629 3767746972750521101292217)
                      ·
                        rfl

theorem cell23_7337661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_7337661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337661 prefixEnd_7337661 := by exact prefixLift 7337661
  have htrace : WordTrace (prefixWord ++ tailWord_7337661) baseStart_7337661 baseEnd_7337661 := by
    simpa [prefixWord, tailWord_7337661, baseEnd_7337661] using wordTrace_append hprefix tailTrace_7337661
  have hstable : (prefixWord ++ tailWord_7337661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337661).length < 2 ^ (prefixWord ++ tailWord_7337661).sum := by decide
  have hdescent : baseEnd_7337661 < baseStart_7337661 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337662 : List Nat := [4, 2, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_7337662 : Nat := 118140960795 + 7337662 * 2 ^ 59
def prefixEnd_7337662 : Nat := 4983230072969 + 3 ^ 40 * 7337662 * 2
def baseEnd_7337662 : Nat := 1255915828743725199126571

theorem tailTrace_7337662 : CollatzResearch.WordTrace tailWord_7337662 prefixEnd_7337662 1255915828743725199126571 := by
  unfold tailWord_7337662
  simp only [CollatzResearch.WordTrace]
  refine ⟨33453314942863902718064905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178417679695274147829679493 33453314942863902718064905)
  ·
    refine ⟨25089986207147927038548679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33453314942863902718064905 25089986207147927038548679)
    ·
      refine ⟨37634979310721890557823019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25089986207147927038548679 37634979310721890557823019)
      ·
        refine ⟨56452468966082835836734529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37634979310721890557823019 56452468966082835836734529)
        ·
          refine ⟨42339351724562126877550897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56452468966082835836734529 42339351724562126877550897)
          ·
            refine ⟨31754513793421595158163173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42339351724562126877550897 31754513793421595158163173)
            ·
              refine ⟨5953971336266549092155595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31754513793421595158163173 5953971336266549092155595)
              ·
                refine ⟨8930957004399823638233393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5953971336266549092155595 8930957004399823638233393)
                ·
                  refine ⟨6698217753299867728675045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8930957004399823638233393 6698217753299867728675045)
                  ·
                    refine ⟨1255915828743725199126571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6698217753299867728675045 1255915828743725199126571)
                    ·
                      rfl

theorem cell23_7337662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_7337662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337662 prefixEnd_7337662 := by exact prefixLift 7337662
  have htrace : WordTrace (prefixWord ++ tailWord_7337662) baseStart_7337662 baseEnd_7337662 := by
    simpa [prefixWord, tailWord_7337662, baseEnd_7337662] using wordTrace_append hprefix tailTrace_7337662
  have hstable : (prefixWord ++ tailWord_7337662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337662).length < 2 ^ (prefixWord ++ tailWord_7337662).sum := by decide
  have hdescent : baseEnd_7337662 < baseStart_7337662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337666 : List Nat := [3, 5, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_7337666 : Nat := 118140960795 + 7337666 * 2 ^ 59
def prefixEnd_7337666 : Nat := 4983230072969 + 3 ^ 40 * 7337666 * 2
def baseEnd_7337666 : Nat := 1255916513384597860576565

theorem tailTrace_7337666 : CollatzResearch.WordTrace tailWord_7337666 prefixEnd_7337666 1255916513384597860576565 := by
  unfold tailWord_7337666
  simp only [CollatzResearch.WordTrace]
  refine ⟨66906666358724182606916213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178417776956597820285109901 66906666358724182606916213)
  ·
    refine ⟨6272499971130392119398395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66906666358724182606916213 6272499971130392119398395)
    ·
      refine ⟨9408749956695588179097593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6272499971130392119398395 9408749956695588179097593)
      ·
        refine ⟨7056562467521691134323195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9408749956695588179097593 7056562467521691134323195)
        ·
          refine ⟨10584843701282536701484793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7056562467521691134323195 10584843701282536701484793)
          ·
            refine ⟨7938632775961902526113595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10584843701282536701484793 7938632775961902526113595)
            ·
              refine ⟨11907949163942853789170393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7938632775961902526113595 11907949163942853789170393)
              ·
                refine ⟨8930961872957140341877795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11907949163942853789170393 8930961872957140341877795)
                ·
                  refine ⟨13396442809435710512816693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8930961872957140341877795 13396442809435710512816693)
                  ·
                    refine ⟨1255916513384597860576565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13396442809435710512816693 1255916513384597860576565)
                    ·
                      rfl

theorem cell23_7337666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_7337666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337666 prefixEnd_7337666 := by exact prefixLift 7337666
  have htrace : WordTrace (prefixWord ++ tailWord_7337666) baseStart_7337666 baseEnd_7337666 := by
    simpa [prefixWord, tailWord_7337666, baseEnd_7337666] using wordTrace_append hprefix tailTrace_7337666
  have hstable : (prefixWord ++ tailWord_7337666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337666).length < 2 ^ (prefixWord ++ tailWord_7337666).sum := by decide
  have hdescent : baseEnd_7337666 < baseStart_7337666 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337686 : List Nat := [5, 2, 1, 3, 1, 1, 3, 1, 1, 1, 4]
def baseStart_7337686 : Nat := 118140960795 + 7337686 * 2 ^ 59
def prefixEnd_7337686 : Nat := 4983230072969 + 3 ^ 40 * 7337686 * 2
def baseEnd_7337686 : Nat := 3767759809766883503479603

theorem tailTrace_7337686 : CollatzResearch.WordTrace tailWord_7337686 prefixEnd_7337686 3767759809766883503479603 := by
  unfold tailWord_7337686
  simp only [CollatzResearch.WordTrace]
  refine ⟨16726712180926517115212057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178418263263216182562261941 16726712180926517115212057)
  ·
    refine ⟨12545034135694887836409043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16726712180926517115212057 12545034135694887836409043)
    ·
      refine ⟨18817551203542331754613565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12545034135694887836409043 18817551203542331754613565)
      ·
        refine ⟨7056581701328374407980087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18817551203542331754613565 7056581701328374407980087)
        ·
          refine ⟨10584872551992561611970131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7056581701328374407980087 10584872551992561611970131)
          ·
            refine ⟨15877308827988842417955197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10584872551992561611970131 15877308827988842417955197)
            ·
              refine ⟨5953990810495815906733199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15877308827988842417955197 5953990810495815906733199)
              ·
                refine ⟨8930986215743723860099799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5953990810495815906733199 8930986215743723860099799)
                ·
                  refine ⟨13396479323615585790149699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8930986215743723860099799 13396479323615585790149699)
                  ·
                    refine ⟨20094718985423378685224549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13396479323615585790149699 20094718985423378685224549)
                    ·
                      refine ⟨3767759809766883503479603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20094718985423378685224549 3767759809766883503479603)
                      ·
                        rfl

theorem cell23_7337686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_7337686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337686 prefixEnd_7337686 := by exact prefixLift 7337686
  have htrace : WordTrace (prefixWord ++ tailWord_7337686) baseStart_7337686 baseEnd_7337686 := by
    simpa [prefixWord, tailWord_7337686, baseEnd_7337686] using wordTrace_append hprefix tailTrace_7337686
  have hstable : (prefixWord ++ tailWord_7337686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337686).length < 2 ^ (prefixWord ++ tailWord_7337686).sum := by decide
  have hdescent : baseEnd_7337686 < baseStart_7337686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337718 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 1, 8]
def baseStart_7337718 : Nat := 118140960795 + 7337718 * 2 ^ 59
def prefixEnd_7337718 : Nat := 4983230072969 + 3 ^ 40 * 7337718 * 2
def baseEnd_7337718 : Nat := 1255925413715942459426485

theorem tailTrace_7337718 : CollatzResearch.WordTrace tailWord_7337718 prefixEnd_7337718 1255925413715942459426485 := by
  unfold tailWord_7337718
  simp only [CollatzResearch.WordTrace]
  refine ⟨16726785126919271456784863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178419041353805562205705205 16726785126919271456784863)
  ·
    refine ⟨25090177690378907185177295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16726785126919271456784863 25090177690378907185177295)
    ·
      refine ⟨37635266535568360777765943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25090177690378907185177295 37635266535568360777765943)
      ·
        refine ⟨56452899803352541166648915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37635266535568360777765943 56452899803352541166648915)
        ·
          refine ⟨84679349705028811749973373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56452899803352541166648915 84679349705028811749973373)
          ·
            refine ⟨31754756139385804406240015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84679349705028811749973373 31754756139385804406240015)
            ·
              refine ⟨47632134209078706609360023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31754756139385804406240015 47632134209078706609360023)
              ·
                refine ⟨71448201313618059914040035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47632134209078706609360023 71448201313618059914040035)
                ·
                  refine ⟨107172301970427089871060053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71448201313618059914040035 107172301970427089871060053)
                  ·
                    refine ⟨1255925413715942459426485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107172301970427089871060053 1255925413715942459426485)
                    ·
                      rfl

theorem cell23_7337718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_7337718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337718 prefixEnd_7337718 := by exact prefixLift 7337718
  have htrace : WordTrace (prefixWord ++ tailWord_7337718) baseStart_7337718 baseEnd_7337718 := by
    simpa [prefixWord, tailWord_7337718, baseEnd_7337718] using wordTrace_append hprefix tailTrace_7337718
  have hstable : (prefixWord ++ tailWord_7337718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337718).length < 2 ^ (prefixWord ++ tailWord_7337718).sum := by decide
  have hdescent : baseEnd_7337718 < baseStart_7337718 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337731 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 9]
def baseStart_7337731 : Nat := 118140960795 + 7337731 * 2 ^ 59
def prefixEnd_7337731 : Nat := 4983230072969 + 3 ^ 40 * 7337731 * 2
def baseEnd_7337731 : Nat := 418642546266259536379655

theorem tailTrace_7337731 : CollatzResearch.WordTrace tailWord_7337731 prefixEnd_7337731 418642546266259536379655 := by
  unfold tailWord_7337731
  simp only [CollatzResearch.WordTrace]
  refine ⟨267629036179661246528781047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178419357453107497685854031 267629036179661246528781047)
  ·
    refine ⟨401443554269491869793171571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267629036179661246528781047 401443554269491869793171571)
    ·
      refine ⟨602165331404237804689757357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401443554269491869793171571 602165331404237804689757357)
      ·
        refine ⟨225811999276589176758659009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 602165331404237804689757357 225811999276589176758659009)
        ·
          refine ⟨169358999457441882568994257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225811999276589176758659009 169358999457441882568994257)
          ·
            refine ⟨127019249593081411926745693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169358999457441882568994257 127019249593081411926745693)
            ·
              refine ⟨47632218597405529472529635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127019249593081411926745693 47632218597405529472529635)
              ·
                refine ⟨71448327896108294208794453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47632218597405529472529635 71448327896108294208794453)
                ·
                  refine ⟨418642546266259536379655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71448327896108294208794453 418642546266259536379655)
                  ·
                    rfl

theorem cell23_7337731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 9].length) (baseStart_7337731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337731 prefixEnd_7337731 := by exact prefixLift 7337731
  have htrace : WordTrace (prefixWord ++ tailWord_7337731) baseStart_7337731 baseEnd_7337731 := by
    simpa [prefixWord, tailWord_7337731, baseEnd_7337731] using wordTrace_append hprefix tailTrace_7337731
  have hstable : (prefixWord ++ tailWord_7337731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337731).length < 2 ^ (prefixWord ++ tailWord_7337731).sum := by decide
  have hdescent : baseEnd_7337731 < baseStart_7337731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337746 : List Nat := [3, 2, 4, 1, 1, 1, 4, 1, 1, 3, 2]
def baseStart_7337746 : Nat := 118140960795 + 7337746 * 2 ^ 59
def prefixEnd_7337746 : Nat := 4983230072969 + 3 ^ 40 * 7337746 * 2
def baseEnd_7337746 : Nat := 3767790618606153268729327

theorem tailTrace_7337746 : CollatzResearch.WordTrace tailWord_7337746 prefixEnd_7337746 3767790618606153268729327 := by
  unfold tailWord_7337746
  simp only [CollatzResearch.WordTrace]
  refine ⟨66907395818651726022644273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178419722183071269393718061 66907395818651726022644273)
  ·
    refine ⟨50180546863988794516983205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66907395818651726022644273 50180546863988794516983205)
    ·
      refine ⟨9408852536997898971934351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50180546863988794516983205 9408852536997898971934351)
      ·
        refine ⟨14113278805496848457901527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9408852536997898971934351 14113278805496848457901527)
        ·
          refine ⟨21169918208245272686852291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14113278805496848457901527 21169918208245272686852291)
          ·
            refine ⟨31754877312367909030278437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21169918208245272686852291 31754877312367909030278437)
            ·
              refine ⟨5954039496068982943177207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31754877312367909030278437 5954039496068982943177207)
              ·
                refine ⟨8931059244103474414765811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5954039496068982943177207 8931059244103474414765811)
                ·
                  refine ⟨13396588866155211622148717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8931059244103474414765811 13396588866155211622148717)
                  ·
                    refine ⟨5023720824808204358305769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13396588866155211622148717 5023720824808204358305769)
                    ·
                      refine ⟨3767790618606153268729327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5023720824808204358305769 3767790618606153268729327)
                      ·
                        rfl

theorem cell23_7337746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_7337746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337746 prefixEnd_7337746 := by exact prefixLift 7337746
  have htrace : WordTrace (prefixWord ++ tailWord_7337746) baseStart_7337746 baseEnd_7337746 := by
    simpa [prefixWord, tailWord_7337746, baseEnd_7337746] using wordTrace_append hprefix tailTrace_7337746
  have hstable : (prefixWord ++ tailWord_7337746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337746).length < 2 ^ (prefixWord ++ tailWord_7337746).sum := by decide
  have hdescent : baseEnd_7337746 < baseStart_7337746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337765 : List Nat := [1, 3, 1, 2, 3, 2, 2, 4, 5]
def baseStart_7337765 : Nat := 118140960795 + 7337765 * 2 ^ 59
def prefixEnd_7337765 : Nat := 4983230072969 + 3 ^ 40 * 7337765 * 2
def baseEnd_7337765 : Nat := 418644486082065410487971

theorem tailTrace_7337765 : CollatzResearch.WordTrace tailWord_7337765 prefixEnd_7337765 418644486082065410487971 := by
  unfold tailWord_7337765
  simp only [CollatzResearch.WordTrace]
  refine ⟨267630276261538070335518749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178420184174358713557012499 267630276261538070335518749)
  ·
    refine ⟨100361353598076776375819531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267630276261538070335518749 100361353598076776375819531)
    ·
      refine ⟨150542030397115164563729297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100361353598076776375819531 150542030397115164563729297)
      ·
        refine ⟨112906522797836373422796973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150542030397115164563729297 112906522797836373422796973)
        ·
          refine ⟨42339946049188640033548865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112906522797836373422796973 42339946049188640033548865)
          ·
            refine ⟨31754959536891480025161649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42339946049188640033548865 31754959536891480025161649)
            ·
              refine ⟨23816219652668610018871237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31754959536891480025161649 23816219652668610018871237)
              ·
                refine ⟨4465541184875364378538357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23816219652668610018871237 4465541184875364378538357)
                ·
                  refine ⟨418644486082065410487971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4465541184875364378538357 418644486082065410487971)
                  ·
                    rfl

theorem cell23_7337765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 5].length) (baseStart_7337765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337765 prefixEnd_7337765 := by exact prefixLift 7337765
  have htrace : WordTrace (prefixWord ++ tailWord_7337765) baseStart_7337765 baseEnd_7337765 := by
    simpa [prefixWord, tailWord_7337765, baseEnd_7337765] using wordTrace_append hprefix tailTrace_7337765
  have hstable : (prefixWord ++ tailWord_7337765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337765).length < 2 ^ (prefixWord ++ tailWord_7337765).sum := by decide
  have hdescent : baseEnd_7337765 < baseStart_7337765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337778 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 1, 7]
def baseStart_7337778 : Nat := 118140960795 + 7337778 * 2 ^ 59
def prefixEnd_7337778 : Nat := 4983230072969 + 3 ^ 40 * 7337778 * 2
def baseEnd_7337778 : Nat := 1255935683329032381176393

theorem tailTrace_7337778 : CollatzResearch.WordTrace tailWord_7337778 prefixEnd_7337778 1255935683329032381176393 := by
  unfold tailWord_7337778
  simp only [CollatzResearch.WordTrace]
  refine ⟨66907687602622743388935497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178420500273660649037161325 66907687602622743388935497)
  ·
    refine ⟨50180765701967057541701623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66907687602622743388935497 50180765701967057541701623)
    ·
      refine ⟨75271148552950586312552435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50180765701967057541701623 75271148552950586312552435)
      ·
        refine ⟨112906722829425879468828653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75271148552950586312552435 112906722829425879468828653)
        ·
          refine ⟨42340021061034704800810745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112906722829425879468828653 42340021061034704800810745)
          ·
            refine ⟨31755015795776028600608059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42340021061034704800810745 31755015795776028600608059)
            ·
              refine ⟨47632523693664042900912089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31755015795776028600608059 47632523693664042900912089)
              ·
                refine ⟨35724392770248032175684067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47632523693664042900912089 35724392770248032175684067)
                ·
                  refine ⟨53586589155372048263526101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35724392770248032175684067 53586589155372048263526101)
                  ·
                    refine ⟨1255935683329032381176393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53586589155372048263526101 1255935683329032381176393)
                    ·
                      rfl

theorem cell23_7337778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 1, 7].length) (baseStart_7337778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337778 prefixEnd_7337778 := by exact prefixLift 7337778
  have htrace : WordTrace (prefixWord ++ tailWord_7337778) baseStart_7337778 baseEnd_7337778 := by
    simpa [prefixWord, tailWord_7337778, baseEnd_7337778] using wordTrace_append hprefix tailTrace_7337778
  have hstable : (prefixWord ++ tailWord_7337778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337778).length < 2 ^ (prefixWord ++ tailWord_7337778).sum := by decide
  have hdescent : baseEnd_7337778 < baseStart_7337778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337876 : List Nat := [2, 4, 2, 1, 1, 2, 4, 2, 1, 4]
def baseStart_7337876 : Nat := 118140960795 + 7337876 * 2 ^ 59
def prefixEnd_7337876 : Nat := 4983230072969 + 3 ^ 40 * 7337876 * 2
def baseEnd_7337876 : Nat := 1255952457030412586701243

theorem tailTrace_7337876 : CollatzResearch.WordTrace tailWord_7337876 prefixEnd_7337876 1255952457030412586701243 := by
  unfold tailWord_7337876
  simp only [CollatzResearch.WordTrace]
  refine ⟨133817162382067968146404741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178422883176090624195206321 133817162382067968146404741)
  ·
    refine ⟨25090717946637744027450889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133817162382067968146404741 25090717946637744027450889)
    ·
      refine ⟨18818038459978308020588167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25090717946637744027450889 18818038459978308020588167)
      ·
        refine ⟨28227057689967462030882251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18818038459978308020588167 28227057689967462030882251)
        ·
          refine ⟨42340586534951193046323377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28227057689967462030882251 42340586534951193046323377)
          ·
            refine ⟨31755439901213394784742533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42340586534951193046323377 31755439901213394784742533)
            ·
              refine ⟨5954144981477511522139225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31755439901213394784742533 5954144981477511522139225)
              ·
                refine ⟨4465608736108133641604419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5954144981477511522139225 4465608736108133641604419)
                ·
                  refine ⟨6698413104162200462406629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4465608736108133641604419 6698413104162200462406629)
                  ·
                    refine ⟨1255952457030412586701243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6698413104162200462406629 1255952457030412586701243)
                    ·
                      rfl

theorem cell23_7337876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_7337876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337876 prefixEnd_7337876 := by exact prefixLift 7337876
  have htrace : WordTrace (prefixWord ++ tailWord_7337876) baseStart_7337876 baseEnd_7337876 := by
    simpa [prefixWord, tailWord_7337876, baseEnd_7337876] using wordTrace_append hprefix tailTrace_7337876
  have hstable : (prefixWord ++ tailWord_7337876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337876).length < 2 ^ (prefixWord ++ tailWord_7337876).sum := by decide
  have hdescent : baseEnd_7337876 < baseStart_7337876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337885 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 3, 5]
def baseStart_7337885 : Nat := 118140960795 + 7337885 * 2 ^ 59
def prefixEnd_7337885 : Nat := 4983230072969 + 3 ^ 40 * 7337885 * 2
def baseEnd_7337885 : Nat := 1255953997472376074963729

theorem tailTrace_7337885 : CollatzResearch.WordTrace tailWord_7337885 prefixEnd_7337885 1255953997472376074963729 := by
  unfold tailWord_7337885
  simp only [CollatzResearch.WordTrace]
  refine ⟨267634653021103330829887109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178423102014068887219924739 267634653021103330829887109)
  ·
    refine ⟨50181497441456874530603833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267634653021103330829887109 50181497441456874530603833)
    ·
      refine ⟨37636123081092655897952875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50181497441456874530603833 37636123081092655897952875)
      ·
        refine ⟨56454184621638983846929313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37636123081092655897952875 56454184621638983846929313)
        ·
          refine ⟨42340638466229237885196985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56454184621638983846929313 42340638466229237885196985)
          ·
            refine ⟨31755478849671928413897739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42340638466229237885196985 31755478849671928413897739)
            ·
              refine ⟨47633218274507892620846609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31755478849671928413897739 47633218274507892620846609)
              ·
                refine ⟨35724913705880919465634957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47633218274507892620846609 35724913705880919465634957)
                ·
                  refine ⟨13396842639705344799613109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35724913705880919465634957 13396842639705344799613109)
                  ·
                    refine ⟨1255953997472376074963729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13396842639705344799613109 1255953997472376074963729)
                    ·
                      rfl

theorem cell23_7337885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 5].length) (baseStart_7337885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337885 prefixEnd_7337885 := by exact prefixLift 7337885
  have htrace : WordTrace (prefixWord ++ tailWord_7337885) baseStart_7337885 baseEnd_7337885 := by
    simpa [prefixWord, tailWord_7337885, baseEnd_7337885] using wordTrace_append hprefix tailTrace_7337885
  have hstable : (prefixWord ++ tailWord_7337885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337885).length < 2 ^ (prefixWord ++ tailWord_7337885).sum := by decide
  have hdescent : baseEnd_7337885 < baseStart_7337885 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337909 : List Nat := [1, 3, 3, 2, 1, 2, 3, 1, 2, 3, 2]
def baseStart_7337909 : Nat := 118140960795 + 7337909 * 2 ^ 59
def prefixEnd_7337909 : Nat := 4983230072969 + 3 ^ 40 * 7337909 * 2
def baseEnd_7337909 : Nat := 3767874315952836130991077

theorem tailTrace_7337909 : CollatzResearch.WordTrace tailWord_7337909 prefixEnd_7337909 3767874315952836130991077 := by
  unfold tailWord_7337909
  simp only [CollatzResearch.WordTrace]
  refine ⟨267635528373016382928760781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178423685582010921952507187 267635528373016382928760781)
  ·
    refine ⟨100363323139881143598285293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267635528373016382928760781 100363323139881143598285293)
    ·
      refine ⟨37636246177455428849356985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100363323139881143598285293 37636246177455428849356985)
      ·
        refine ⟨28227184633091571637017739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37636246177455428849356985 28227184633091571637017739)
        ·
          refine ⟨42340776949637357455526609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28227184633091571637017739 42340776949637357455526609)
          ·
            refine ⟨31755582712228018091644957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42340776949637357455526609 31755582712228018091644957)
            ·
              refine ⟨11908343517085506784366859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31755582712228018091644957 11908343517085506784366859)
              ·
                refine ⟨17862515275628260176550289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11908343517085506784366859 17862515275628260176550289)
                ·
                  refine ⟨13396886456721195132412717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17862515275628260176550289 13396886456721195132412717)
                  ·
                    refine ⟨5023832421270448174654769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13396886456721195132412717 5023832421270448174654769)
                    ·
                      refine ⟨3767874315952836130991077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5023832421270448174654769 3767874315952836130991077)
                      ·
                        rfl

theorem cell23_7337909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_7337909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337909 prefixEnd_7337909 := by exact prefixLift 7337909
  have htrace : WordTrace (prefixWord ++ tailWord_7337909) baseStart_7337909 baseEnd_7337909 := by
    simpa [prefixWord, tailWord_7337909, baseEnd_7337909] using wordTrace_append hprefix tailTrace_7337909
  have hstable : (prefixWord ++ tailWord_7337909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337909).length < 2 ^ (prefixWord ++ tailWord_7337909).sum := by decide
  have hdescent : baseEnd_7337909 < baseStart_7337909 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337925 : List Nat := [1, 3, 1, 1, 1, 1, 1, 4, 5, 2, 3]
def baseStart_7337925 : Nat := 118140960795 + 7337925 * 2 ^ 59
def prefixEnd_7337925 : Nat := 4983230072969 + 3 ^ 40 * 7337925 * 2
def baseEnd_7337925 : Nat := 3767882531643308068391003

theorem tailTrace_7337925 : CollatzResearch.WordTrace tailWord_7337925 prefixEnd_7337925 3767882531643308068391003 := by
  unfold tailWord_7337925
  simp only [CollatzResearch.WordTrace]
  refine ⟨267636111940958417661343229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178424074627305611774228819 267636111940958417661343229)
  ·
    refine ⟨100363541977859406623003711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267636111940958417661343229 100363541977859406623003711)
    ·
      refine ⟨150545312966789109934505567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100363541977859406623003711 150545312966789109934505567)
      ·
        refine ⟨225817969450183664901758351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150545312966789109934505567 225817969450183664901758351)
        ·
          refine ⟨338726954175275497352637527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225817969450183664901758351 338726954175275497352637527)
          ·
            refine ⟨508090431262913246028956291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338726954175275497352637527 508090431262913246028956291)
            ·
              refine ⟨762135646894369869043434437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508090431262913246028956291 762135646894369869043434437)
              ·
                refine ⟨142900433792694350445643957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 762135646894369869043434437 142900433792694350445643957)
                ·
                  refine ⟨13396915668065095354279121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142900433792694350445643957 13396915668065095354279121)
                  ·
                    refine ⟨10047686751048821515709341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13396915668065095354279121 10047686751048821515709341)
                    ·
                      refine ⟨3767882531643308068391003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10047686751048821515709341 3767882531643308068391003)
                      ·
                        rfl

theorem cell23_7337925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 2, 3].length) (baseStart_7337925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337925 prefixEnd_7337925 := by exact prefixLift 7337925
  have htrace : WordTrace (prefixWord ++ tailWord_7337925) baseStart_7337925 baseEnd_7337925 := by
    simpa [prefixWord, tailWord_7337925, baseEnd_7337925] using wordTrace_append hprefix tailTrace_7337925
  have hstable : (prefixWord ++ tailWord_7337925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337925).length < 2 ^ (prefixWord ++ tailWord_7337925).sum := by decide
  have hdescent : baseEnd_7337925 < baseStart_7337925 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337932 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 4, 4]
def baseStart_7337932 : Nat := 118140960795 + 7337932 * 2 ^ 59
def prefixEnd_7337932 : Nat := 4983230072969 + 3 ^ 40 * 7337932 * 2
def baseEnd_7337932 : Nat := 1255962042002629847001157

theorem tailTrace_7337932 : CollatzResearch.WordTrace tailWord_7337932 prefixEnd_7337932 1255962042002629847001157 := by
  unfold tailWord_7337932
  simp only [CollatzResearch.WordTrace]
  refine ⟨133818183625966528928424025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178424244834622038571232033 133818183625966528928424025)
  ·
    refine ⟨100363637719474896696318019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133818183625966528928424025 100363637719474896696318019)
    ·
      refine ⟨150545456579212345044477029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100363637719474896696318019 150545456579212345044477029)
      ·
        refine ⟨28227273108602314695839443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150545456579212345044477029 28227273108602314695839443)
        ·
          refine ⟨42340909662903472043759165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28227273108602314695839443 42340909662903472043759165)
          ·
            refine ⟨15877841123588802016409687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42340909662903472043759165 15877841123588802016409687)
            ·
              refine ⟨23816761685383203024614531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15877841123588802016409687 23816761685383203024614531)
              ·
                refine ⟨35725142528074804536921797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23816761685383203024614531 35725142528074804536921797)
                ·
                  refine ⟨6698464224014025850672837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35725142528074804536921797 6698464224014025850672837)
                  ·
                    refine ⟨1255962042002629847001157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6698464224014025850672837 1255962042002629847001157)
                    ·
                      rfl

theorem cell23_7337932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 4, 4].length) (baseStart_7337932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337932 prefixEnd_7337932 := by exact prefixLift 7337932
  have htrace : WordTrace (prefixWord ++ tailWord_7337932) baseStart_7337932 baseEnd_7337932 := by
    simpa [prefixWord, tailWord_7337932, baseEnd_7337932] using wordTrace_append hprefix tailTrace_7337932
  have hstable : (prefixWord ++ tailWord_7337932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337932).length < 2 ^ (prefixWord ++ tailWord_7337932).sum := by decide
  have hdescent : baseEnd_7337932 < baseStart_7337932 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337949 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 1, 6]
def baseStart_7337949 : Nat := 118140960795 + 7337949 * 2 ^ 59
def prefixEnd_7337949 : Nat := 4983230072969 + 3 ^ 40 * 7337949 * 2
def baseEnd_7337949 : Nat := 1255964951726338658163631

theorem tailTrace_7337949 : CollatzResearch.WordTrace tailWord_7337949 prefixEnd_7337949 1255964951726338658163631 := by
  unfold tailWord_7337949
  simp only [CollatzResearch.WordTrace]
  refine ⟨267636987292871469760216901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178424658195247646506811267 267636987292871469760216901)
  ·
    refine ⟨50181935117413400580040669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267636987292871469760216901 50181935117413400580040669)
    ·
      refine ⟨18818225669030025217515251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50181935117413400580040669 18818225669030025217515251)
      ·
        refine ⟨28227338503545037826272877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18818225669030025217515251 28227338503545037826272877)
        ·
          refine ⟨10585251938829389184852329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28227338503545037826272877 10585251938829389184852329)
          ·
            refine ⟨7938938954122041888639247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10585251938829389184852329 7938938954122041888639247)
            ·
              refine ⟨11908408431183062832958871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7938938954122041888639247 11908408431183062832958871)
              ·
                refine ⟨17862612646774594249438307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11908408431183062832958871 17862612646774594249438307)
                ·
                  refine ⟨26793918970161891374157461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17862612646774594249438307 26793918970161891374157461)
                  ·
                    refine ⟨1255964951726338658163631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26793918970161891374157461 1255964951726338658163631)
                    ·
                      rfl

theorem cell23_7337949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_7337949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337949 prefixEnd_7337949 := by exact prefixLift 7337949
  have htrace : WordTrace (prefixWord ++ tailWord_7337949) baseStart_7337949 baseEnd_7337949 := by
    simpa [prefixWord, tailWord_7337949, baseEnd_7337949] using wordTrace_append hprefix tailTrace_7337949
  have hstable : (prefixWord ++ tailWord_7337949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337949).length < 2 ^ (prefixWord ++ tailWord_7337949).sum := by decide
  have hdescent : baseEnd_7337949 < baseStart_7337949 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337985 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_7337985 : Nat := 118140960795 + 7337985 * 2 ^ 59
def prefixEnd_7337985 : Nat := 4983230072969 + 3 ^ 40 * 7337985 * 2
def baseEnd_7337985 : Nat := 3767913340482577833640727

theorem tailTrace_7337985 : CollatzResearch.WordTrace tailWord_7337985 prefixEnd_7337985 3767913340482577833640727 := by
  unfold tailWord_7337985
  simp only [CollatzResearch.WordTrace]
  refine ⟨267638300320741047908527409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178425533547160698605684939 267638300320741047908527409)
  ·
    refine ⟨200728725240555785931395557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267638300320741047908527409 200728725240555785931395557)
    ·
      refine ⟨37636635982604209862136667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200728725240555785931395557 37636635982604209862136667)
      ·
        refine ⟨56454953973906314793205001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37636635982604209862136667 56454953973906314793205001)
        ·
          refine ⟨42341215480429736094903751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56454953973906314793205001 42341215480429736094903751)
          ·
            refine ⟨63511823220644604142355627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42341215480429736094903751 63511823220644604142355627)
            ·
              refine ⟨95267734830966906213533441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63511823220644604142355627 95267734830966906213533441)
              ·
                refine ⟨71450801123225179660150081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95267734830966906213533441 71450801123225179660150081)
                ·
                  refine ⟨53588100842418884745112561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71450801123225179660150081 53588100842418884745112561)
                  ·
                    refine ⟨40191075631814163558834421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53588100842418884745112561 40191075631814163558834421)
                    ·
                      refine ⟨3767913340482577833640727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40191075631814163558834421 3767913340482577833640727)
                      ·
                        rfl

theorem cell23_7337985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_7337985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337985 prefixEnd_7337985 := by exact prefixLift 7337985
  have htrace : WordTrace (prefixWord ++ tailWord_7337985) baseStart_7337985 baseEnd_7337985 := by
    simpa [prefixWord, tailWord_7337985, baseEnd_7337985] using wordTrace_append hprefix tailTrace_7337985
  have hstable : (prefixWord ++ tailWord_7337985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337985).length < 2 ^ (prefixWord ++ tailWord_7337985).sum := by decide
  have hdescent : baseEnd_7337985 < baseStart_7337985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7337995 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 4]
def baseStart_7337995 : Nat := 118140960795 + 7337995 * 2 ^ 59
def prefixEnd_7337995 : Nat := 4983230072969 + 3 ^ 40 * 7337995 * 2
def baseEnd_7337995 : Nat := 3767918475289122794515681

theorem tailTrace_7337995 : CollatzResearch.WordTrace tailWord_7337995 prefixEnd_7337995 3767918475289122794515681 := by
  unfold tailWord_7337995
  simp only [CollatzResearch.WordTrace]
  refine ⟨267638665050704819616391439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178425776700469879744260959 267638665050704819616391439)
  ·
    refine ⟨401457997576057229424587159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267638665050704819616391439 401457997576057229424587159)
    ·
      refine ⟨602186996364085844136880739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401457997576057229424587159 602186996364085844136880739)
      ·
        refine ⟨903280494546128766205321109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602186996364085844136880739 903280494546128766205321109)
        ·
          refine ⟨42341273181849785915874427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 903280494546128766205321109 42341273181849785915874427)
          ·
            refine ⟨63511909772774678873811641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42341273181849785915874427 63511909772774678873811641)
            ·
              refine ⟨47633932329581009155358731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63511909772774678873811641 47633932329581009155358731)
              ·
                refine ⟨71450898494371513733038097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47633932329581009155358731 71450898494371513733038097)
                ·
                  refine ⟨53588173870778635299778573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71450898494371513733038097 53588173870778635299778573)
                  ·
                    refine ⟨20095565201541988237416965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53588173870778635299778573 20095565201541988237416965)
                    ·
                      refine ⟨3767918475289122794515681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20095565201541988237416965 3767918475289122794515681)
                      ·
                        rfl

theorem cell23_7337995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 2, 3, 4].length) (baseStart_7337995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7337995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7337995 prefixEnd_7337995 := by exact prefixLift 7337995
  have htrace : WordTrace (prefixWord ++ tailWord_7337995) baseStart_7337995 baseEnd_7337995 := by
    simpa [prefixWord, tailWord_7337995, baseEnd_7337995] using wordTrace_append hprefix tailTrace_7337995
  have hstable : (prefixWord ++ tailWord_7337995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7337995).length < 2 ^ (prefixWord ++ tailWord_7337995).sum := by decide
  have hdescent : baseEnd_7337995 < baseStart_7337995 := by decide
  rcases family_descends (prefixWord ++ tailWord_7337995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338015 : List Nat := [1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 5]
def baseStart_7338015 : Nat := 118140960795 + 7338015 * 2 ^ 59
def prefixEnd_7338015 : Nat := 4983230072969 + 3 ^ 40 * 7338015 * 2
def baseEnd_7338015 : Nat := 3767928744902212716265589

theorem tailTrace_7338015 : CollatzResearch.WordTrace tailWord_7338015 prefixEnd_7338015 3767928744902212716265589 := by
  unfold tailWord_7338015
  simp only [CollatzResearch.WordTrace]
  refine ⟨267639394510632363032119499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178426263007088242021412999 267639394510632363032119499)
  ·
    refine ⟨401459091765948544548179249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267639394510632363032119499 401459091765948544548179249)
    ·
      refine ⟨301094318824461408411134437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401459091765948544548179249 301094318824461408411134437)
      ·
        refine ⟨56455184779586514077087707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301094318824461408411134437 56455184779586514077087707)
        ·
          refine ⟨84682777169379771115631561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56455184779586514077087707 84682777169379771115631561)
          ·
            refine ⟨63512082877034828336723671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84682777169379771115631561 63512082877034828336723671)
            ·
              refine ⟨95268124315552242505085507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63512082877034828336723671 95268124315552242505085507)
              ·
                refine ⟨142902186473328363757628261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95268124315552242505085507 142902186473328363757628261)
                ·
                  refine ⟨26794159963749068204555299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142902186473328363757628261 26794159963749068204555299)
                  ·
                    refine ⟨40191239945623602306832949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26794159963749068204555299 40191239945623602306832949)
                    ·
                      refine ⟨3767928744902212716265589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40191239945623602306832949 3767928744902212716265589)
                      ·
                        rfl

theorem cell23_7338015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_7338015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338015 prefixEnd_7338015 := by exact prefixLift 7338015
  have htrace : WordTrace (prefixWord ++ tailWord_7338015) baseStart_7338015 baseEnd_7338015 := by
    simpa [prefixWord, tailWord_7338015, baseEnd_7338015] using wordTrace_append hprefix tailTrace_7338015
  have hstable : (prefixWord ++ tailWord_7338015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338015).length < 2 ^ (prefixWord ++ tailWord_7338015).sum := by decide
  have hdescent : baseEnd_7338015 < baseStart_7338015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338062 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3]
def baseStart_7338062 : Nat := 118140960795 + 7338062 * 2 ^ 59
def prefixEnd_7338062 : Nat := 4983230072969 + 3 ^ 40 * 7338062 * 2
def baseEnd_7338062 : Nat := 3767952878492974032377873

theorem tailTrace_7338062 : CollatzResearch.WordTrace tailWord_7338062 prefixEnd_7338062 3767952878492974032377873 := by
  unfold tailWord_7338062
  simp only [CollatzResearch.WordTrace]
  refine ⟨33455138592682761257385055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178427405827641393372720293 33455138592682761257385055)
  ·
    refine ⟨50182707889024141886077583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33455138592682761257385055 50182707889024141886077583)
    ·
      refine ⟨75274061833536212829116375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50182707889024141886077583 75274061833536212829116375)
      ·
        refine ⟨112911092750304319243674563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75274061833536212829116375 112911092750304319243674563)
        ·
          refine ⟨169366639125456478865511845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112911092750304319243674563 169366639125456478865511845)
          ·
            refine ⟨31756244836023089787283471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169366639125456478865511845 31756244836023089787283471)
            ·
              refine ⟨47634367254034634680925207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31756244836023089787283471 47634367254034634680925207)
              ·
                refine ⟨71451550881051952021387811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47634367254034634680925207 71451550881051952021387811)
                ·
                  refine ⟨107177326321577928032081717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71451550881051952021387811 107177326321577928032081717)
                  ·
                    refine ⟨10047874342647930753007661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107177326321577928032081717 10047874342647930753007661)
                    ·
                      refine ⟨3767952878492974032377873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10047874342647930753007661 3767952878492974032377873)
                      ·
                        rfl

theorem cell23_7338062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_7338062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338062 prefixEnd_7338062 := by exact prefixLift 7338062
  have htrace : WordTrace (prefixWord ++ tailWord_7338062) baseStart_7338062 baseEnd_7338062 := by
    simpa [prefixWord, tailWord_7338062, baseEnd_7338062] using wordTrace_append hprefix tailTrace_7338062
  have hstable : (prefixWord ++ tailWord_7338062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338062).length < 2 ^ (prefixWord ++ tailWord_7338062).sum := by decide
  have hdescent : baseEnd_7338062 < baseStart_7338062 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338065 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 1, 7]
def baseStart_7338065 : Nat := 118140960795 + 7338065 * 2 ^ 59
def prefixEnd_7338065 : Nat := 4983230072969 + 3 ^ 40 * 7338065 * 2
def baseEnd_7338065 : Nat := 1255984806311645840213453

theorem tailTrace_7338065 : CollatzResearch.WordTrace tailWord_7338065 prefixEnd_7338065 1255984806311645840213453 := by
  unfold tailWord_7338065
  simp only [CollatzResearch.WordTrace]
  refine ⟨267641218160451221571439649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178427478773634147714293099 267641218160451221571439649)
  ·
    refine ⟨200730913620338416178579737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267641218160451221571439649 200730913620338416178579737)
    ·
      refine ⟨150548185215253812133934803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200730913620338416178579737 150548185215253812133934803)
      ·
        refine ⟨225822277822880718200902205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150548185215253812133934803 225822277822880718200902205)
        ·
          refine ⟨84683354183580269325338327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225822277822880718200902205 84683354183580269325338327)
          ·
            refine ⟨127025031275370403988007491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84683354183580269325338327 127025031275370403988007491)
            ·
              refine ⟨190537546913055605982011237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127025031275370403988007491 190537546913055605982011237)
              ·
                refine ⟨35725790046197926121627107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190537546913055605982011237 35725790046197926121627107)
                ·
                  refine ⟨53588685069296889182440661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35725790046197926121627107 53588685069296889182440661)
                  ·
                    refine ⟨1255984806311645840213453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53588685069296889182440661 1255984806311645840213453)
                    ·
                      rfl

theorem cell23_7338065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_7338065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338065 prefixEnd_7338065 := by exact prefixLift 7338065
  have htrace : WordTrace (prefixWord ++ tailWord_7338065) baseStart_7338065 baseEnd_7338065 := by
    simpa [prefixWord, tailWord_7338065, baseEnd_7338065] using wordTrace_append hprefix tailTrace_7338065
  have hstable : (prefixWord ++ tailWord_7338065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338065).length < 2 ^ (prefixWord ++ tailWord_7338065).sum := by decide
  have hdescent : baseEnd_7338065 < baseStart_7338065 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338119 : List Nat := [1, 1, 4, 2, 1, 1, 4, 1, 2, 4, 2]
def baseStart_7338119 : Nat := 118140960795 + 7338119 * 2 ^ 59
def prefixEnd_7338119 : Nat := 4983230072969 + 3 ^ 40 * 7338119 * 2
def baseEnd_7338119 : Nat := 3767982146890280309365111

theorem tailTrace_7338119 : CollatzResearch.WordTrace tailWord_7338119 prefixEnd_7338119 3767982146890280309365111 := by
  unfold tailWord_7338119
  simp only [CollatzResearch.WordTrace]
  refine ⟨267643187702255588793905411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178428791801503725862603607 267643187702255588793905411)
  ·
    refine ⟨401464781553383383190858117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267643187702255588793905411 401464781553383383190858117)
    ·
      refine ⟨75274646541259384348285897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401464781553383383190858117 75274646541259384348285897)
      ·
        refine ⟨56455984905944538261214423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75274646541259384348285897 56455984905944538261214423)
        ·
          refine ⟨84683977358916807391821635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56455984905944538261214423 84683977358916807391821635)
          ·
            refine ⟨127025966038375211087732453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84683977358916807391821635 127025966038375211087732453)
            ·
              refine ⟨23817368632195352078949835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127025966038375211087732453 23817368632195352078949835)
              ·
                refine ⟨35726052948293028118424753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23817368632195352078949835 35726052948293028118424753)
                ·
                  refine ⟨26794539711219771088818565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35726052948293028118424753 26794539711219771088818565)
                  ·
                    refine ⟨5023976195853707079153481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26794539711219771088818565 5023976195853707079153481)
                    ·
                      refine ⟨3767982146890280309365111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5023976195853707079153481 3767982146890280309365111)
                      ·
                        rfl

theorem cell23_7338119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_7338119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338119 prefixEnd_7338119 := by exact prefixLift 7338119
  have htrace : WordTrace (prefixWord ++ tailWord_7338119) baseStart_7338119 baseEnd_7338119 := by
    simpa [prefixWord, tailWord_7338119, baseEnd_7338119] using wordTrace_append hprefix tailTrace_7338119
  have hstable : (prefixWord ++ tailWord_7338119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338119).length < 2 ^ (prefixWord ++ tailWord_7338119).sum := by decide
  have hdescent : baseEnd_7338119 < baseStart_7338119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338155 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 3, 11]
def baseStart_7338155 : Nat := 118140960795 + 7338155 * 2 ^ 59
def prefixEnd_7338155 : Nat := 4983230072969 + 3 ^ 40 * 7338155 * 2
def baseEnd_7338155 : Nat := 1256000210731280722838315

theorem tailTrace_7338155 : CollatzResearch.WordTrace tailWord_7338155 prefixEnd_7338155 1256000210731280722838315 := by
  unfold tailWord_7338155
  simp only [CollatzResearch.WordTrace]
  refine ⟨267644500730125166942215919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178429667153416777961477279 267644500730125166942215919)
  ·
    refine ⟨401466751095187750413323879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267644500730125166942215919 401466751095187750413323879)
    ·
      refine ⟨602200126642781625619985819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401466751095187750413323879 602200126642781625619985819)
      ·
        refine ⟨903300189964172438429978729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602200126642781625619985819 903300189964172438429978729)
        ·
          refine ⟨677475142473129328822484047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903300189964172438429978729 677475142473129328822484047)
          ·
            refine ⟨1016212713709693993233726071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677475142473129328822484047 1016212713709693993233726071)
            ·
              refine ⟨1524319070564540989850589107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1016212713709693993233726071 1524319070564540989850589107)
              ·
                refine ⟨2286478605846811484775883661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1524319070564540989850589107 2286478605846811484775883661)
                ·
                  refine ⟨857429477192554306790956373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2286478605846811484775883661 857429477192554306790956373)
                  ·
                    refine ⟨1256000210731280722838315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 857429477192554306790956373 1256000210731280722838315)
                    ·
                      rfl

theorem cell23_7338155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 11].length) (baseStart_7338155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338155 prefixEnd_7338155 := by exact prefixLift 7338155
  have htrace : WordTrace (prefixWord ++ tailWord_7338155) baseStart_7338155 baseEnd_7338155 := by
    simpa [prefixWord, tailWord_7338155, baseEnd_7338155] using wordTrace_append hprefix tailTrace_7338155
  have hstable : (prefixWord ++ tailWord_7338155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338155).length < 2 ^ (prefixWord ++ tailWord_7338155).sum := by decide
  have hdescent : baseEnd_7338155 < baseStart_7338155 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338176 : List Nat := [2, 1, 1, 2, 5, 3, 2, 1, 6]
def baseStart_7338176 : Nat := 118140960795 + 7338176 * 2 ^ 59
def prefixEnd_7338176 : Nat := 4983230072969 + 3 ^ 40 * 7338176 * 2
def baseEnd_7338176 : Nat := 418667935031954065150261

theorem tailTrace_7338176 : CollatzResearch.WordTrace tailWord_7338176 prefixEnd_7338176 418667935031954065150261 := by
  unfold tailWord_7338176
  simp only [CollatzResearch.WordTrace]
  refine ⟨133822633331524543764365191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178430177775366058352486921 133822633331524543764365191)
  ·
    refine ⟨200733949997286815646547787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133822633331524543764365191 200733949997286815646547787)
    ·
      refine ⟨301100924995930223469821681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200733949997286815646547787 301100924995930223469821681)
      ·
        refine ⟨225825693746947667602366261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301100924995930223469821681 225825693746947667602366261)
        ·
          refine ⟨21171158788776343837721837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225825693746947667602366261 21171158788776343837721837)
          ·
            refine ⟨7939184545791128939145689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21171158788776343837721837 7939184545791128939145689)
            ·
              refine ⟨5954388409343346704359267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7939184545791128939145689 5954388409343346704359267)
              ·
                refine ⟨8931582614015020056538901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5954388409343346704359267 8931582614015020056538901)
                ·
                  refine ⟨418667935031954065150261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8931582614015020056538901 418667935031954065150261)
                  ·
                    rfl

theorem cell23_7338176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 6].length) (baseStart_7338176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338176 prefixEnd_7338176 := by exact prefixLift 7338176
  have htrace : WordTrace (prefixWord ++ tailWord_7338176) baseStart_7338176 baseEnd_7338176 := by
    simpa [prefixWord, tailWord_7338176, baseEnd_7338176] using wordTrace_append hprefix tailTrace_7338176
  have hstable : (prefixWord ++ tailWord_7338176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338176).length < 2 ^ (prefixWord ++ tailWord_7338176).sum := by decide
  have hdescent : baseEnd_7338176 < baseStart_7338176 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338202 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 3, 6]
def baseStart_7338202 : Nat := 118140960795 + 7338202 * 2 ^ 59
def prefixEnd_7338202 : Nat := 4983230072969 + 3 ^ 40 * 7338202 * 2
def baseEnd_7338202 : Nat := 1256008255261534494875743

theorem tailTrace_7338202 : CollatzResearch.WordTrace tailWord_7338202 prefixEnd_7338202 1256008255261534494875743 := by
  unfold tailWord_7338202
  simp only [CollatzResearch.WordTrace]
  refine ⟨66911553740238723492294215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178430809973969929312784573 66911553740238723492294215)
  ·
    refine ⟨100367330610358085238441323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66911553740238723492294215 100367330610358085238441323)
    ·
      refine ⟨150550995915537127857661985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100367330610358085238441323 150550995915537127857661985)
      ·
        refine ⟨112913246936652845893246489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150550995915537127857661985 112913246936652845893246489)
        ·
          refine ⟨84684935202489634419934867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112913246936652845893246489 84684935202489634419934867)
          ·
            refine ⟨127027402803734451629902301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84684935202489634419934867 127027402803734451629902301)
            ·
              refine ⟨47635276051400419361213363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 127027402803734451629902301 47635276051400419361213363)
              ·
                refine ⟨71452914077100629041820045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47635276051400419361213363 71452914077100629041820045)
                ·
                  refine ⟨26794842778912735890682517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71452914077100629041820045 26794842778912735890682517)
                  ·
                    refine ⟨1256008255261534494875743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26794842778912735890682517 1256008255261534494875743)
                    ·
                      rfl

theorem cell23_7338202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 3, 6].length) (baseStart_7338202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338202 prefixEnd_7338202 := by exact prefixLift 7338202
  have htrace : WordTrace (prefixWord ++ tailWord_7338202) baseStart_7338202 baseEnd_7338202 := by
    simpa [prefixWord, tailWord_7338202, baseEnd_7338202] using wordTrace_append hprefix tailTrace_7338202
  have hstable : (prefixWord ++ tailWord_7338202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338202).length < 2 ^ (prefixWord ++ tailWord_7338202).sum := by decide
  have hdescent : baseEnd_7338202 < baseStart_7338202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338210 : List Nat := [3, 3, 4, 1, 1, 1, 2, 2, 6]
def baseStart_7338210 : Nat := 118140960795 + 7338210 * 2 ^ 59
def prefixEnd_7338210 : Nat := 4983230072969 + 3 ^ 40 * 7338210 * 2
def baseEnd_7338210 : Nat := 418669874847759939258577

theorem tailTrace_7338210 : CollatzResearch.WordTrace tailWord_7338210 prefixEnd_7338210 418669874847759939258577 := by
  unfold tailWord_7338210
  simp only [CollatzResearch.WordTrace]
  refine ⟨66911626686231477833867021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178431004496617274223645389 66911626686231477833867021)
  ·
    refine ⟨25091860007336804187700133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66911626686231477833867021 25091860007336804187700133)
    ·
      refine ⟨4704723751375650785193775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25091860007336804187700133 4704723751375650785193775)
      ·
        refine ⟨7057085627063476177790663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4704723751375650785193775 7057085627063476177790663)
        ·
          refine ⟨10585628440595214266685995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7057085627063476177790663 10585628440595214266685995)
          ·
            refine ⟨15878442660892821400028993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10585628440595214266685995 15878442660892821400028993)
            ·
              refine ⟨11908831995669616050021745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15878442660892821400028993 11908831995669616050021745)
              ·
                refine ⟨8931623996752212037516309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11908831995669616050021745 8931623996752212037516309)
                ·
                  refine ⟨418669874847759939258577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8931623996752212037516309 418669874847759939258577)
                  ·
                    rfl

theorem cell23_7338210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 2, 6].length) (baseStart_7338210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338210 prefixEnd_7338210 := by exact prefixLift 7338210
  have htrace : WordTrace (prefixWord ++ tailWord_7338210) baseStart_7338210 baseEnd_7338210 := by
    simpa [prefixWord, tailWord_7338210, baseEnd_7338210] using wordTrace_append hprefix tailTrace_7338210
  have hstable : (prefixWord ++ tailWord_7338210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338210).length < 2 ^ (prefixWord ++ tailWord_7338210).sum := by decide
  have hdescent : baseEnd_7338210 < baseStart_7338210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338236 : List Nat := [2, 2, 2, 1, 4, 1, 2, 3, 2, 4]
def baseStart_7338236 : Nat := 118140960795 + 7338236 * 2 ^ 59
def prefixEnd_7338236 : Nat := 4983230072969 + 3 ^ 40 * 7338236 * 2
def baseEnd_7338236 : Nat := 1256014074708952117200691

theorem tailTrace_7338236 : CollatzResearch.WordTrace tailWord_7338236 prefixEnd_7338236 1256014074708952117200691 := by
  unfold tailWord_7338236
  simp only [CollatzResearch.WordTrace]
  refine ⟨133823727521415858887957281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178431636695221145183943041 133823727521415858887957281)
  ·
    refine ⟨100367795641061894165967961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133823727521415858887957281 100367795641061894165967961)
    ·
      refine ⟨75275846730796420624475971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100367795641061894165967961 75275846730796420624475971)
      ·
        refine ⟨112913770096194630936713957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75275846730796420624475971 112913770096194630936713957)
        ·
          refine ⟨21171331893036493300633867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112913770096194630936713957 21171331893036493300633867)
          ·
            refine ⟨31756997839554739950950801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21171331893036493300633867 31756997839554739950950801)
            ·
              refine ⟨23817748379666054963213101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31756997839554739950950801 23817748379666054963213101)
              ·
                refine ⟨8931655642374770611204913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23817748379666054963213101 8931655642374770611204913)
                ·
                  refine ⟨6698741731781077958403685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8931655642374770611204913 6698741731781077958403685)
                  ·
                    refine ⟨1256014074708952117200691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6698741731781077958403685 1256014074708952117200691)
                    ·
                      rfl

theorem cell23_7338236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 2, 4].length) (baseStart_7338236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338236 prefixEnd_7338236 := by exact prefixLift 7338236
  have htrace : WordTrace (prefixWord ++ tailWord_7338236) baseStart_7338236 baseEnd_7338236 := by
    simpa [prefixWord, tailWord_7338236, baseEnd_7338236] using wordTrace_append hprefix tailTrace_7338236
  have hstable : (prefixWord ++ tailWord_7338236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338236).length < 2 ^ (prefixWord ++ tailWord_7338236).sum := by decide
  have hdescent : baseEnd_7338236 < baseStart_7338236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338239 : List Nat := [1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 4]
def baseStart_7338239 : Nat := 118140960795 + 7338239 * 2 ^ 59
def prefixEnd_7338239 : Nat := 4983230072969 + 3 ^ 40 * 7338239 * 2
def baseEnd_7338239 : Nat := 3768043764568819839864559

theorem tailTrace_7338239 : CollatzResearch.WordTrace tailWord_7338239 prefixEnd_7338239 3768043764568819839864559 := by
  unfold tailWord_7338239
  simp only [CollatzResearch.WordTrace]
  refine ⟨267647564461820849288273771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178431709641213899525515847 267647564461820849288273771)
  ·
    refine ⟨401471346692731273932410657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267647564461820849288273771 401471346692731273932410657)
    ·
      refine ⟨301103510019548455449307993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401471346692731273932410657 301103510019548455449307993)
      ·
        refine ⟨225827632514661341586980995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301103510019548455449307993 225827632514661341586980995)
        ·
          refine ⟨338741448771992012380471493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225827632514661341586980995 338741448771992012380471493)
          ·
            refine ⟨63514021644748502321338405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338741448771992012380471493 63514021644748502321338405)
            ·
              refine ⟨11908879058390344185250951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63514021644748502321338405 11908879058390344185250951)
              ·
                refine ⟨17863318587585516277876427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11908879058390344185250951 17863318587585516277876427)
                ·
                  refine ⟨26794977881378274416814641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17863318587585516277876427 26794977881378274416814641)
                  ·
                    refine ⟨20096233411033705812610981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26794977881378274416814641 20096233411033705812610981)
                    ·
                      refine ⟨3768043764568819839864559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20096233411033705812610981 3768043764568819839864559)
                      ·
                        rfl

theorem cell23_7338239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_7338239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338239 prefixEnd_7338239 := by exact prefixLift 7338239
  have htrace : WordTrace (prefixWord ++ tailWord_7338239) baseStart_7338239 baseEnd_7338239 := by
    simpa [prefixWord, tailWord_7338239, baseEnd_7338239] using wordTrace_append hprefix tailTrace_7338239
  have hstable : (prefixWord ++ tailWord_7338239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338239).length < 2 ^ (prefixWord ++ tailWord_7338239).sum := by decide
  have hdescent : baseEnd_7338239 < baseStart_7338239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338247 : List Nat := [1, 1, 4, 5, 2, 1, 1, 1, 2, 3, 2]
def baseStart_7338247 : Nat := 118140960795 + 7338247 * 2 ^ 59
def prefixEnd_7338247 : Nat := 4983230072969 + 3 ^ 40 * 7338247 * 2
def baseEnd_7338247 : Nat := 3768047872414055808564523

theorem tailTrace_7338247 : CollatzResearch.WordTrace tailWord_7338247 prefixEnd_7338247 3768047872414055808564523 := by
  unfold tailWord_7338247
  simp only [CollatzResearch.WordTrace]
  refine ⟨267647856245791866654564995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178431904163861244436376663 267647856245791866654564995)
  ·
    refine ⟨401471784368687799981847493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267647856245791866654564995 401471784368687799981847493)
    ·
      refine ⟨75275959569128962496596405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401471784368687799981847493 75275959569128962496596405)
      ·
        refine ⟨7057121209605840234055913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 75275959569128962496596405 7057121209605840234055913)
        ·
          refine ⟨5292840907204380175541935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7057121209605840234055913 5292840907204380175541935)
          ·
            refine ⟨7939261360806570263312903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5292840907204380175541935 7939261360806570263312903)
            ·
              refine ⟨11908892041209855394969355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7939261360806570263312903 11908892041209855394969355)
              ·
                refine ⟨17863338061814783092454033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11908892041209855394969355 17863338061814783092454033)
                ·
                  refine ⟨13397503546361087319340525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17863338061814783092454033 13397503546361087319340525)
                  ·
                    refine ⟨5024063829885407744752697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13397503546361087319340525 5024063829885407744752697)
                    ·
                      refine ⟨3768047872414055808564523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024063829885407744752697 3768047872414055808564523)
                      ·
                        rfl

theorem cell23_7338247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_7338247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338247 prefixEnd_7338247 := by exact prefixLift 7338247
  have htrace : WordTrace (prefixWord ++ tailWord_7338247) baseStart_7338247 baseEnd_7338247 := by
    simpa [prefixWord, tailWord_7338247, baseEnd_7338247] using wordTrace_append hprefix tailTrace_7338247
  have hstable : (prefixWord ++ tailWord_7338247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338247).length < 2 ^ (prefixWord ++ tailWord_7338247).sum := by decide
  have hdescent : baseEnd_7338247 < baseStart_7338247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338249 : List Nat := [1, 2, 1, 1, 3, 5, 3, 7]
def baseStart_7338249 : Nat := 118140960795 + 7338249 * 2 ^ 59
def prefixEnd_7338249 : Nat := 4983230072969 + 3 ^ 40 * 7338249 * 2
def baseEnd_7338249 : Nat := 139557366643532029657019

theorem tailTrace_7338249 : CollatzResearch.WordTrace tailWord_7338249 prefixEnd_7338249 139557366643532029657019 := by
  unfold tailWord_7338249
  simp only [CollatzResearch.WordTrace]
  refine ⟨267647929191784620996137801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178431952794523080664091867 267647929191784620996137801)
  ·
    refine ⟨200735946893838465747103351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267647929191784620996137801 200735946893838465747103351)
    ·
      refine ⟨301103920340757698620655027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200735946893838465747103351 301103920340757698620655027)
      ·
        refine ⟨451655880511136547930982541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301103920340757698620655027 451655880511136547930982541)
        ·
          refine ⟨169370955191676205474118453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451655880511136547930982541 169370955191676205474118453)
          ·
            refine ⟨15878527049219644263198605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169370955191676205474118453 15878527049219644263198605)
            ·
              refine ⟨5954447643457366598699477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15878527049219644263198605 5954447643457366598699477)
              ·
                refine ⟨139557366643532029657019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5954447643457366598699477 139557366643532029657019)
                ·
                  rfl

theorem cell23_7338249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 3, 7].length) (baseStart_7338249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338249 prefixEnd_7338249 := by exact prefixLift 7338249
  have htrace : WordTrace (prefixWord ++ tailWord_7338249) baseStart_7338249 baseEnd_7338249 := by
    simpa [prefixWord, tailWord_7338249, baseEnd_7338249] using wordTrace_append hprefix tailTrace_7338249
  have hstable : (prefixWord ++ tailWord_7338249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338249).length < 2 ^ (prefixWord ++ tailWord_7338249).sum := by decide
  have hdescent : baseEnd_7338249 < baseStart_7338249 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338263 : List Nat := [1, 1, 3, 4, 1, 2, 4, 1, 1, 2, 3]
def baseStart_7338263 : Nat := 118140960795 + 7338263 * 2 ^ 59
def prefixEnd_7338263 : Nat := 4983230072969 + 3 ^ 40 * 7338263 * 2
def baseEnd_7338263 : Nat := 3768056088104527745964449

theorem tailTrace_7338263 : CollatzResearch.WordTrace tailWord_7338263 prefixEnd_7338263 3768056088104527745964449 := by
  unfold tailWord_7338263
  simp only [CollatzResearch.WordTrace]
  refine ⟨267648439813733901387147443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178432293209155934258098295 267648439813733901387147443)
  ·
    refine ⟨401472659720600852080721165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267648439813733901387147443 401472659720600852080721165)
    ·
      refine ⟨150552247395225319530270437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401472659720600852080721165 150552247395225319530270437)
      ·
        refine ⟨28228546386604747411925707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150552247395225319530270437 28228546386604747411925707)
        ·
          refine ⟨42342819579907121117888561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28228546386604747411925707 42342819579907121117888561)
          ·
            refine ⟨31757114684930340838416421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42342819579907121117888561 31757114684930340838416421)
            ·
              refine ⟨5954459003424438907203079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31757114684930340838416421 5954459003424438907203079)
              ·
                refine ⟨8931688505136658360804619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5954459003424438907203079 8931688505136658360804619)
                ·
                  refine ⟨13397532757704987541206929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8931688505136658360804619 13397532757704987541206929)
                  ·
                    refine ⟨10048149568278740655905197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13397532757704987541206929 10048149568278740655905197)
                    ·
                      refine ⟨3768056088104527745964449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10048149568278740655905197 3768056088104527745964449)
                      ·
                        rfl

theorem cell23_7338263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 4, 1, 1, 2, 3].length) (baseStart_7338263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338263 prefixEnd_7338263 := by exact prefixLift 7338263
  have htrace : WordTrace (prefixWord ++ tailWord_7338263) baseStart_7338263 baseEnd_7338263 := by
    simpa [prefixWord, tailWord_7338263, baseEnd_7338263] using wordTrace_append hprefix tailTrace_7338263
  have hstable : (prefixWord ++ tailWord_7338263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338263).length < 2 ^ (prefixWord ++ tailWord_7338263).sum := by decide
  have hdescent : baseEnd_7338263 < baseStart_7338263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338270 : List Nat := [4, 3, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_7338270 : Nat := 118140960795 + 7338270 * 2 ^ 59
def prefixEnd_7338270 : Nat := 4983230072969 + 3 ^ 40 * 7338270 * 2
def baseEnd_7338270 : Nat := 1256019894156369739525639

theorem tailTrace_7338270 : CollatzResearch.WordTrace tailWord_7338270 prefixEnd_7338270 1256019894156369739525639 := by
  unfold tailWord_7338270
  simp only [CollatzResearch.WordTrace]
  refine ⟨33456086890588567697831533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178432463416472361055101509 33456086890588567697831533)
  ·
    refine ⟨12546032583970712886686825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33456086890588567697831533 12546032583970712886686825)
    ·
      refine ⟨9409524437978034665015119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12546032583970712886686825 9409524437978034665015119)
      ·
        refine ⟨14114286656967051997522679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9409524437978034665015119 14114286656967051997522679)
        ·
          refine ⟨21171429985450577996284019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14114286656967051997522679 21171429985450577996284019)
          ·
            refine ⟨31757144978175866994426029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21171429985450577996284019 31757144978175866994426029)
            ·
              refine ⟨11908929366815950122909761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31757144978175866994426029 11908929366815950122909761)
              ·
                refine ⟨8931697025111962592182321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11908929366815950122909761 8931697025111962592182321)
                ·
                  refine ⟨6698772768833971944136741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8931697025111962592182321 6698772768833971944136741)
                  ·
                    refine ⟨1256019894156369739525639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6698772768833971944136741 1256019894156369739525639)
                    ·
                      rfl

theorem cell23_7338270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_7338270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338270 prefixEnd_7338270 := by exact prefixLift 7338270
  have htrace : WordTrace (prefixWord ++ tailWord_7338270) baseStart_7338270 baseEnd_7338270 := by
    simpa [prefixWord, tailWord_7338270, baseEnd_7338270] using wordTrace_append hprefix tailTrace_7338270
  have hstable : (prefixWord ++ tailWord_7338270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338270).length < 2 ^ (prefixWord ++ tailWord_7338270).sum := by decide
  have hdescent : baseEnd_7338270 < baseStart_7338270 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338303 : List Nat := [1, 1, 2, 2, 4, 1, 4, 2, 1, 3, 2]
def baseStart_7338303 : Nat := 118140960795 + 7338303 * 2 ^ 59
def prefixEnd_7338303 : Nat := 4983230072969 + 3 ^ 40 * 7338303 * 2
def baseEnd_7338303 : Nat := 3768076627330707589464265

theorem tailTrace_7338303 : CollatzResearch.WordTrace tailWord_7338303 prefixEnd_7338303 3768076627330707589464265 := by
  unfold tailWord_7338303
  simp only [CollatzResearch.WordTrace]
  refine ⟨267649898733588988218603563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178433265822392658812402375 267649898733588988218603563)
  ·
    refine ⟨401474848100383482327905345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267649898733588988218603563 401474848100383482327905345)
    ·
      refine ⟨301106136075287611745929009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401474848100383482327905345 301106136075287611745929009)
      ·
        refine ⟨225829602056465708809446757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301106136075287611745929009 225829602056465708809446757)
        ·
          refine ⟨42343050385587320401771267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225829602056465708809446757 42343050385587320401771267)
          ·
            refine ⟨63514575578380980602656901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42343050385587320401771267 63514575578380980602656901)
            ·
              refine ⟨11908982920946433862998169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63514575578380980602656901 11908982920946433862998169)
              ·
                refine ⟨8931737190709825397248627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11908982920946433862998169 8931737190709825397248627)
                ·
                  refine ⟨13397605786064738095872941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8931737190709825397248627 13397605786064738095872941)
                  ·
                    refine ⟨5024102169774276785952353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13397605786064738095872941 5024102169774276785952353)
                    ·
                      refine ⟨3768076627330707589464265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024102169774276785952353 3768076627330707589464265)
                      ·
                        rfl

theorem cell23_7338303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 2, 1, 3, 2].length) (baseStart_7338303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338303 prefixEnd_7338303 := by exact prefixLift 7338303
  have htrace : WordTrace (prefixWord ++ tailWord_7338303) baseStart_7338303 baseEnd_7338303 := by
    simpa [prefixWord, tailWord_7338303, baseEnd_7338303] using wordTrace_append hprefix tailTrace_7338303
  have hstable : (prefixWord ++ tailWord_7338303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338303).length < 2 ^ (prefixWord ++ tailWord_7338303).sum := by decide
  have hdescent : baseEnd_7338303 < baseStart_7338303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338316 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 3, 4, 2]
def baseStart_7338316 : Nat := 118140960795 + 7338316 * 2 ^ 59
def prefixEnd_7338316 : Nat := 4983230072969 + 3 ^ 40 * 7338316 * 2
def baseEnd_7338316 : Nat := 3768083302579216038601705

theorem tailTrace_7338316 : CollatzResearch.WordTrace tailWord_7338316 prefixEnd_7338316 3768083302579216038601705 := by
  unfold tailWord_7338316
  simp only [CollatzResearch.WordTrace]
  refine ⟨133825186441270945719413401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178433581921694594292551201 133825186441270945719413401)
  ·
    refine ⟨100368889830953209289560051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133825186441270945719413401 100368889830953209289560051)
    ·
      refine ⟨150553334746429813934340077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100368889830953209289560051 150553334746429813934340077)
      ·
        refine ⟨56457500529911180225377529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150553334746429813934340077 56457500529911180225377529)
        ·
          refine ⟨42343125397433385169033147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56457500529911180225377529 42343125397433385169033147)
          ·
            refine ⟨63514688096150077753549721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42343125397433385169033147 63514688096150077753549721)
            ·
              refine ⟨47636016072112558315162291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63514688096150077753549721 47636016072112558315162291)
              ·
                refine ⟨71454024108168837472743437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47636016072112558315162291 71454024108168837472743437)
                ·
                  refine ⟨26795259040563314052278789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71454024108168837472743437 26795259040563314052278789)
                  ·
                    refine ⟨5024111070105621384802273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26795259040563314052278789 5024111070105621384802273)
                    ·
                      refine ⟨3768083302579216038601705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024111070105621384802273 3768083302579216038601705)
                      ·
                        rfl

theorem cell23_7338316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_7338316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338316 prefixEnd_7338316 := by exact prefixLift 7338316
  have htrace : WordTrace (prefixWord ++ tailWord_7338316) baseStart_7338316 baseEnd_7338316 := by
    simpa [prefixWord, tailWord_7338316, baseEnd_7338316] using wordTrace_append hprefix tailTrace_7338316
  have hstable : (prefixWord ++ tailWord_7338316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338316).length < 2 ^ (prefixWord ++ tailWord_7338316).sum := by decide
  have hdescent : baseEnd_7338316 < baseStart_7338316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338379 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 5]
def baseStart_7338379 : Nat := 118140960795 + 7338379 * 2 ^ 59
def prefixEnd_7338379 : Nat := 4983230072969 + 3 ^ 40 * 7338379 * 2
def baseEnd_7338379 : Nat := 3768115651860449292113915

theorem tailTrace_7338379 : CollatzResearch.WordTrace tailWord_7338379 prefixEnd_7338379 3768115651860449292113915 := by
  unfold tailWord_7338379
  simp only [CollatzResearch.WordTrace]
  refine ⟨267652670681313653198370191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178435113787542435465580127 267652670681313653198370191)
  ·
    refine ⟨401479006021970479797555287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267652670681313653198370191 401479006021970479797555287)
    ·
      refine ⟨602218509032955719696332931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401479006021970479797555287 602218509032955719696332931)
      ·
        refine ⟨903327763549433579544499397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602218509032955719696332931 903327763549433579544499397)
        ·
          refine ⟨169373955665518796164593637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 903327763549433579544499397 169373955665518796164593637)
          ·
            refine ⟨31757616687284774280861307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169373955665518796164593637 31757616687284774280861307)
            ·
              refine ⟨47636425030927161421291961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31757616687284774280861307 47636425030927161421291961)
              ·
                refine ⟨35727318773195371065968971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47636425030927161421291961 35727318773195371065968971)
                ·
                  refine ⟨53590978159793056598953457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35727318773195371065968971 53590978159793056598953457)
                  ·
                    refine ⟨40193233619844792449215093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53590978159793056598953457 40193233619844792449215093)
                    ·
                      refine ⟨3768115651860449292113915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40193233619844792449215093 3768115651860449292113915)
                      ·
                        rfl

theorem cell23_7338379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 5].length) (baseStart_7338379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338379 prefixEnd_7338379 := by exact prefixLift 7338379
  have htrace : WordTrace (prefixWord ++ tailWord_7338379) baseStart_7338379 baseEnd_7338379 := by
    simpa [prefixWord, tailWord_7338379, baseEnd_7338379] using wordTrace_append hprefix tailTrace_7338379
  have hstable : (prefixWord ++ tailWord_7338379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338379).length < 2 ^ (prefixWord ++ tailWord_7338379).sum := by decide
  have hdescent : baseEnd_7338379 < baseStart_7338379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338389 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 3, 3, 4]
def baseStart_7338389 : Nat := 118140960795 + 7338389 * 2 ^ 59
def prefixEnd_7338389 : Nat := 4983230072969 + 3 ^ 40 * 7338389 * 2
def baseEnd_7338389 : Nat := 3768120786666994252988869

theorem tailTrace_7338389 : CollatzResearch.WordTrace tailWord_7338389 prefixEnd_7338389 3768120786666994252988869 := by
  unfold tailWord_7338389
  simp only [CollatzResearch.WordTrace]
  refine ⟨267653035411277424906234221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178435356940851616604156147 267653035411277424906234221)
  ·
    refine ⟨100369888279229034339837833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267653035411277424906234221 100369888279229034339837833)
    ·
      refine ⟨75277416209421775754878375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100369888279229034339837833 75277416209421775754878375)
      ·
        refine ⟨112916124314132663632317563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75277416209421775754878375 112916124314132663632317563)
        ·
          refine ⟨169374186471198995448476345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112916124314132663632317563 169374186471198995448476345)
          ·
            refine ⟨127030639853399246586357259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169374186471198995448476345 127030639853399246586357259)
            ·
              refine ⟨190545959780098869879535889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127030639853399246586357259 190545959780098869879535889)
              ·
                refine ⟨142909469835074152409651917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190545959780098869879535889 142909469835074152409651917)
                ·
                  refine ⟨53591051188152807153619469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142909469835074152409651917 53591051188152807153619469)
                  ·
                    refine ⟨20096644195557302682607301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53591051188152807153619469 20096644195557302682607301)
                    ·
                      refine ⟨3768120786666994252988869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20096644195557302682607301 3768120786666994252988869)
                      ·
                        rfl

theorem cell23_7338389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 3, 3, 4].length) (baseStart_7338389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338389 prefixEnd_7338389 := by exact prefixLift 7338389
  have htrace : WordTrace (prefixWord ++ tailWord_7338389) baseStart_7338389 baseEnd_7338389 := by
    simpa [prefixWord, tailWord_7338389, baseEnd_7338389] using wordTrace_append hprefix tailTrace_7338389
  have hstable : (prefixWord ++ tailWord_7338389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338389).length < 2 ^ (prefixWord ++ tailWord_7338389).sum := by decide
  have hdescent : baseEnd_7338389 < baseStart_7338389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338420 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 1, 7]
def baseStart_7338420 : Nat := 118140960795 + 7338420 * 2 ^ 59
def prefixEnd_7338420 : Nat := 4983230072969 + 3 ^ 40 * 7338420 * 2
def baseEnd_7338420 : Nat := 1256045568189094543900409

theorem tailTrace_7338420 : CollatzResearch.WordTrace tailWord_7338420 prefixEnd_7338420 1256045568189094543900409 := by
  unfold tailWord_7338420
  simp only [CollatzResearch.WordTrace]
  refine ⟨133827083037082558600306357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178436110716110078133741809 133827083037082558600306357)
  ·
    refine ⟨12546289034726489868778721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133827083037082558600306357 12546289034726489868778721)
    ·
      refine ⟨9409716776044867401584041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12546289034726489868778721 9409716776044867401584041)
      ·
        refine ⟨7057287582033650551188031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9409716776044867401584041 7057287582033650551188031)
        ·
          refine ⟨10585931373050475826782047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7057287582033650551188031 10585931373050475826782047)
          ·
            refine ⟨15878897059575713740173071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10585931373050475826782047 15878897059575713740173071)
            ·
              refine ⟨23818345589363570610259607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15878897059575713740173071 23818345589363570610259607)
              ·
                refine ⟨35727518384045355915389411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23818345589363570610259607 35727518384045355915389411)
                ·
                  refine ⟨53591277576068033873084117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35727518384045355915389411 53591277576068033873084117)
                  ·
                    refine ⟨1256045568189094543900409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53591277576068033873084117 1256045568189094543900409)
                    ·
                      rfl

theorem cell23_7338420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_7338420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338420 prefixEnd_7338420 := by exact prefixLift 7338420
  have htrace : WordTrace (prefixWord ++ tailWord_7338420) baseStart_7338420 baseEnd_7338420 := by
    simpa [prefixWord, tailWord_7338420, baseEnd_7338420] using wordTrace_append hprefix tailTrace_7338420
  have hstable : (prefixWord ++ tailWord_7338420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338420).length < 2 ^ (prefixWord ++ tailWord_7338420).sum := by decide
  have hdescent : baseEnd_7338420 < baseStart_7338420 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338423 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 2, 1, 4]
def baseStart_7338423 : Nat := 118140960795 + 7338423 * 2 ^ 59
def prefixEnd_7338423 : Nat := 4983230072969 + 3 ^ 40 * 7338423 * 2
def baseEnd_7338423 : Nat := 3768138245009247119963713

theorem tailTrace_7338423 : CollatzResearch.WordTrace tailWord_7338423 prefixEnd_7338423 3768138245009247119963713 := by
  unfold tailWord_7338423
  simp only [CollatzResearch.WordTrace]
  refine ⟨267654275493154248712971923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178436183662102832475314615 267654275493154248712971923)
  ·
    refine ⟨401481413239731373069457885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267654275493154248712971923 401481413239731373069457885)
    ·
      refine ⟨150555529964899264901046707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401481413239731373069457885 150555529964899264901046707)
      ·
        refine ⟨225833294947348897351570061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150555529964899264901046707 225833294947348897351570061)
        ·
          refine ⟨84687485605255836506838773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225833294947348897351570061 84687485605255836506838773)
          ·
            refine ⟨7939451775492734672516135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84687485605255836506838773 7939451775492734672516135)
            ·
              refine ⟨11909177663239102008774203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7939451775492734672516135 11909177663239102008774203)
              ·
                refine ⟨17863766494858653013161305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11909177663239102008774203 17863766494858653013161305)
                ·
                  refine ⟨13397824871143989759870979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17863766494858653013161305 13397824871143989759870979)
                  ·
                    refine ⟨20096737306715984639806469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13397824871143989759870979 20096737306715984639806469)
                    ·
                      refine ⟨3768138245009247119963713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20096737306715984639806469 3768138245009247119963713)
                      ·
                        rfl

theorem cell23_7338423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_7338423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338423 prefixEnd_7338423 := by exact prefixLift 7338423
  have htrace : WordTrace (prefixWord ++ tailWord_7338423) baseStart_7338423 baseEnd_7338423 := by
    simpa [prefixWord, tailWord_7338423, baseEnd_7338423] using wordTrace_append hprefix tailTrace_7338423
  have hstable : (prefixWord ++ tailWord_7338423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338423).length < 2 ^ (prefixWord ++ tailWord_7338423).sum := by decide
  have hdescent : baseEnd_7338423 < baseStart_7338423 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338463 : List Nat := [1, 1, 2, 3, 3, 3, 3, 1, 6]
def baseStart_7338463 : Nat := 118140960795 + 7338463 * 2 ^ 59
def prefixEnd_7338463 : Nat := 4983230072969 + 3 ^ 40 * 7338463 * 2
def baseEnd_7338463 : Nat := 418684309359491884829281

theorem tailTrace_7338463 : CollatzResearch.WordTrace tailWord_7338463 prefixEnd_7338463 418684309359491884829281 := by
  unfold tailWord_7338463
  simp only [CollatzResearch.WordTrace]
  refine ⟨267655734413009335544428043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178437156275339557029618695 267655734413009335544428043)
  ·
    refine ⟨401483601619514003316642065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267655734413009335544428043 401483601619514003316642065)
    ·
      refine ⟨301112701214635502487481549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401483601619514003316642065 301112701214635502487481549)
      ·
        refine ⟨112917262955488313432805581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301112701214635502487481549 112917262955488313432805581)
        ·
          refine ⟨42343973608308117537302093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112917262955488313432805581 42343973608308117537302093)
          ·
            refine ⟨15878990103115544076488285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42343973608308117537302093 15878990103115544076488285)
            ·
              refine ⟨5954621288668329028683107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15878990103115544076488285 5954621288668329028683107)
              ·
                refine ⟨8931931933002493543024661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5954621288668329028683107 8931931933002493543024661)
                ·
                  refine ⟨418684309359491884829281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8931931933002493543024661 418684309359491884829281)
                  ·
                    rfl

theorem cell23_7338463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 3, 1, 6].length) (baseStart_7338463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338463 prefixEnd_7338463 := by exact prefixLift 7338463
  have htrace : WordTrace (prefixWord ++ tailWord_7338463) baseStart_7338463 baseEnd_7338463 := by
    simpa [prefixWord, tailWord_7338463, baseEnd_7338463] using wordTrace_append hprefix tailTrace_7338463
  have hstable : (prefixWord ++ tailWord_7338463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338463).length < 2 ^ (prefixWord ++ tailWord_7338463).sum := by decide
  have hdescent : baseEnd_7338463 < baseStart_7338463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338483 : List Nat := [1, 1, 1, 2, 2, 2, 4, 3, 2, 3, 2]
def baseStart_7338483 : Nat := 118140960795 + 7338483 * 2 ^ 59
def prefixEnd_7338483 : Nat := 4983230072969 + 3 ^ 40 * 7338483 * 2
def baseEnd_7338483 : Nat := 3768169053848516885213437

theorem tailTrace_7338483 : CollatzResearch.WordTrace tailWord_7338483 prefixEnd_7338483 3768169053848516885213437 := by
  unfold tailWord_7338483
  simp only [CollatzResearch.WordTrace]
  refine ⟨267656463872936878960156103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178437642581957919306770735 267656463872936878960156103)
  ·
    refine ⟨401484695809405318440234155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267656463872936878960156103 401484695809405318440234155)
    ·
      refine ⟨602227043714107977660351233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401484695809405318440234155 602227043714107977660351233)
      ·
        refine ⟨451670282785580983245263425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602227043714107977660351233 451670282785580983245263425)
        ·
          refine ⟨338752712089185737433947569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451670282785580983245263425 338752712089185737433947569)
          ·
            refine ⟨254064534066889303075460677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338752712089185737433947569 254064534066889303075460677)
            ·
              refine ⟨47637100137541744326648877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 254064534066889303075460677 47637100137541744326648877)
              ·
                refine ⟨17863912551578154122493329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47637100137541744326648877 17863912551578154122493329)
                ·
                  refine ⟨13397934413683615591869997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17863912551578154122493329 13397934413683615591869997)
                  ·
                    refine ⟨5024225405131355846951249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13397934413683615591869997 5024225405131355846951249)
                    ·
                      refine ⟨3768169053848516885213437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024225405131355846951249 3768169053848516885213437)
                      ·
                        rfl

theorem cell23_7338483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 3, 2, 3, 2].length) (baseStart_7338483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338483 prefixEnd_7338483 := by exact prefixLift 7338483
  have htrace : WordTrace (prefixWord ++ tailWord_7338483) baseStart_7338483 baseEnd_7338483 := by
    simpa [prefixWord, tailWord_7338483, baseEnd_7338483] using wordTrace_append hprefix tailTrace_7338483
  have hstable : (prefixWord ++ tailWord_7338483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338483).length < 2 ^ (prefixWord ++ tailWord_7338483).sum := by decide
  have hdescent : baseEnd_7338483 < baseStart_7338483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338490 : List Nat := [3, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3]
def baseStart_7338490 : Nat := 118140960795 + 7338490 * 2 ^ 59
def prefixEnd_7338490 : Nat := 4983230072969 + 3 ^ 40 * 7338490 * 2
def baseEnd_7338490 : Nat := 3768172648213098357825905

theorem tailTrace_7338490 : CollatzResearch.WordTrace tailWord_7338490 prefixEnd_7338490 3768172648213098357825905 := by
  unfold tailWord_7338490
  simp only [CollatzResearch.WordTrace]
  refine ⟨66914179795977879788915231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178437812789274346103773949 66914179795977879788915231)
  ·
    refine ⟨100371269693966819683372847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66914179795977879788915231 100371269693966819683372847)
    ·
      refine ⟨150556904540950229525059271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100371269693966819683372847 150556904540950229525059271)
      ·
        refine ⟨225835356811425344287588907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150556904540950229525059271 225835356811425344287588907)
        ·
          refine ⟨338753035217138016431383361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225835356811425344287588907 338753035217138016431383361)
          ·
            refine ⟨254064776412853512323537521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338753035217138016431383361 254064776412853512323537521)
            ·
              refine ⟨190548582309640134242653141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254064776412853512323537521 190548582309640134242653141)
              ·
                refine ⟨4465982397882190646312183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 190548582309640134242653141 4465982397882190646312183)
                ·
                  refine ⟨6698973596823285969468275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4465982397882190646312183 6698973596823285969468275)
                  ·
                    refine ⟨10048460395234928954202413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6698973596823285969468275 10048460395234928954202413)
                    ·
                      refine ⟨3768172648213098357825905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10048460395234928954202413 3768172648213098357825905)
                      ·
                        rfl

theorem cell23_7338490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3].length) (baseStart_7338490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338490 prefixEnd_7338490 := by exact prefixLift 7338490
  have htrace : WordTrace (prefixWord ++ tailWord_7338490) baseStart_7338490 baseEnd_7338490 := by
    simpa [prefixWord, tailWord_7338490, baseEnd_7338490] using wordTrace_append hprefix tailTrace_7338490
  have hstable : (prefixWord ++ tailWord_7338490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338490).length < 2 ^ (prefixWord ++ tailWord_7338490).sum := by decide
  have hdescent : baseEnd_7338490 < baseStart_7338490 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338500 : List Nat := [2, 3, 2, 3, 1, 1, 1, 1, 4, 3, 2]
def baseStart_7338500 : Nat := 118140960795 + 7338500 * 2 ^ 59
def prefixEnd_7338500 : Nat := 4983230072969 + 3 ^ 40 * 7338500 * 2
def baseEnd_7338500 : Nat := 3768177783019643318700859

theorem tailTrace_7338500 : CollatzResearch.WordTrace tailWord_7338500 prefixEnd_7338500 3768177783019643318700859 := by
  unfold tailWord_7338500
  simp only [CollatzResearch.WordTrace]
  refine ⟨133828541956937645431762477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178438055942583527242349969 133828541956937645431762477)
  ·
    refine ⟨50185703233851617036910929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133828541956937645431762477 50185703233851617036910929)
    ·
      refine ⟨37639277425388712777683197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50185703233851617036910929 37639277425388712777683197)
      ·
        refine ⟨14114729034520767291631199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37639277425388712777683197 14114729034520767291631199)
        ·
          refine ⟨21172093551781150937446799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14114729034520767291631199 21172093551781150937446799)
          ·
            refine ⟨31758140327671726406170199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21172093551781150937446799 31758140327671726406170199)
            ·
              refine ⟨47637210491507589609255299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31758140327671726406170199 47637210491507589609255299)
              ·
                refine ⟨71455815737261384413882949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47637210491507589609255299 71455815737261384413882949)
                ·
                  refine ⟨13397965450736509577603053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71455815737261384413882949 13397965450736509577603053)
                  ·
                    refine ⟨5024237044026191091601145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13397965450736509577603053 5024237044026191091601145)
                    ·
                      refine ⟨3768177783019643318700859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024237044026191091601145 3768177783019643318700859)
                      ·
                        rfl

theorem cell23_7338500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_7338500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338500 prefixEnd_7338500 := by exact prefixLift 7338500
  have htrace : WordTrace (prefixWord ++ tailWord_7338500) baseStart_7338500 baseEnd_7338500 := by
    simpa [prefixWord, tailWord_7338500, baseEnd_7338500] using wordTrace_append hprefix tailTrace_7338500
  have hstable : (prefixWord ++ tailWord_7338500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338500).length < 2 ^ (prefixWord ++ tailWord_7338500).sum := by decide
  have hdescent : baseEnd_7338500 < baseStart_7338500 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338530 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 5, 2, 2]
def baseStart_7338530 : Nat := 118140960795 + 7338530 * 2 ^ 59
def prefixEnd_7338530 : Nat := 4983230072969 + 3 ^ 40 * 7338530 * 2
def baseEnd_7338530 : Nat := 3768193187439278201325721

theorem tailTrace_7338530 : CollatzResearch.WordTrace tailWord_7338530 prefixEnd_7338530 3768193187439278201325721 := by
  unfold tailWord_7338530
  simp only [CollatzResearch.WordTrace]
  refine ⟨66914544525941651496779261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178438785402511070658078029 66914544525941651496779261)
  ·
    refine ⟨25092954197228119311292223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66914544525941651496779261 25092954197228119311292223)
    ·
      refine ⟨37639431295842178966938335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25092954197228119311292223 37639431295842178966938335)
      ·
        refine ⟨56459146943763268450407503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37639431295842178966938335 56459146943763268450407503)
        ·
          refine ⟨84688720415644902675611255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56459146943763268450407503 84688720415644902675611255)
          ·
            refine ⟨127033080623467354013416883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84688720415644902675611255 127033080623467354013416883)
            ·
              refine ⟨190549620935201031020125325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127033080623467354013416883 190549620935201031020125325)
              ·
                refine ⟨71456107850700386632546997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190549620935201031020125325 71456107850700386632546997)
                ·
                  refine ⟨6699010111003161246801281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71456107850700386632546997 6699010111003161246801281)
                  ·
                    refine ⟨5024257583252370935100961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6699010111003161246801281 5024257583252370935100961)
                    ·
                      refine ⟨3768193187439278201325721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024257583252370935100961 3768193187439278201325721)
                      ·
                        rfl

theorem cell23_7338530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_7338530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338530 prefixEnd_7338530 := by exact prefixLift 7338530
  have htrace : WordTrace (prefixWord ++ tailWord_7338530) baseStart_7338530 baseEnd_7338530 := by
    simpa [prefixWord, tailWord_7338530, baseEnd_7338530] using wordTrace_append hprefix tailTrace_7338530
  have hstable : (prefixWord ++ tailWord_7338530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338530).length < 2 ^ (prefixWord ++ tailWord_7338530).sum := by decide
  have hdescent : baseEnd_7338530 < baseStart_7338530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338547 : List Nat := [1, 1, 1, 2, 4, 2, 2, 5, 1, 2, 2]
def baseStart_7338547 : Nat := 118140960795 + 7338547 * 2 ^ 59
def prefixEnd_7338547 : Nat := 4983230072969 + 3 ^ 40 * 7338547 * 2
def baseEnd_7338547 : Nat := 3768201916610404634813143

theorem tailTrace_7338547 : CollatzResearch.WordTrace tailWord_7338547 prefixEnd_7338547 3768201916610404634813143 := by
  unfold tailWord_7338547
  simp only [CollatzResearch.WordTrace]
  refine ⟨267658798144705017890485895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178439198763136678593657263 267658798144705017890485895)
  ·
    refine ⟨401488197217057526835728843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267658798144705017890485895 401488197217057526835728843)
    ·
      refine ⟨602232295825586290253593265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401488197217057526835728843 602232295825586290253593265)
      ·
        refine ⟨451674221869189717690194949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602232295825586290253593265 451674221869189717690194949)
        ·
          refine ⟨84688916600473072066911553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 451674221869189717690194949 84688916600473072066911553)
          ·
            refine ⟨63516687450354804050183665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84688916600473072066911553 63516687450354804050183665)
            ·
              refine ⟨47637515587766103037637749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63516687450354804050183665 47637515587766103037637749)
              ·
                refine ⟨4466017086353072159778539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47637515587766103037637749 4466017086353072159778539)
                ·
                  refine ⟨6699025629529608239667809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466017086353072159778539 6699025629529608239667809)
                  ·
                    refine ⟨5024269222147206179750857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6699025629529608239667809 5024269222147206179750857)
                    ·
                      refine ⟨3768201916610404634813143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024269222147206179750857 3768201916610404634813143)
                      ·
                        rfl

theorem cell23_7338547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 5, 1, 2, 2].length) (baseStart_7338547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338547 prefixEnd_7338547 := by exact prefixLift 7338547
  have htrace : WordTrace (prefixWord ++ tailWord_7338547) baseStart_7338547 baseEnd_7338547 := by
    simpa [prefixWord, tailWord_7338547, baseEnd_7338547] using wordTrace_append hprefix tailTrace_7338547
  have hstable : (prefixWord ++ tailWord_7338547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338547).length < 2 ^ (prefixWord ++ tailWord_7338547).sum := by decide
  have hdescent : baseEnd_7338547 < baseStart_7338547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338550 : List Nat := [5, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5]
def baseStart_7338550 : Nat := 118140960795 + 7338550 * 2 ^ 59
def prefixEnd_7338550 : Nat := 4983230072969 + 3 ^ 40 * 7338550 * 2
def baseEnd_7338550 : Nat := 3768203457052368123075629

theorem tailTrace_7338550 : CollatzResearch.WordTrace tailWord_7338550 prefixEnd_7338550 3768203457052368123075629 := by
  unfold tailWord_7338550
  simp only [CollatzResearch.WordTrace]
  refine ⟨16728681722730884337677819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178439271709129432935230069 16728681722730884337677819)
  ·
    refine ⟨25093022584096326506516729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16728681722730884337677819 25093022584096326506516729)
    ·
      refine ⟨18819766938072244879887547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25093022584096326506516729 18819766938072244879887547)
      ·
        refine ⟨28229650407108367319831321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18819766938072244879887547 28229650407108367319831321)
        ·
          refine ⟨21172237805331275489873491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28229650407108367319831321 21172237805331275489873491)
          ·
            refine ⟨31758356707996913234810237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21172237805331275489873491 31758356707996913234810237)
            ·
              refine ⟨11909383765498842463053839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31758356707996913234810237 11909383765498842463053839)
              ·
                refine ⟨17864075648248263694580759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11909383765498842463053839 17864075648248263694580759)
                ·
                  refine ⟨26796113472372395541871139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17864075648248263694580759 26796113472372395541871139)
                  ·
                    refine ⟨40194170208558593312806709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26796113472372395541871139 40194170208558593312806709)
                    ·
                      refine ⟨3768203457052368123075629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40194170208558593312806709 3768203457052368123075629)
                      ·
                        rfl

theorem cell23_7338550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_7338550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338550 prefixEnd_7338550 := by exact prefixLift 7338550
  have htrace : WordTrace (prefixWord ++ tailWord_7338550) baseStart_7338550 baseEnd_7338550 := by
    simpa [prefixWord, tailWord_7338550, baseEnd_7338550] using wordTrace_append hprefix tailTrace_7338550
  have hstable : (prefixWord ++ tailWord_7338550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338550).length < 2 ^ (prefixWord ++ tailWord_7338550).sum := by decide
  have hdescent : baseEnd_7338550 < baseStart_7338550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338558 : List Nat := [4, 2, 1, 4, 1, 2, 2, 2, 1, 1, 3]
def baseStart_7338558 : Nat := 118140960795 + 7338558 * 2 ^ 59
def prefixEnd_7338558 : Nat := 4983230072969 + 3 ^ 40 * 7338558 * 2
def baseEnd_7338558 : Nat := 3768207564897604091775593

theorem tailTrace_7338558 : CollatzResearch.WordTrace tailWord_7338558 prefixEnd_7338558 3768207564897604091775593 := by
  unfold tailWord_7338558
  simp only [CollatzResearch.WordTrace]
  refine ⟨33457399918458145846142041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178439466231776777846090885 33457399918458145846142041)
  ·
    refine ⟨25093049938843609384606531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33457399918458145846142041 25093049938843609384606531)
    ·
      refine ⟨37639574908265414076909797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25093049938843609384606531 37639574908265414076909797)
      ·
        refine ⟨7057420295299765139420587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37639574908265414076909797 7057420295299765139420587)
        ·
          refine ⟨10586130442949647709130881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7057420295299765139420587 10586130442949647709130881)
          ·
            refine ⟨7939597832212235781848161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10586130442949647709130881 7939597832212235781848161)
            ·
              refine ⟨5954698374159176836386121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7939597832212235781848161 5954698374159176836386121)
              ·
                refine ⟨4466023780619382627289591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5954698374159176836386121 4466023780619382627289591)
                ·
                  refine ⟨6699035670929073940934387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466023780619382627289591 6699035670929073940934387)
                  ·
                    refine ⟨10048553506393610911401581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6699035670929073940934387 10048553506393610911401581)
                    ·
                      refine ⟨3768207564897604091775593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10048553506393610911401581 3768207564897604091775593)
                      ·
                        rfl

theorem cell23_7338558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_7338558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338558 prefixEnd_7338558 := by exact prefixLift 7338558
  have htrace : WordTrace (prefixWord ++ tailWord_7338558) baseStart_7338558 baseEnd_7338558 := by
    simpa [prefixWord, tailWord_7338558, baseEnd_7338558] using wordTrace_append hprefix tailTrace_7338558
  have hstable : (prefixWord ++ tailWord_7338558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338558).length < 2 ^ (prefixWord ++ tailWord_7338558).sum := by decide
  have hdescent : baseEnd_7338558 < baseStart_7338558 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338563 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 4, 1, 3]
def baseStart_7338563 : Nat := 118140960795 + 7338563 * 2 ^ 59
def prefixEnd_7338563 : Nat := 4983230072969 + 3 ^ 40 * 7338563 * 2
def baseEnd_7338563 : Nat := 3768210132300876572213069

theorem tailTrace_7338563 : CollatzResearch.WordTrace tailWord_7338563 prefixEnd_7338563 3768210132300876572213069 := by
  unfold tailWord_7338563
  simp only [CollatzResearch.WordTrace]
  refine ⟨267659381712647052623068343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178439587808431368415378895 267659381712647052623068343)
  ·
    refine ⟨401489072568970578934602515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267659381712647052623068343 401489072568970578934602515)
    ·
      refine ⟨602233608853455868401903773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401489072568970578934602515 602233608853455868401903773)
      ·
        refine ⟨225837603320045950650713915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 602233608853455868401903773 225837603320045950650713915)
        ·
          refine ⟨338756404980068925976070873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225837603320045950650713915 338756404980068925976070873)
          ·
            refine ⟨254067303735051694482053155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338756404980068925976070873 254067303735051694482053155)
            ·
              refine ⟨381100955602577541723079733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254067303735051694482053155 381100955602577541723079733)
              ·
                refine ⟨35728214587741644536538725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 381100955602577541723079733 35728214587741644536538725)
                ·
                  refine ⟨6699040235201558350601011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35728214587741644536538725 6699040235201558350601011)
                  ·
                    refine ⟨10048560352802337525901517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6699040235201558350601011 10048560352802337525901517)
                    ·
                      refine ⟨3768210132300876572213069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10048560352802337525901517 3768210132300876572213069)
                      ·
                        rfl

theorem cell23_7338563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 1, 3].length) (baseStart_7338563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338563 prefixEnd_7338563 := by exact prefixLift 7338563
  have htrace : WordTrace (prefixWord ++ tailWord_7338563) baseStart_7338563 baseEnd_7338563 := by
    simpa [prefixWord, tailWord_7338563, baseEnd_7338563] using wordTrace_append hprefix tailTrace_7338563
  have hstable : (prefixWord ++ tailWord_7338563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338563).length < 2 ^ (prefixWord ++ tailWord_7338563).sum := by decide
  have hdescent : baseEnd_7338563 < baseStart_7338563 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338580 : List Nat := [2, 4, 1, 1, 1, 4, 2, 1, 1, 3, 3]
def baseStart_7338580 : Nat := 118140960795 + 7338580 * 2 ^ 59
def prefixEnd_7338580 : Nat := 4983230072969 + 3 ^ 40 * 7338580 * 2
def baseEnd_7338580 : Nat := 3768218861472003005700491

theorem tailTrace_7338580 : CollatzResearch.WordTrace tailWord_7338580 prefixEnd_7338580 3768218861472003005700491 := by
  unfold tailWord_7338580
  simp only [CollatzResearch.WordTrace]
  refine ⟨133830000876792732263218597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178440001169056976350958129 133830000876792732263218597)
  ·
    refine ⟨25093125164398637299353487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133830000876792732263218597 25093125164398637299353487)
    ·
      refine ⟨37639687746597955949030231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25093125164398637299353487 37639687746597955949030231)
      ·
        refine ⟨56459531619896933923545347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37639687746597955949030231 56459531619896933923545347)
        ·
          refine ⟨84689297429845400885318021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56459531619896933923545347 84689297429845400885318021)
          ·
            refine ⟨15879243268096012665997129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84689297429845400885318021 15879243268096012665997129)
            ·
              refine ⟨11909432451072009499497847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15879243268096012665997129 11909432451072009499497847)
              ·
                refine ⟨17864148676608014249246771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11909432451072009499497847 17864148676608014249246771)
                ·
                  refine ⟨26796223014912021373870157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17864148676608014249246771 26796223014912021373870157)
                  ·
                    refine ⟨10048583630592008015201309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26796223014912021373870157 10048583630592008015201309)
                    ·
                      refine ⟨3768218861472003005700491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10048583630592008015201309 3768218861472003005700491)
                      ·
                        rfl

theorem cell23_7338580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_7338580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338580 prefixEnd_7338580 := by exact prefixLift 7338580
  have htrace : WordTrace (prefixWord ++ tailWord_7338580) baseStart_7338580 baseEnd_7338580 := by
    simpa [prefixWord, tailWord_7338580, baseEnd_7338580] using wordTrace_append hprefix tailTrace_7338580
  have hstable : (prefixWord ++ tailWord_7338580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338580).length < 2 ^ (prefixWord ++ tailWord_7338580).sum := by decide
  have hdescent : baseEnd_7338580 < baseStart_7338580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338596 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 1, 8]
def baseStart_7338596 : Nat := 118140960795 + 7338596 * 2 ^ 59
def prefixEnd_7338596 : Nat := 4983230072969 + 3 ^ 40 * 7338596 * 2
def baseEnd_7338596 : Nat := 1256075692387491647700139

theorem tailTrace_7338596 : CollatzResearch.WordTrace tailWord_7338596 prefixEnd_7338596 1256075692387491647700139 := by
  unfold tailWord_7338596
  simp only [CollatzResearch.WordTrace]
  refine ⟨133830292660763749629509821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178440390214351666172679761 133830292660763749629509821)
  ·
    refine ⟨50186359747786406111066183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133830292660763749629509821 50186359747786406111066183)
    ·
      refine ⟨75279539621679609166599275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50186359747786406111066183 75279539621679609166599275)
      ·
        refine ⟨112919309432519413749898913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75279539621679609166599275 112919309432519413749898913)
        ·
          refine ⟨84689482074389560312424185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112919309432519413749898913 84689482074389560312424185)
          ·
            refine ⟨63517111555792170234318139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84689482074389560312424185 63517111555792170234318139)
            ·
              refine ⟨95275667333688255351477209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63517111555792170234318139 95275667333688255351477209)
              ·
                refine ⟨71456750500266191513607907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95275667333688255351477209 71456750500266191513607907)
                ·
                  refine ⟨107185125750399287270411861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71456750500266191513607907 107185125750399287270411861)
                  ·
                    refine ⟨1256075692387491647700139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107185125750399287270411861 1256075692387491647700139)
                    ·
                      rfl

theorem cell23_7338596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_7338596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338596 prefixEnd_7338596 := by exact prefixLift 7338596
  have htrace : WordTrace (prefixWord ++ tailWord_7338596) baseStart_7338596 baseEnd_7338596 := by
    simpa [prefixWord, tailWord_7338596, baseEnd_7338596] using wordTrace_append hprefix tailTrace_7338596
  have hstable : (prefixWord ++ tailWord_7338596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338596).length < 2 ^ (prefixWord ++ tailWord_7338596).sum := by decide
  have hdescent : baseEnd_7338596 < baseStart_7338596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338603 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 3, 4, 2]
def baseStart_7338603 : Nat := 118140960795 + 7338603 * 2 ^ 59
def prefixEnd_7338603 : Nat := 4983230072969 + 3 ^ 40 * 7338603 * 2
def baseEnd_7338603 : Nat := 3768230671527056415712885

theorem tailTrace_7338603 : CollatzResearch.WordTrace tailWord_7338603 prefixEnd_7338603 3768230671527056415712885 := by
  unfold tailWord_7338603
  simp only [CollatzResearch.WordTrace]
  refine ⟨267660840632502139454524463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178440560421668092969682975 267660840632502139454524463)
  ·
    refine ⟨401491260948753209181786695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267660840632502139454524463 401491260948753209181786695)
    ·
      refine ⟨602236891423129813772680043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401491260948753209181786695 602236891423129813772680043)
      ·
        refine ⟨903355337134694720659020065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602236891423129813772680043 903355337134694720659020065)
        ·
          refine ⟨677516502851021040494265049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 903355337134694720659020065 677516502851021040494265049)
          ·
            refine ⟨508137377138265780370698787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677516502851021040494265049 508137377138265780370698787)
            ·
              refine ⟨762206065707398670556048181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508137377138265780370698787 762206065707398670556048181)
              ·
                refine ⟨71456818660068625364629517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 762206065707398670556048181 71456818660068625364629517)
                ·
                  refine ⟨26796306997525734511736069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71456818660068625364629517 26796306997525734511736069)
                  ·
                    refine ⟨5024307562036075220950513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26796306997525734511736069 5024307562036075220950513)
                    ·
                      refine ⟨3768230671527056415712885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024307562036075220950513 3768230671527056415712885)
                      ·
                        rfl

theorem cell23_7338603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 3, 4, 2].length) (baseStart_7338603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338603 prefixEnd_7338603 := by exact prefixLift 7338603
  have htrace : WordTrace (prefixWord ++ tailWord_7338603) baseStart_7338603 baseEnd_7338603 := by
    simpa [prefixWord, tailWord_7338603, baseEnd_7338603] using wordTrace_append hprefix tailTrace_7338603
  have hstable : (prefixWord ++ tailWord_7338603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338603).length < 2 ^ (prefixWord ++ tailWord_7338603).sum := by decide
  have hdescent : baseEnd_7338603 < baseStart_7338603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338607 : List Nat := [1, 1, 2, 1, 3, 2, 6, 1, 1, 3, 2]
def baseStart_7338607 : Nat := 118140960795 + 7338607 * 2 ^ 59
def prefixEnd_7338607 : Nat := 4983230072969 + 3 ^ 40 * 7338607 * 2
def baseEnd_7338607 : Nat := 3768232725449674400062867

theorem tailTrace_7338607 : CollatzResearch.WordTrace tailWord_7338607 prefixEnd_7338607 3768232725449674400062867 := by
  unfold tailWord_7338607
  simp only [CollatzResearch.WordTrace]
  refine ⟨267660986524487648137670075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178440657682991765425113383 267660986524487648137670075)
  ·
    refine ⟨401491479786731472206505113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267660986524487648137670075 401491479786731472206505113)
    ·
      refine ⟨301118609840048604154878835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401491479786731472206505113 301118609840048604154878835)
      ·
        refine ⟨451677914760072906232318253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301118609840048604154878835 451677914760072906232318253)
        ·
          refine ⟨169379218035027339837119345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451677914760072906232318253 169379218035027339837119345)
          ·
            refine ⟨127034413526270504877839509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169379218035027339837119345 127034413526270504877839509)
            ·
              refine ⟨5954738134043929916148727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 127034413526270504877839509 5954738134043929916148727)
              ·
                refine ⟨8932107201065894874223091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5954738134043929916148727 8932107201065894874223091)
                ·
                  refine ⟨13398160801598842311334637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8932107201065894874223091 13398160801598842311334637)
                  ·
                    refine ⟨5024310300599565866750489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13398160801598842311334637 5024310300599565866750489)
                    ·
                      refine ⟨3768232725449674400062867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024310300599565866750489 3768232725449674400062867)
                      ·
                        rfl

theorem cell23_7338607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 6, 1, 1, 3, 2].length) (baseStart_7338607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338607 prefixEnd_7338607 := by exact prefixLift 7338607
  have htrace : WordTrace (prefixWord ++ tailWord_7338607) baseStart_7338607 baseEnd_7338607 := by
    simpa [prefixWord, tailWord_7338607, baseEnd_7338607] using wordTrace_append hprefix tailTrace_7338607
  have hstable : (prefixWord ++ tailWord_7338607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338607).length < 2 ^ (prefixWord ++ tailWord_7338607).sum := by decide
  have hdescent : baseEnd_7338607 < baseStart_7338607 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338616 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 3, 4, 4]
def baseStart_7338616 : Nat := 118140960795 + 7338616 * 2 ^ 59
def prefixEnd_7338616 : Nat := 4983230072969 + 3 ^ 40 * 7338616 * 2
def baseEnd_7338616 : Nat := 3768237346775564864850325

theorem tailTrace_7338616 : CollatzResearch.WordTrace tailWord_7338616 prefixEnd_7338616 3768237346775564864850325 := by
  unfold tailWord_7338616
  simp only [CollatzResearch.WordTrace]
  refine ⟨133830657390727521337373851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178440876520970028449831801 133830657390727521337373851)
  ·
    refine ⟨200745986086091282006060777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133830657390727521337373851 200745986086091282006060777)
    ·
      refine ⟨150559489564568461504545583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200745986086091282006060777 150559489564568461504545583)
      ·
        refine ⟨225839234346852692256818375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150559489564568461504545583 225839234346852692256818375)
        ·
          refine ⟨338758851520279038385227563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225839234346852692256818375 338758851520279038385227563)
          ·
            refine ⟨508138277280418557577841345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338758851520279038385227563 508138277280418557577841345)
            ·
              refine ⟨381103707960313918183381009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 508138277280418557577841345 381103707960313918183381009)
              ·
                refine ⟨285827780970235438637535757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381103707960313918183381009 285827780970235438637535757)
                ·
                  refine ⟨107185417863838289489075909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 285827780970235438637535757 107185417863838289489075909)
                  ·
                    refine ⟨20097265849469679279201733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107185417863838289489075909 20097265849469679279201733)
                    ·
                      refine ⟨3768237346775564864850325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20097265849469679279201733 3768237346775564864850325)
                      ·
                        rfl

theorem cell23_7338616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 3, 4, 4].length) (baseStart_7338616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338616 prefixEnd_7338616 := by exact prefixLift 7338616
  have htrace : WordTrace (prefixWord ++ tailWord_7338616) baseStart_7338616 baseEnd_7338616 := by
    simpa [prefixWord, tailWord_7338616, baseEnd_7338616] using wordTrace_append hprefix tailTrace_7338616
  have hstable : (prefixWord ++ tailWord_7338616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338616).length < 2 ^ (prefixWord ++ tailWord_7338616).sum := by decide
  have hdescent : baseEnd_7338616 < baseStart_7338616 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338653 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 1, 5, 3]
def baseStart_7338653 : Nat := 118140960795 + 7338653 * 2 ^ 59
def prefixEnd_7338653 : Nat := 4983230072969 + 3 ^ 40 * 7338653 * 2
def baseEnd_7338653 : Nat := 3768256345559781220087655

theorem tailTrace_7338653 : CollatzResearch.WordTrace tailWord_7338653 prefixEnd_7338653 3768256345559781220087655 := by
  unfold tailWord_7338653
  simp only [CollatzResearch.WordTrace]
  refine ⟨267662664282320997993844613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178441776188213998662563075 267662664282320997993844613)
  ·
    refine ⟨50186749552935187123845865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267662664282320997993844613 50186749552935187123845865)
    ·
      refine ⟨37640062164701390342884399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50186749552935187123845865 37640062164701390342884399)
      ·
        refine ⟨56460093247052085514326599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37640062164701390342884399 56460093247052085514326599)
        ·
          refine ⟨84690139870578128271489899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56460093247052085514326599 84690139870578128271489899)
          ·
            refine ⟨127035209805867192407234849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84690139870578128271489899 127035209805867192407234849)
            ·
              refine ⟨95276407354400394305426137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127035209805867192407234849 95276407354400394305426137)
              ·
                refine ⟨71457305515800295729069603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95276407354400394305426137 71457305515800295729069603)
                ·
                  refine ⟨107185958273700443593604405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71457305515800295729069603 107185958273700443593604405)
                  ·
                    refine ⟨10048683588159416586900413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107185958273700443593604405 10048683588159416586900413)
                    ·
                      refine ⟨3768256345559781220087655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10048683588159416586900413 3768256345559781220087655)
                      ·
                        rfl

theorem cell23_7338653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_7338653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338653 prefixEnd_7338653 := by exact prefixLift 7338653
  have htrace : WordTrace (prefixWord ++ tailWord_7338653) baseStart_7338653 baseEnd_7338653 := by
    simpa [prefixWord, tailWord_7338653, baseEnd_7338653] using wordTrace_append hprefix tailTrace_7338653
  have hstable : (prefixWord ++ tailWord_7338653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338653).length < 2 ^ (prefixWord ++ tailWord_7338653).sum := by decide
  have hdescent : baseEnd_7338653 < baseStart_7338653 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338737 : List Nat := [1, 2, 2, 2, 2, 2, 3, 4, 1, 4]
def baseStart_7338737 : Nat := 118140960795 + 7338737 * 2 ^ 59
def prefixEnd_7338737 : Nat := 4983230072969 + 3 ^ 40 * 7338737 * 2
def baseEnd_7338737 : Nat := 1256099825978252963812423

theorem tailTrace_7338737 : CollatzResearch.WordTrace tailWord_7338737 prefixEnd_7338737 1256099825978252963812423 := by
  unfold tailWord_7338737
  simp only [CollatzResearch.WordTrace]
  refine ⟨267665728014016680339902465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178443818676011120226601643 267665728014016680339902465)
  ·
    refine ⟨200749296010512510254926849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267665728014016680339902465 200749296010512510254926849)
    ·
      refine ⟨150561972007884382691195137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200749296010512510254926849 150561972007884382691195137)
      ·
        refine ⟨112921479005913287018396353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150561972007884382691195137 112921479005913287018396353)
        ·
          refine ⟨84691109254434965263797265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112921479005913287018396353 84691109254434965263797265)
          ·
            refine ⟨63518331940826223947847949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84691109254434965263797265 63518331940826223947847949)
            ·
              refine ⟨23819374477809833980442981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63518331940826223947847949 23819374477809833980442981)
              ·
                refine ⟨4466132714589343871333059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23819374477809833980442981 4466132714589343871333059)
                ·
                  refine ⟨6699199071884015806999589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466132714589343871333059 6699199071884015806999589)
                  ·
                    refine ⟨1256099825978252963812423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6699199071884015806999589 1256099825978252963812423)
                    ·
                      rfl

theorem cell23_7338737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 1, 4].length) (baseStart_7338737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338737 prefixEnd_7338737 := by exact prefixLift 7338737
  have htrace : WordTrace (prefixWord ++ tailWord_7338737) baseStart_7338737 baseEnd_7338737 := by
    simpa [prefixWord, tailWord_7338737, baseEnd_7338737] using wordTrace_append hprefix tailTrace_7338737
  have hstable : (prefixWord ++ tailWord_7338737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338737).length < 2 ^ (prefixWord ++ tailWord_7338737).sum := by decide
  have hdescent : baseEnd_7338737 < baseStart_7338737 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338743 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 3]
def baseStart_7338743 : Nat := 118140960795 + 7338743 * 2 ^ 59
def prefixEnd_7338743 : Nat := 4983230072969 + 3 ^ 40 * 7338743 * 2
def baseEnd_7338743 : Nat := 3768302558818685867962241

theorem tailTrace_7338743 : CollatzResearch.WordTrace tailWord_7338743 prefixEnd_7338743 3768302558818685867962241 := by
  unfold tailWord_7338743
  simp only [CollatzResearch.WordTrace]
  refine ⟨267665946851994943364620883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178443964567996628909747255 267665946851994943364620883)
  ·
    refine ⟨401498920277992415046931325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267665946851994943364620883 401498920277992415046931325)
    ·
      refine ⟨150562095104247155642599247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401498920277992415046931325 150562095104247155642599247)
      ·
        refine ⟨225843142656370733463898871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150562095104247155642599247 225843142656370733463898871)
        ·
          refine ⟨338764713984556100195848307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225843142656370733463898871 338764713984556100195848307)
          ·
            refine ⟨508147070976834150293772461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338764713984556100195848307 508147070976834150293772461)
            ·
              refine ⟨190555151616312806360164673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 508147070976834150293772461 190555151616312806360164673)
              ·
                refine ⟨142916363712234604770123505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190555151616312806360164673 142916363712234604770123505)
                ·
                  refine ⟨107187272784175953577592629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142916363712234604770123505 107187272784175953577592629)
                  ·
                    refine ⟨10048806823516495647899309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107187272784175953577592629 10048806823516495647899309)
                    ·
                      refine ⟨3768302558818685867962241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10048806823516495647899309 3768302558818685867962241)
                      ·
                        rfl

theorem cell23_7338743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_7338743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338743 prefixEnd_7338743 := by exact prefixLift 7338743
  have htrace : WordTrace (prefixWord ++ tailWord_7338743) baseStart_7338743 baseEnd_7338743 := by
    simpa [prefixWord, tailWord_7338743, baseEnd_7338743] using wordTrace_append hprefix tailTrace_7338743
  have hstable : (prefixWord ++ tailWord_7338743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338743).length < 2 ^ (prefixWord ++ tailWord_7338743).sum := by decide
  have hdescent : baseEnd_7338743 < baseStart_7338743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338814 : List Nat := [4, 2, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_7338814 : Nat := 118140960795 + 7338814 * 2 ^ 59
def prefixEnd_7338814 : Nat := 4983230072969 + 3 ^ 40 * 7338814 * 2
def baseEnd_7338814 : Nat := 1256113005315051696724805

theorem tailTrace_7338814 : CollatzResearch.WordTrace tailWord_7338814 prefixEnd_7338814 1256113005315051696724805 := by
  unfold tailWord_7338814
  simp only [CollatzResearch.WordTrace]
  refine ⟨33458567054342215311306937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178445690956491814993636997 33458567054342215311306937)
  ·
    refine ⟨25093925290756661483480203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33458567054342215311306937 25093925290756661483480203)
    ·
      refine ⟨37640887936134992225220305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25093925290756661483480203 37640887936134992225220305)
      ·
        refine ⟨28230665952101244168915229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37640887936134992225220305 28230665952101244168915229)
        ·
          refine ⟨10586499732037966563343211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28230665952101244168915229 10586499732037966563343211)
          ·
            refine ⟨15879749598056949845014817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10586499732037966563343211 15879749598056949845014817)
            ·
              refine ⟨11909812198542712383761113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15879749598056949845014817 11909812198542712383761113)
              ·
                refine ⟨8932359148907034287820835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11909812198542712383761113 8932359148907034287820835)
                ·
                  refine ⟨13398538723360551431731253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8932359148907034287820835 13398538723360551431731253)
                  ·
                    refine ⟨1256113005315051696724805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13398538723360551431731253 1256113005315051696724805)
                    ·
                      rfl

theorem cell23_7338814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_7338814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338814 prefixEnd_7338814 := by exact prefixLift 7338814
  have htrace : WordTrace (prefixWord ++ tailWord_7338814) baseStart_7338814 baseEnd_7338814 := by
    simpa [prefixWord, tailWord_7338814, baseEnd_7338814] using wordTrace_append hprefix tailTrace_7338814
  have hstable : (prefixWord ++ tailWord_7338814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338814).length < 2 ^ (prefixWord ++ tailWord_7338814).sum := by decide
  have hdescent : baseEnd_7338814 < baseStart_7338814 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338830 : List Nat := [4, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4]
def baseStart_7338830 : Nat := 118140960795 + 7338830 * 2 ^ 59
def prefixEnd_7338830 : Nat := 4983230072969 + 3 ^ 40 * 7338830 * 2
def baseEnd_7338830 : Nat := 3768347231635627027574341

theorem tailTrace_7338830 : CollatzResearch.WordTrace tailWord_7338830 prefixEnd_7338830 3768347231635627027574341 := by
  unfold tailWord_7338830
  simp only [CollatzResearch.WordTrace]
  refine ⟨33458640000334969652879743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178446080001786504815358629 33458640000334969652879743)
  ·
    refine ⟨50187960000502454479319615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33458640000334969652879743 50187960000502454479319615)
    ·
      refine ⟨75281940000753681718979423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50187960000502454479319615 75281940000753681718979423)
      ·
        refine ⟨112922910001130522578469135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75281940000753681718979423 112922910001130522578469135)
        ·
          refine ⟨169384365001695783867703703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112922910001130522578469135 169384365001695783867703703)
          ·
            refine ⟨254076547502543675801555555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169384365001695783867703703 254076547502543675801555555)
            ·
              refine ⟨381114821253815513702333333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254076547502543675801555555 381114821253815513702333333)
              ·
                refine ⟨17864757246272602204796875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 381114821253815513702333333 17864757246272602204796875)
                ·
                  refine ⟨26797135869408903307195313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17864757246272602204796875 26797135869408903307195313)
                  ·
                    refine ⟨20097851902056677480396485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26797135869408903307195313 20097851902056677480396485)
                    ·
                      refine ⟨3768347231635627027574341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20097851902056677480396485 3768347231635627027574341)
                      ·
                        rfl

theorem cell23_7338830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_7338830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338830 prefixEnd_7338830 := by exact prefixLift 7338830
  have htrace : WordTrace (prefixWord ++ tailWord_7338830) baseStart_7338830 baseEnd_7338830 := by
    simpa [prefixWord, tailWord_7338830, baseEnd_7338830] using wordTrace_append hprefix tailTrace_7338830
  have hstable : (prefixWord ++ tailWord_7338830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338830).length < 2 ^ (prefixWord ++ tailWord_7338830).sum := by decide
  have hdescent : baseEnd_7338830 < baseStart_7338830 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338837 : List Nat := [1, 3, 2, 2, 2, 1, 1, 5, 1, 2, 3]
def baseStart_7338837 : Nat := 118140960795 + 7338837 * 2 ^ 59
def prefixEnd_7338837 : Nat := 4983230072969 + 3 ^ 40 * 7338837 * 2
def baseEnd_7338837 : Nat := 3768350826000208500186809

theorem tailTrace_7338837 : CollatzResearch.WordTrace tailWord_7338837 prefixEnd_7338837 3768350826000208500186809 := by
  unfold tailWord_7338837
  simp only [CollatzResearch.WordTrace]
  refine ⟨267669375313654397418542765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178446250209102931612361843 267669375313654397418542765)
  ·
    refine ⟨100376015742620399031953537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267669375313654397418542765 100376015742620399031953537)
    ·
      refine ⟨75282011806965299273965153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100376015742620399031953537 75282011806965299273965153)
      ·
        refine ⟨56461508855223974455473865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75282011806965299273965153 56461508855223974455473865)
        ·
          refine ⟨42346131641417980841605399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56461508855223974455473865 42346131641417980841605399)
          ·
            refine ⟨63519197462126971262408099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42346131641417980841605399 63519197462126971262408099)
            ·
              refine ⟨95278796193190456893612149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63519197462126971262408099 95278796193190456893612149)
              ·
                refine ⟨8932387143111605333776139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95278796193190456893612149 8932387143111605333776139)
                ·
                  refine ⟨13398580714667408000664209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8932387143111605333776139 13398580714667408000664209)
                  ·
                    refine ⟨10048935536000556000498157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13398580714667408000664209 10048935536000556000498157)
                    ·
                      refine ⟨3768350826000208500186809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10048935536000556000498157 3768350826000208500186809)
                      ·
                        rfl

theorem cell23_7338837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_7338837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338837 prefixEnd_7338837 := by exact prefixLift 7338837
  have htrace : WordTrace (prefixWord ++ tailWord_7338837) baseStart_7338837 baseEnd_7338837 := by
    simpa [prefixWord, tailWord_7338837, baseEnd_7338837] using wordTrace_append hprefix tailTrace_7338837
  have hstable : (prefixWord ++ tailWord_7338837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338837).length < 2 ^ (prefixWord ++ tailWord_7338837).sum := by decide
  have hdescent : baseEnd_7338837 < baseStart_7338837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338851 : List Nat := [1, 1, 1, 5, 3, 3, 1, 1, 3, 2, 2]
def baseStart_7338851 : Nat := 118140960795 + 7338851 * 2 ^ 59
def prefixEnd_7338851 : Nat := 4983230072969 + 3 ^ 40 * 7338851 * 2
def baseEnd_7338851 : Nat := 3768358014729371445411745

theorem tailTrace_7338851 : CollatzResearch.WordTrace tailWord_7338851 prefixEnd_7338851 3768358014729371445411745 := by
  unfold tailWord_7338851
  simp only [CollatzResearch.WordTrace]
  refine ⟨267669885935603677809552407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178446590623735785206368271 267669885935603677809552407)
  ·
    refine ⟨401504828903405516714328611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267669885935603677809552407 401504828903405516714328611)
    ·
      refine ⟨602257243355108275071492917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401504828903405516714328611 602257243355108275071492917)
      ·
        refine ⟨56461616564541400787952461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 602257243355108275071492917 56461616564541400787952461)
        ·
          refine ⟨21173106211703025295482173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56461616564541400787952461 21173106211703025295482173)
          ·
            refine ⟨7939914829388634485805815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21173106211703025295482173 7939914829388634485805815)
            ·
              refine ⟨11909872244082951728708723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7939914829388634485805815 11909872244082951728708723)
              ·
                refine ⟨17864808366124427593063085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11909872244082951728708723 17864808366124427593063085)
                ·
                  refine ⟨6699303137296660347398657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17864808366124427593063085 6699303137296660347398657)
                  ·
                    refine ⟨5024477352972495260548993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6699303137296660347398657 5024477352972495260548993)
                    ·
                      refine ⟨3768358014729371445411745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024477352972495260548993 3768358014729371445411745)
                      ·
                        rfl

theorem cell23_7338851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_7338851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338851 prefixEnd_7338851 := by exact prefixLift 7338851
  have htrace : WordTrace (prefixWord ++ tailWord_7338851) baseStart_7338851 baseEnd_7338851 := by
    simpa [prefixWord, tailWord_7338851, baseEnd_7338851] using wordTrace_append hprefix tailTrace_7338851
  have hstable : (prefixWord ++ tailWord_7338851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338851).length < 2 ^ (prefixWord ++ tailWord_7338851).sum := by decide
  have hdescent : baseEnd_7338851 < baseStart_7338851 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338902 : List Nat := [5, 3, 1, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_7338902 : Nat := 118140960795 + 7338902 * 2 ^ 59
def prefixEnd_7338902 : Nat := 4983230072969 + 3 ^ 40 * 7338902 * 2
def baseEnd_7338902 : Nat := 3768384202242750745874011

theorem tailTrace_7338902 : CollatzResearch.WordTrace tailWord_7338902 prefixEnd_7338902 3768384202242750745874011 := by
  unfold tailWord_7338902
  simp only [CollatzResearch.WordTrace]
  refine ⟨16729484128651182094978685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178447830705612609013105973 16729484128651182094978685)
  ·
    refine ⟨6273556548244193285617007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16729484128651182094978685 6273556548244193285617007)
    ·
      refine ⟨9410334822366289928425511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6273556548244193285617007 9410334822366289928425511)
      ·
        refine ⟨14115502233549434892638267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9410334822366289928425511 14115502233549434892638267)
        ·
          refine ⟨21173253350324152338957401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14115502233549434892638267 21173253350324152338957401)
          ·
            refine ⟨15879940012743114254218051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21173253350324152338957401 15879940012743114254218051)
            ·
              refine ⟨23819910019114671381327077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15879940012743114254218051 23819910019114671381327077)
              ·
                refine ⟨4466233128584000883998827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23819910019114671381327077 4466233128584000883998827)
                ·
                  refine ⟨6699349692876001325998241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466233128584000883998827 6699349692876001325998241)
                  ·
                    refine ⟨5024512269657000994498681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6699349692876001325998241 5024512269657000994498681)
                    ·
                      refine ⟨3768384202242750745874011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024512269657000994498681 3768384202242750745874011)
                      ·
                        rfl

theorem cell23_7338902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_7338902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338902 prefixEnd_7338902 := by exact prefixLift 7338902
  have htrace : WordTrace (prefixWord ++ tailWord_7338902) baseStart_7338902 baseEnd_7338902 := by
    simpa [prefixWord, tailWord_7338902, baseEnd_7338902] using wordTrace_append hprefix tailTrace_7338902
  have hstable : (prefixWord ++ tailWord_7338902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338902).length < 2 ^ (prefixWord ++ tailWord_7338902).sum := by decide
  have hdescent : baseEnd_7338902 < baseStart_7338902 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338958 : List Nat := [4, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2]
def baseStart_7338958 : Nat := 118140960795 + 7338958 * 2 ^ 59
def prefixEnd_7338958 : Nat := 4983230072969 + 3 ^ 40 * 7338958 * 2
def baseEnd_7338958 : Nat := 3768412957159402526773753

theorem tailTrace_7338958 : CollatzResearch.WordTrace tailWord_7338958 prefixEnd_7338958 3768412957159402526773753 := by
  unfold tailWord_7338958
  simp only [CollatzResearch.WordTrace]
  refine ⟨33459223568277004385462191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178449192364144023389131685 33459223568277004385462191)
  ·
    refine ⟨50188835352415506578193287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33459223568277004385462191 50188835352415506578193287)
    ·
      refine ⟨75283253028623259867289931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50188835352415506578193287 75283253028623259867289931)
      ·
        refine ⟨112924879542934889800934897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75283253028623259867289931 112924879542934889800934897)
        ·
          refine ⟨84693659657201167350701173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112924879542934889800934897 84693659657201167350701173)
          ·
            refine ⟨7940030592862609439128235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84693659657201167350701173 7940030592862609439128235)
            ·
              refine ⟨11910045889293914158692353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7940030592862609439128235 11910045889293914158692353)
              ·
                refine ⟨8932534416970435619019265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11910045889293914158692353 8932534416970435619019265)
                ·
                  refine ⟨6699400812727826714264449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8932534416970435619019265 6699400812727826714264449)
                  ·
                    refine ⟨5024550609545870035698337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6699400812727826714264449 5024550609545870035698337)
                    ·
                      refine ⟨3768412957159402526773753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024550609545870035698337 3768412957159402526773753)
                      ·
                        rfl

theorem cell23_7338958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2].length) (baseStart_7338958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338958 prefixEnd_7338958 := by exact prefixLift 7338958
  have htrace : WordTrace (prefixWord ++ tailWord_7338958) baseStart_7338958 baseEnd_7338958 := by
    simpa [prefixWord, tailWord_7338958, baseEnd_7338958] using wordTrace_append hprefix tailTrace_7338958
  have hstable : (prefixWord ++ tailWord_7338958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338958).length < 2 ^ (prefixWord ++ tailWord_7338958).sum := by decide
  have hdescent : baseEnd_7338958 < baseStart_7338958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338960 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 4, 5]
def baseStart_7338960 : Nat := 118140960795 + 7338960 * 2 ^ 59
def prefixEnd_7338960 : Nat := 4983230072969 + 3 ^ 40 * 7338960 * 2
def baseEnd_7338960 : Nat := 1256137994706903839649581

theorem tailTrace_7338960 : CollatzResearch.WordTrace tailWord_7338960 prefixEnd_7338960 1256137994706903839649581 := by
  unfold tailWord_7338960
  simp only [CollatzResearch.WordTrace]
  refine ⟨133836930746104394712635167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178449240994805859616846889 133836930746104394712635167)
  ·
    refine ⟨200755396119156592068952751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133836930746104394712635167 200755396119156592068952751)
    ·
      refine ⟨301133094178734888103429127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200755396119156592068952751 301133094178734888103429127)
      ·
        refine ⟨451699641268102332155143691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301133094178734888103429127 451699641268102332155143691)
        ·
          refine ⟨677549461902153498232715537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451699641268102332155143691 677549461902153498232715537)
          ·
            refine ⟨508162096426615123674536653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 677549461902153498232715537 508162096426615123674536653)
            ·
              refine ⟨190560786159980671377951245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 508162096426615123674536653 190560786159980671377951245)
              ·
                refine ⟨71460294809992751766731717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190560786159980671377951245 71460294809992751766731717)
                ·
                  refine ⟨13398805276873640956262197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71460294809992751766731717 13398805276873640956262197)
                  ·
                    refine ⟨1256137994706903839649581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13398805276873640956262197 1256137994706903839649581)
                    ·
                      rfl

theorem cell23_7338960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 4, 5].length) (baseStart_7338960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338960 prefixEnd_7338960 := by exact prefixLift 7338960
  have htrace : WordTrace (prefixWord ++ tailWord_7338960) baseStart_7338960 baseEnd_7338960 := by
    simpa [prefixWord, tailWord_7338960, baseEnd_7338960] using wordTrace_append hprefix tailTrace_7338960
  have hstable : (prefixWord ++ tailWord_7338960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338960).length < 2 ^ (prefixWord ++ tailWord_7338960).sum := by decide
  have hdescent : baseEnd_7338960 < baseStart_7338960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338964 : List Nat := [2, 4, 1, 2, 1, 2, 2, 4, 5]
def baseStart_7338964 : Nat := 118140960795 + 7338964 * 2 ^ 59
def prefixEnd_7338964 : Nat := 4983230072969 + 3 ^ 40 * 7338964 * 2
def baseEnd_7338964 : Nat := 418712893115925500366525

theorem tailTrace_7338964 : CollatzResearch.WordTrace tailWord_7338964 prefixEnd_7338964 418712893115925500366525 := by
  unfold tailWord_7338964
  simp only [CollatzResearch.WordTrace]
  refine ⟨133837003692097149054207973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178449338256129532072277297 133837003692097149054207973)
  ·
    refine ⟨25094438192268215447663995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133837003692097149054207973 25094438192268215447663995)
    ·
      refine ⟨37641657288402323171495993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25094438192268215447663995 37641657288402323171495993)
      ·
        refine ⟨28231242966301742378621995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37641657288402323171495993 28231242966301742378621995)
        ·
          refine ⟨42346864449452613567932993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28231242966301742378621995 42346864449452613567932993)
          ·
            refine ⟨31760148337089460175949745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42346864449452613567932993 31760148337089460175949745)
            ·
              refine ⟨23820111252817095131962309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31760148337089460175949745 23820111252817095131962309)
              ·
                refine ⟨4466270859903205337242933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23820111252817095131962309 4466270859903205337242933)
                ·
                  refine ⟨418712893115925500366525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4466270859903205337242933 418712893115925500366525)
                  ·
                    rfl

theorem cell23_7338964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_7338964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338964 prefixEnd_7338964 := by exact prefixLift 7338964
  have htrace : WordTrace (prefixWord ++ tailWord_7338964) baseStart_7338964 baseEnd_7338964 := by
    simpa [prefixWord, tailWord_7338964, baseEnd_7338964] using wordTrace_append hprefix tailTrace_7338964
  have hstable : (prefixWord ++ tailWord_7338964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338964).length < 2 ^ (prefixWord ++ tailWord_7338964).sum := by decide
  have hdescent : baseEnd_7338964 < baseStart_7338964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7338967 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 2, 5, 2]
def baseStart_7338967 : Nat := 118140960795 + 7338967 * 2 ^ 59
def prefixEnd_7338967 : Nat := 4983230072969 + 3 ^ 40 * 7338967 * 2
def baseEnd_7338967 : Nat := 3768417578485292991561211

theorem tailTrace_7338967 : CollatzResearch.WordTrace tailWord_7338967 prefixEnd_7338967 3768417578485292991561211 := by
  unfold tailWord_7338967
  simp only [CollatzResearch.WordTrace]
  refine ⟨267674116803183429620775155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178449411202122286413850103 267674116803183429620775155)
  ·
    refine ⟨401511175204775144431162733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267674116803183429620775155 401511175204775144431162733)
    ·
      refine ⟨150566690701790679161686025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401511175204775144431162733 150566690701790679161686025)
      ·
        refine ⟨112925018026343009371264519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150566690701790679161686025 112925018026343009371264519)
        ·
          refine ⟨169387527039514514056896779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112925018026343009371264519 169387527039514514056896779)
          ·
            refine ⟨254081290559271771085345169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169387527039514514056896779 254081290559271771085345169)
            ·
              refine ⟨190560967919453828314008877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254081290559271771085345169 190560967919453828314008877)
              ·
                refine ⟨71460362969795185617753329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190560967919453828314008877 71460362969795185617753329)
                ·
                  refine ⟨53595272227346389213314997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71460362969795185617753329 53595272227346389213314997)
                  ·
                    refine ⟨5024556771313723988748281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53595272227346389213314997 5024556771313723988748281)
                    ·
                      refine ⟨3768417578485292991561211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024556771313723988748281 3768417578485292991561211)
                      ·
                        rfl

theorem cell23_7338967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 5, 2].length) (baseStart_7338967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7338967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7338967 prefixEnd_7338967 := by exact prefixLift 7338967
  have htrace : WordTrace (prefixWord ++ tailWord_7338967) baseStart_7338967 baseEnd_7338967 := by
    simpa [prefixWord, tailWord_7338967, baseEnd_7338967] using wordTrace_append hprefix tailTrace_7338967
  have hstable : (prefixWord ++ tailWord_7338967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7338967).length < 2 ^ (prefixWord ++ tailWord_7338967).sum := by decide
  have hdescent : baseEnd_7338967 < baseStart_7338967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7338967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339000 : List Nat := [2, 1, 2, 1, 1, 3, 1, 2, 2, 3, 5]
def baseStart_7339000 : Nat := 118140960795 + 7339000 * 2 ^ 59
def prefixEnd_7339000 : Nat := 4983230072969 + 3 ^ 40 * 7339000 * 2
def baseEnd_7339000 : Nat := 3768434523346891362448559

theorem tailTrace_7339000 : CollatzResearch.WordTrace tailWord_7339000 prefixEnd_7339000 3768434523346891362448559 := by
  unfold tailWord_7339000
  simp only [CollatzResearch.WordTrace]
  refine ⟨133837660206031938128363227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178450213608042584171150969 133837660206031938128363227)
  ·
    refine ⟨200756490309047907192544841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133837660206031938128363227 200756490309047907192544841)
    ·
      refine ⟨150567367731785930394408631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200756490309047907192544841 150567367731785930394408631)
      ·
        refine ⟨225851051597678895591612947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150567367731785930394408631 225851051597678895591612947)
        ·
          refine ⟨338776577396518343387419421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225851051597678895591612947 338776577396518343387419421)
          ·
            refine ⟨127041216523694378770282283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338776577396518343387419421 127041216523694378770282283)
            ·
              refine ⟨190561824785541568155423425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127041216523694378770282283 190561824785541568155423425)
              ·
                refine ⟨142921368589156176116567569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190561824785541568155423425 142921368589156176116567569)
                ·
                  refine ⟨107191026441867132087425677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142921368589156176116567569 107191026441867132087425677)
                  ·
                    refine ⟨40196634915700174532784629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107191026441867132087425677 40196634915700174532784629)
                    ·
                      refine ⟨3768434523346891362448559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40196634915700174532784629 3768434523346891362448559)
                      ·
                        rfl

theorem cell23_7339000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 2, 3, 5].length) (baseStart_7339000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339000 prefixEnd_7339000 := by exact prefixLift 7339000
  have htrace : WordTrace (prefixWord ++ tailWord_7339000) baseStart_7339000 baseEnd_7339000 := by
    simpa [prefixWord, tailWord_7339000, baseEnd_7339000] using wordTrace_append hprefix tailTrace_7339000
  have hstable : (prefixWord ++ tailWord_7339000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339000).length < 2 ^ (prefixWord ++ tailWord_7339000).sum := by decide
  have hdescent : baseEnd_7339000 < baseStart_7339000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339026 : List Nat := [3, 2, 5, 1, 2, 1, 2, 1, 2, 2, 2]
def baseStart_7339026 : Nat := 118140960795 + 7339026 * 2 ^ 59
def prefixEnd_7339026 : Nat := 4983230072969 + 3 ^ 40 * 7339026 * 2
def baseEnd_7339026 : Nat := 3768447873843908260723441

theorem tailTrace_7339026 : CollatzResearch.WordTrace tailWord_7339026 prefixEnd_7339026 3768447873843908260723441 := by
  unfold tailWord_7339026
  simp only [CollatzResearch.WordTrace]
  refine ⟨66919067177492420674293233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178450845806646455131448621 66919067177492420674293233)
  ·
    refine ⟨50189300383119315505719925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66919067177492420674293233 50189300383119315505719925)
    ·
      refine ⟨4705246910917435828661243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 50189300383119315505719925 4705246910917435828661243)
      ·
        refine ⟨7057870366376153742991865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4705246910917435828661243 7057870366376153742991865)
        ·
          refine ⟨5293402774782115307243899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7057870366376153742991865 5293402774782115307243899)
          ·
            refine ⟨7940104162173172960865849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5293402774782115307243899 7940104162173172960865849)
            ·
              refine ⟨5955078121629879720649387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7940104162173172960865849 5955078121629879720649387)
              ·
                refine ⟨8932617182444819580974081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5955078121629879720649387 8932617182444819580974081)
                ·
                  refine ⟨6699462886833614685730561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8932617182444819580974081 6699462886833614685730561)
                  ·
                    refine ⟨5024597165125211014297921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6699462886833614685730561 5024597165125211014297921)
                    ·
                      refine ⟨3768447873843908260723441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024597165125211014297921 3768447873843908260723441)
                      ·
                        rfl

theorem cell23_7339026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_7339026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339026 prefixEnd_7339026 := by exact prefixLift 7339026
  have htrace : WordTrace (prefixWord ++ tailWord_7339026) baseStart_7339026 baseEnd_7339026 := by
    simpa [prefixWord, tailWord_7339026, baseEnd_7339026] using wordTrace_append hprefix tailTrace_7339026
  have hstable : (prefixWord ++ tailWord_7339026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339026).length < 2 ^ (prefixWord ++ tailWord_7339026).sum := by decide
  have hdescent : baseEnd_7339026 < baseStart_7339026 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339104 : List Nat := [2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 4]
def baseStart_7339104 : Nat := 118140960795 + 7339104 * 2 ^ 59
def prefixEnd_7339104 : Nat := 4983230072969 + 3 ^ 40 * 7339104 * 2
def baseEnd_7339104 : Nat := 3768487925334958955548081

theorem tailTrace_7339104 : CollatzResearch.WordTrace tailWord_7339104 prefixEnd_7339104 3768487925334958955548081 := by
  unfold tailWord_7339104
  simp only [CollatzResearch.WordTrace]
  refine ⟨133839556801843551009256183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178452742402458068012341577 133839556801843551009256183)
  ·
    refine ⟨200759335202765326513884275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133839556801843551009256183 200759335202765326513884275)
    ·
      refine ⟨301139002804147989770826413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200759335202765326513884275 301139002804147989770826413)
      ·
        refine ⟨112927126051555496164059905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301139002804147989770826413 112927126051555496164059905)
        ·
          refine ⟨84695344538666622123044929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112927126051555496164059905 84695344538666622123044929)
          ·
            refine ⟨63521508403999966592283697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84695344538666622123044929 63521508403999966592283697)
            ·
              refine ⟨47641131302999974944212773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63521508403999966592283697 47641131302999974944212773)
              ·
                refine ⟨8932712119312495302039895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47641131302999974944212773 8932712119312495302039895)
                ·
                  refine ⟨13399068178968742953059843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8932712119312495302039895 13399068178968742953059843)
                  ·
                    refine ⟨20098602268453114429589765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13399068178968742953059843 20098602268453114429589765)
                    ·
                      refine ⟨3768487925334958955548081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20098602268453114429589765 3768487925334958955548081)
                      ·
                        rfl

theorem cell23_7339104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_7339104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339104 prefixEnd_7339104 := by exact prefixLift 7339104
  have htrace : WordTrace (prefixWord ++ tailWord_7339104) baseStart_7339104 baseEnd_7339104 := by
    simpa [prefixWord, tailWord_7339104, baseEnd_7339104] using wordTrace_append hprefix tailTrace_7339104
  have hstable : (prefixWord ++ tailWord_7339104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339104).length < 2 ^ (prefixWord ++ tailWord_7339104).sum := by decide
  have hdescent : baseEnd_7339104 < baseStart_7339104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339114 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 1, 6]
def baseStart_7339114 : Nat := 118140960795 + 7339114 * 2 ^ 59
def prefixEnd_7339114 : Nat := 4983230072969 + 3 ^ 40 * 7339114 * 2
def baseEnd_7339114 : Nat := 1256164353380501305474345

theorem tailTrace_7339114 : CollatzResearch.WordTrace tailWord_7339114 prefixEnd_7339114 1256164353380501305474345 := by
  unfold tailWord_7339114
  simp only [CollatzResearch.WordTrace]
  refine ⟨66919869583412718431594099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178452985555767249150917597 66919869583412718431594099)
  ·
    refine ⟨100379804375119077647391149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66919869583412718431594099 100379804375119077647391149)
    ·
      refine ⟨37642426640669654117771681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100379804375119077647391149 37642426640669654117771681)
      ·
        refine ⟨28231819980502240588328761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37642426640669654117771681 28231819980502240588328761)
        ·
          refine ⟨21173864985376680441246571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28231819980502240588328761 21173864985376680441246571)
          ·
            refine ⟨31760797478065020661869857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21173864985376680441246571 31760797478065020661869857)
            ·
              refine ⟨23820598108548765496402393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31760797478065020661869857 23820598108548765496402393)
              ·
                refine ⟨17865448581411574122301795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23820598108548765496402393 17865448581411574122301795)
                ·
                  refine ⟨26798172872117361183452693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17865448581411574122301795 26798172872117361183452693)
                  ·
                    refine ⟨1256164353380501305474345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26798172872117361183452693 1256164353380501305474345)
                    ·
                      rfl

theorem cell23_7339114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 1, 6].length) (baseStart_7339114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339114 prefixEnd_7339114 := by exact prefixLift 7339114
  have htrace : WordTrace (prefixWord ++ tailWord_7339114) baseStart_7339114 baseEnd_7339114 := by
    simpa [prefixWord, tailWord_7339114, baseEnd_7339114] using wordTrace_append hprefix tailTrace_7339114
  have hstable : (prefixWord ++ tailWord_7339114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339114).length < 2 ^ (prefixWord ++ tailWord_7339114).sum := by decide
  have hdescent : baseEnd_7339114 < baseStart_7339114 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339118 : List Nat := [4, 1, 2, 2, 1, 4, 2, 1, 1, 5]
def baseStart_7339118 : Nat := 118140960795 + 7339118 * 2 ^ 59
def prefixEnd_7339118 : Nat := 4983230072969 + 3 ^ 40 * 7339118 * 2
def baseEnd_7339118 : Nat := 1256165038021373966924339

theorem tailTrace_7339118 : CollatzResearch.WordTrace tailWord_7339118 prefixEnd_7339118 1256165038021373966924339 := by
  unfold tailWord_7339118
  simp only [CollatzResearch.WordTrace]
  refine ⟨33459953028204547801190251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178453082817090921606348005 33459953028204547801190251)
  ·
    refine ⟨50189929542306821701785377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33459953028204547801190251 50189929542306821701785377)
    ·
      refine ⟨37642447156730116276339033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50189929542306821701785377 37642447156730116276339033)
      ·
        refine ⟨28231835367547587207254275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37642447156730116276339033 28231835367547587207254275)
        ·
          refine ⟨42347753051321380810881413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28231835367547587207254275 42347753051321380810881413)
          ·
            refine ⟨7940203697122758902040265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42347753051321380810881413 7940203697122758902040265)
            ·
              refine ⟨5955152772842069176530199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7940203697122758902040265 5955152772842069176530199)
              ·
                refine ⟨8932729159263103764795299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5955152772842069176530199 8932729159263103764795299)
                ·
                  refine ⟨13399093738894655647192949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8932729159263103764795299 13399093738894655647192949)
                  ·
                    refine ⟨1256165038021373966924339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13399093738894655647192949 1256165038021373966924339)
                    ·
                      rfl

theorem cell23_7339118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_7339118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339118 prefixEnd_7339118 := by exact prefixLift 7339118
  have htrace : WordTrace (prefixWord ++ tailWord_7339118) baseStart_7339118 baseEnd_7339118 := by
    simpa [prefixWord, tailWord_7339118, baseEnd_7339118] using wordTrace_append hprefix tailTrace_7339118
  have hstable : (prefixWord ++ tailWord_7339118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339118).length < 2 ^ (prefixWord ++ tailWord_7339118).sum := by decide
  have hdescent : baseEnd_7339118 < baseStart_7339118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339172 : List Nat := [2, 3, 1, 2, 3, 3, 1, 3, 1, 2, 2]
def baseStart_7339172 : Nat := 118140960795 + 7339172 * 2 ^ 59
def prefixEnd_7339172 : Nat := 4983230072969 + 3 ^ 40 * 7339172 * 2
def baseEnd_7339172 : Nat := 3768522842019464689497769

theorem tailTrace_7339172 : CollatzResearch.WordTrace tailWord_7339172 prefixEnd_7339172 3768522842019464689497769 := by
  unfold tailWord_7339172
  simp only [CollatzResearch.WordTrace]
  refine ⟨133840796883720374815993885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178454395844960499754658513 133840796883720374815993885)
  ·
    refine ⟨50190298831395140555997707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133840796883720374815993885 50190298831395140555997707)
    ·
      refine ⟨75285448247092710833996561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50190298831395140555997707 75285448247092710833996561)
      ·
        refine ⟨56464086185319533125497421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75285448247092710833996561 56464086185319533125497421)
        ·
          refine ⟨21174032319494824922061533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56464086185319533125497421 21174032319494824922061533)
          ·
            refine ⟨7940262119810559345773075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21174032319494824922061533 7940262119810559345773075)
            ·
              refine ⟨11910393179715839018659613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7940262119810559345773075 11910393179715839018659613)
              ·
                refine ⟨4466397442393439631997355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11910393179715839018659613 4466397442393439631997355)
                ·
                  refine ⟨6699596163590159447996033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466397442393439631997355 6699596163590159447996033)
                  ·
                    refine ⟨5024697122692619585997025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6699596163590159447996033 5024697122692619585997025)
                    ·
                      refine ⟨3768522842019464689497769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024697122692619585997025 3768522842019464689497769)
                      ·
                        rfl

theorem cell23_7339172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_7339172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339172 prefixEnd_7339172 := by exact prefixLift 7339172
  have htrace : WordTrace (prefixWord ++ tailWord_7339172) baseStart_7339172 baseEnd_7339172 := by
    simpa [prefixWord, tailWord_7339172, baseEnd_7339172] using wordTrace_append hprefix tailTrace_7339172
  have hstable : (prefixWord ++ tailWord_7339172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339172).length < 2 ^ (prefixWord ++ tailWord_7339172).sum := by decide
  have hdescent : baseEnd_7339172 < baseStart_7339172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339177 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 6, 3, 4]
def baseStart_7339177 : Nat := 118140960795 + 7339177 * 2 ^ 59
def prefixEnd_7339177 : Nat := 4983230072969 + 3 ^ 40 * 7339177 * 2
def baseEnd_7339177 : Nat := 3768525409422737169935245

theorem tailTrace_7339177 : CollatzResearch.WordTrace tailWord_7339177 prefixEnd_7339177 3768525409422737169935245 := by
  unfold tailWord_7339177
  simp only [CollatzResearch.WordTrace]
  refine ⟨267681776132422635485919785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178454517421615090323946523 267681776132422635485919785)
  ·
    refine ⟨200761332099316976614439839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267681776132422635485919785 200761332099316976614439839)
    ·
      refine ⟨301141998148975464921659759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200761332099316976614439839 301141998148975464921659759)
      ·
        refine ⟨451712997223463197382489639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301141998148975464921659759 451712997223463197382489639)
        ·
          refine ⟨677569495835194796073734459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451712997223463197382489639 677569495835194796073734459)
          ·
            refine ⟨1016354243752792194110601689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677569495835194796073734459 1016354243752792194110601689)
            ·
              refine ⟨762265682814594145582951267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1016354243752792194110601689 762265682814594145582951267)
              ·
                refine ⟨1143398524221891218374426901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762265682814594145582951267 1143398524221891218374426901)
                ·
                  refine ⟨53596805822901150861301261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1143398524221891218374426901 53596805822901150861301261)
                  ·
                    refine ⟨20098802183587931572987973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53596805822901150861301261 20098802183587931572987973)
                    ·
                      refine ⟨3768525409422737169935245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20098802183587931572987973 3768525409422737169935245)
                      ·
                        rfl

theorem cell23_7339177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_7339177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339177 prefixEnd_7339177 := by exact prefixLift 7339177
  have htrace : WordTrace (prefixWord ++ tailWord_7339177) baseStart_7339177 baseEnd_7339177 := by
    simpa [prefixWord, tailWord_7339177, baseEnd_7339177] using wordTrace_append hprefix tailTrace_7339177
  have hstable : (prefixWord ++ tailWord_7339177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339177).length < 2 ^ (prefixWord ++ tailWord_7339177).sum := by decide
  have hdescent : baseEnd_7339177 < baseStart_7339177 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339187 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 4, 6]
def baseStart_7339187 : Nat := 118140960795 + 7339187 * 2 ^ 59
def prefixEnd_7339187 : Nat := 4983230072969 + 3 ^ 40 * 7339187 * 2
def baseEnd_7339187 : Nat := 1256176848076427376936733

theorem tailTrace_7339187 : CollatzResearch.WordTrace tailWord_7339187 prefixEnd_7339187 1256176848076427376936733 := by
  unfold tailWord_7339187
  simp only [CollatzResearch.WordTrace]
  refine ⟨267682140862386407193783815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178454760574924271462522543 267682140862386407193783815)
  ·
    refine ⟨401523211293579610790675723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267682140862386407193783815 401523211293579610790675723)
    ·
      refine ⟨602284816940369416186013585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401523211293579610790675723 602284816940369416186013585)
      ·
        refine ⟨451713612705277062139510189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602284816940369416186013585 451713612705277062139510189)
        ·
          refine ⟨169392604764478898302316321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451713612705277062139510189 169392604764478898302316321)
          ·
            refine ⟨127044453573359173726737241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169392604764478898302316321 127044453573359173726737241)
            ·
              refine ⟨95283340180019380295052931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127044453573359173726737241 95283340180019380295052931)
              ·
                refine ⟨142925010270029070442579397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95283340180019380295052931 142925010270029070442579397)
                ·
                  refine ⟨26798439425630450707983637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142925010270029070442579397 26798439425630450707983637)
                  ·
                    refine ⟨1256176848076427376936733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26798439425630450707983637 1256176848076427376936733)
                    ·
                      rfl

theorem cell23_7339187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 6].length) (baseStart_7339187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339187 prefixEnd_7339187 := by exact prefixLift 7339187
  have htrace : WordTrace (prefixWord ++ tailWord_7339187) baseStart_7339187 baseEnd_7339187 := by
    simpa [prefixWord, tailWord_7339187, baseEnd_7339187] using wordTrace_append hprefix tailTrace_7339187
  have hstable : (prefixWord ++ tailWord_7339187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339187).length < 2 ^ (prefixWord ++ tailWord_7339187).sum := by decide
  have hdescent : baseEnd_7339187 < baseStart_7339187 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339207 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_7339207 : Nat := 118140960795 + 7339207 * 2 ^ 59
def prefixEnd_7339207 : Nat := 4983230072969 + 3 ^ 40 * 7339207 * 2
def baseEnd_7339207 : Nat := 3768540813842372052560107

theorem tailTrace_7339207 : CollatzResearch.WordTrace tailWord_7339207 prefixEnd_7339207 3768540813842372052560107 := by
  unfold tailWord_7339207
  simp only [CollatzResearch.WordTrace]
  refine ⟨267682870322313950609511875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178455246881542633739674583 267682870322313950609511875)
  ·
    refine ⟨401524305483470925914267813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267682870322313950609511875 401524305483470925914267813)
    ·
      refine ⟨75285807278150798608925215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401524305483470925914267813 75285807278150798608925215)
      ·
        refine ⟨112928710917226197913387823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75285807278150798608925215 112928710917226197913387823)
        ·
          refine ⟨169393066375839296870081735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112928710917226197913387823 169393066375839296870081735)
          ·
            refine ⟨254089599563758945305122603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169393066375839296870081735 254089599563758945305122603)
            ·
              refine ⟨381134399345638417957683905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 254089599563758945305122603 381134399345638417957683905)
              ·
                refine ⟨285850799509228813468262929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 381134399345638417957683905 285850799509228813468262929)
                ·
                  refine ⟨214388099631921610101197197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285850799509228813468262929 214388099631921610101197197)
                  ·
                    refine ⟨80395537361970603787948949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214388099631921610101197197 80395537361970603787948949)
                    ·
                      refine ⟨3768540813842372052560107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80395537361970603787948949 3768540813842372052560107)
                      ·
                        rfl

theorem cell23_7339207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_7339207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339207 prefixEnd_7339207 := by exact prefixLift 7339207
  have htrace : WordTrace (prefixWord ++ tailWord_7339207) baseStart_7339207 baseEnd_7339207 := by
    simpa [prefixWord, tailWord_7339207, baseEnd_7339207] using wordTrace_append hprefix tailTrace_7339207
  have hstable : (prefixWord ++ tailWord_7339207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339207).length < 2 ^ (prefixWord ++ tailWord_7339207).sum := by decide
  have hdescent : baseEnd_7339207 < baseStart_7339207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339211 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 6, 2, 2]
def baseStart_7339211 : Nat := 118140960795 + 7339211 * 2 ^ 59
def prefixEnd_7339211 : Nat := 4983230072969 + 3 ^ 40 * 7339211 * 2
def baseEnd_7339211 : Nat := 3768542867764990036910089

theorem tailTrace_7339211 : CollatzResearch.WordTrace tailWord_7339211 prefixEnd_7339211 3768542867764990036910089 := by
  unfold tailWord_7339211
  simp only [CollatzResearch.WordTrace]
  refine ⟨267683016214299459292657487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178455344142866306195104991 267683016214299459292657487)
  ·
    refine ⟨401524524321449188938986231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267683016214299459292657487 401524524321449188938986231)
    ·
      refine ⟨602286786482173783408479347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401524524321449188938986231 602286786482173783408479347)
      ·
        refine ⟨903430179723260675112719021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602286786482173783408479347 903430179723260675112719021)
        ·
          refine ⟨338786317396222753167269633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 903430179723260675112719021 338786317396222753167269633)
          ·
            refine ⟨254089738047167064875452225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338786317396222753167269633 254089738047167064875452225)
            ·
              refine ⟨190567303535375298656589169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254089738047167064875452225 190567303535375298656589169)
              ·
                refine ⟨142925477651531473992441877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190567303535375298656589169 142925477651531473992441877)
                ·
                  refine ⟨6699631764915537843395713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 142925477651531473992441877 6699631764915537843395713)
                  ·
                    refine ⟨5024723823686653382546785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6699631764915537843395713 5024723823686653382546785)
                    ·
                      refine ⟨3768542867764990036910089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024723823686653382546785 3768542867764990036910089)
                      ·
                        rfl

theorem cell23_7339211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 6, 2, 2].length) (baseStart_7339211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339211 prefixEnd_7339211 := by exact prefixLift 7339211
  have htrace : WordTrace (prefixWord ++ tailWord_7339211) baseStart_7339211 baseEnd_7339211 := by
    simpa [prefixWord, tailWord_7339211, baseEnd_7339211] using wordTrace_append hprefix tailTrace_7339211
  have hstable : (prefixWord ++ tailWord_7339211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339211).length < 2 ^ (prefixWord ++ tailWord_7339211).sum := by decide
  have hdescent : baseEnd_7339211 < baseStart_7339211 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339217 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 9]
def baseStart_7339217 : Nat := 118140960795 + 7339217 * 2 ^ 59
def prefixEnd_7339217 : Nat := 4983230072969 + 3 ^ 40 * 7339217 * 2
def baseEnd_7339217 : Nat := 418727327627657445937229

theorem tailTrace_7339217 : CollatzResearch.WordTrace tailWord_7339217 prefixEnd_7339217 418727327627657445937229 := by
  unfold tailWord_7339217
  simp only [CollatzResearch.WordTrace]
  refine ⟨267683235052277722317375905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178455490034851814878250603 267683235052277722317375905)
  ·
    refine ⟨200762426289208291738031929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267683235052277722317375905 200762426289208291738031929)
    ·
      refine ⟨150571819716906218803523947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200762426289208291738031929 150571819716906218803523947)
      ·
        refine ⟨225857729575359328205285921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150571819716906218803523947 225857729575359328205285921)
        ·
          refine ⟨169393297181519496153964441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225857729575359328205285921 169393297181519496153964441)
          ·
            refine ⟨127044972886139622115473331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169393297181519496153964441 127044972886139622115473331)
            ·
              refine ⟨190567459329209433173209997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127044972886139622115473331 190567459329209433173209997)
              ·
                refine ⟨71462797248453537439953749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190567459329209433173209997 71462797248453537439953749)
                ·
                  refine ⟨418727327627657445937229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71462797248453537439953749 418727327627657445937229)
                  ·
                    rfl

theorem cell23_7339217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 9].length) (baseStart_7339217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339217 prefixEnd_7339217 := by exact prefixLift 7339217
  have htrace : WordTrace (prefixWord ++ tailWord_7339217) baseStart_7339217 baseEnd_7339217 := by
    simpa [prefixWord, tailWord_7339217, baseEnd_7339217] using wordTrace_append hprefix tailTrace_7339217
  have hstable : (prefixWord ++ tailWord_7339217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339217).length < 2 ^ (prefixWord ++ tailWord_7339217).sum := by decide
  have hdescent : baseEnd_7339217 < baseStart_7339217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339245 : List Nat := [1, 5, 1, 2, 2, 1, 1, 4, 2, 2, 2]
def baseStart_7339245 : Nat := 118140960795 + 7339245 * 2 ^ 59
def prefixEnd_7339245 : Nat := 4983230072969 + 3 ^ 40 * 7339245 * 2
def baseEnd_7339245 : Nat := 3768560326107242903884933

theorem tailTrace_7339245 : CollatzResearch.WordTrace tailWord_7339245 prefixEnd_7339245 3768560326107242903884933 := by
  unfold tailWord_7339245
  simp only [CollatzResearch.WordTrace]
  refine ⟨267684256296176283099395189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178456170864117522066263459 267684256296176283099395189)
  ·
    refine ⟨25095399027766526540568299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267684256296176283099395189 25095399027766526540568299)
    ·
      refine ⟨37643098541649789810852449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25095399027766526540568299 37643098541649789810852449)
      ·
        refine ⟨28232323906237342358139337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37643098541649789810852449 28232323906237342358139337)
        ·
          refine ⟨21174242929678006768604503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28232323906237342358139337 21174242929678006768604503)
          ·
            refine ⟨31761364394517010152906755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21174242929678006768604503 31761364394517010152906755)
            ·
              refine ⟨47642046591775515229360133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31761364394517010152906755 47642046591775515229360133)
              ·
                refine ⟨8932883735957909105505025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47642046591775515229360133 8932883735957909105505025)
                ·
                  refine ⟨6699662801968431829128769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8932883735957909105505025 6699662801968431829128769)
                  ·
                    refine ⟨5024747101476323871846577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6699662801968431829128769 5024747101476323871846577)
                    ·
                      refine ⟨3768560326107242903884933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024747101476323871846577 3768560326107242903884933)
                      ·
                        rfl

theorem cell23_7339245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 4, 2, 2, 2].length) (baseStart_7339245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339245 prefixEnd_7339245 := by exact prefixLift 7339245
  have htrace : WordTrace (prefixWord ++ tailWord_7339245) baseStart_7339245 baseEnd_7339245 := by
    simpa [prefixWord, tailWord_7339245, baseEnd_7339245] using wordTrace_append hprefix tailTrace_7339245
  have hstable : (prefixWord ++ tailWord_7339245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339245).length < 2 ^ (prefixWord ++ tailWord_7339245).sum := by decide
  have hdescent : baseEnd_7339245 < baseStart_7339245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339251 : List Nat := [1, 1, 1, 2, 2, 6, 1, 4, 5]
def baseStart_7339251 : Nat := 118140960795 + 7339251 * 2 ^ 59
def prefixEnd_7339251 : Nat := 4983230072969 + 3 ^ 40 * 7339251 * 2
def baseEnd_7339251 : Nat := 418729267443463320045545

theorem tailTrace_7339251 : CollatzResearch.WordTrace tailWord_7339251 prefixEnd_7339251 418729267443463320045545 := by
  unfold tailWord_7339251
  simp only [CollatzResearch.WordTrace]
  refine ⟨267684475134154546124113607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178456316756103030749409071 267684475134154546124113607)
  ·
    refine ⟨401526712701231819186170411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267684475134154546124113607 401526712701231819186170411)
    ·
      refine ⟨602290069051847728779255617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401526712701231819186170411 602290069051847728779255617)
      ·
        refine ⟨451717551788885796584441713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602290069051847728779255617 451717551788885796584441713)
        ·
          refine ⟨338788163841664347438331285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451717551788885796584441713 338788163841664347438331285)
          ·
            refine ⟨15880695180078016286171779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 338788163841664347438331285 15880695180078016286171779)
            ·
              refine ⟨23821042770117024429257669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15880695180078016286171779 23821042770117024429257669)
              ·
                refine ⟨4466445519396942080485813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23821042770117024429257669 4466445519396942080485813)
                ·
                  refine ⟨418729267443463320045545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4466445519396942080485813 418729267443463320045545)
                  ·
                    rfl

theorem cell23_7339251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 5].length) (baseStart_7339251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339251 prefixEnd_7339251 := by exact prefixLift 7339251
  have htrace : WordTrace (prefixWord ++ tailWord_7339251) baseStart_7339251 baseEnd_7339251 := by
    simpa [prefixWord, tailWord_7339251, baseEnd_7339251] using wordTrace_append hprefix tailTrace_7339251
  have hstable : (prefixWord ++ tailWord_7339251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339251).length < 2 ^ (prefixWord ++ tailWord_7339251).sum := by decide
  have hdescent : baseEnd_7339251 < baseStart_7339251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339254 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8]
def baseStart_7339254 : Nat := 118140960795 + 7339254 * 2 ^ 59
def prefixEnd_7339254 : Nat := 4983230072969 + 3 ^ 40 * 7339254 * 2
def baseEnd_7339254 : Nat := 3768564947433133368672391

theorem tailTrace_7339254 : CollatzResearch.WordTrace tailWord_7339254 prefixEnd_7339254 3768564947433133368672391 := by
  unfold tailWord_7339254
  simp only [CollatzResearch.WordTrace]
  refine ⟨16730286534571479852279551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178456389702095785090981877 16730286534571479852279551)
  ·
    refine ⟨25095429801857219778419327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16730286534571479852279551 25095429801857219778419327)
    ·
      refine ⟨37643144702785829667628991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25095429801857219778419327 37643144702785829667628991)
      ·
        refine ⟨56464717054178744501443487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37643144702785829667628991 56464717054178744501443487)
        ·
          refine ⟨84697075581268116752165231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56464717054178744501443487 84697075581268116752165231)
          ·
            refine ⟨127045613371902175128247847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84697075581268116752165231 127045613371902175128247847)
            ·
              refine ⟨190568420057853262692371771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127045613371902175128247847 190568420057853262692371771)
              ·
                refine ⟨285852630086779894038557657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190568420057853262692371771 285852630086779894038557657)
                ·
                  refine ⟨214389472565084920528918243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285852630086779894038557657 214389472565084920528918243)
                  ·
                    refine ⟨321584208847627380793377365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 214389472565084920528918243 321584208847627380793377365)
                    ·
                      refine ⟨3768564947433133368672391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 321584208847627380793377365 3768564947433133368672391)
                      ·
                        rfl

theorem cell23_7339254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_7339254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339254 prefixEnd_7339254 := by exact prefixLift 7339254
  have htrace : WordTrace (prefixWord ++ tailWord_7339254) baseStart_7339254 baseEnd_7339254 := by
    simpa [prefixWord, tailWord_7339254, baseEnd_7339254] using wordTrace_append hprefix tailTrace_7339254
  have hstable : (prefixWord ++ tailWord_7339254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339254).length < 2 ^ (prefixWord ++ tailWord_7339254).sum := by decide
  have hdescent : baseEnd_7339254 < baseStart_7339254 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339362 : List Nat := [3, 3, 2, 1, 1, 1, 5, 2, 1, 4]
def baseStart_7339362 : Nat := 118140960795 + 7339362 * 2 ^ 59
def prefixEnd_7339362 : Nat := 4983230072969 + 3 ^ 40 * 7339362 * 2
def baseEnd_7339362 : Nat := 1256206801114606315373965

theorem tailTrace_7339362 : CollatzResearch.WordTrace tailWord_7339362 prefixEnd_7339362 1256206801114606315373965 := by
  unfold tailWord_7339362
  simp only [CollatzResearch.WordTrace]
  refine ⟨66922130909188103020351085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178459015757834941387602893 66922130909188103020351085)
  ·
    refine ⟨25095799090945538632631657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66922130909188103020351085 25095799090945538632631657)
    ·
      refine ⟨18821849318209153974473743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25095799090945538632631657 18821849318209153974473743)
      ·
        refine ⟨28232773977313730961710615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18821849318209153974473743 28232773977313730961710615)
        ·
          refine ⟨42349160965970596442565923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28232773977313730961710615 42349160965970596442565923)
          ·
            refine ⟨63523741448955894663848885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42349160965970596442565923 63523741448955894663848885)
            ·
              refine ⟨5955350760839615124735833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63523741448955894663848885 5955350760839615124735833)
              ·
                refine ⟨4466513070629711343551875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5955350760839615124735833 4466513070629711343551875)
                ·
                  refine ⟨6699769605944567015327813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466513070629711343551875 6699769605944567015327813)
                  ·
                    refine ⟨1256206801114606315373965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6699769605944567015327813 1256206801114606315373965)
                    ·
                      rfl

theorem cell23_7339362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_7339362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339362 prefixEnd_7339362 := by exact prefixLift 7339362
  have htrace : WordTrace (prefixWord ++ tailWord_7339362) baseStart_7339362 baseEnd_7339362 := by
    simpa [prefixWord, tailWord_7339362, baseEnd_7339362] using wordTrace_append hprefix tailTrace_7339362
  have hstable : (prefixWord ++ tailWord_7339362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339362).length < 2 ^ (prefixWord ++ tailWord_7339362).sum := by decide
  have hdescent : baseEnd_7339362 < baseStart_7339362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339378 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 4, 3, 2]
def baseStart_7339378 : Nat := 118140960795 + 7339378 * 2 ^ 59
def prefixEnd_7339378 : Nat := 4983230072969 + 3 ^ 40 * 7339378 * 2
def baseEnd_7339378 : Nat := 3768628619034290883521821

theorem tailTrace_7339378 : CollatzResearch.WordTrace tailWord_7339378 prefixEnd_7339378 3768628619034290883521821 := by
  unfold tailWord_7339378
  simp only [CollatzResearch.WordTrace]
  refine ⟨66922276801173611703496697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178459404803129631209324525 66922276801173611703496697)
  ·
    refine ⟨50191707600880208777622523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66922276801173611703496697 50191707600880208777622523)
    ·
      refine ⟨75287561401320313166433785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50191707600880208777622523 75287561401320313166433785)
      ·
        refine ⟨56465671050990234874825339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75287561401320313166433785 56465671050990234874825339)
        ·
          refine ⟨84698506576485352312238009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56465671050990234874825339 84698506576485352312238009)
          ·
            refine ⟨63523879932364014234178507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84698506576485352312238009 63523879932364014234178507)
            ·
              refine ⟨95285819898546021351267761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63523879932364014234178507 95285819898546021351267761)
              ·
                refine ⟨71464364923909516013450821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95285819898546021351267761 71464364923909516013450821)
                ·
                  refine ⟨13399568423233034252522029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71464364923909516013450821 13399568423233034252522029)
                  ·
                    refine ⟨5024838158712387844695761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13399568423233034252522029 5024838158712387844695761)
                    ·
                      refine ⟨3768628619034290883521821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024838158712387844695761 3768628619034290883521821)
                      ·
                        rfl

theorem cell23_7339378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 4, 3, 2].length) (baseStart_7339378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339378 prefixEnd_7339378 := by exact prefixLift 7339378
  have htrace : WordTrace (prefixWord ++ tailWord_7339378) baseStart_7339378 baseEnd_7339378 := by
    simpa [prefixWord, tailWord_7339378, baseEnd_7339378] using wordTrace_append hprefix tailTrace_7339378
  have hstable : (prefixWord ++ tailWord_7339378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339378).length < 2 ^ (prefixWord ++ tailWord_7339378).sum := by decide
  have hdescent : baseEnd_7339378 < baseStart_7339378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339384 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 7, 6]
def baseStart_7339384 : Nat := 118140960795 + 7339384 * 2 ^ 59
def prefixEnd_7339384 : Nat := 4983230072969 + 3 ^ 40 * 7339384 * 2
def baseEnd_7339384 : Nat := 1256210566639405953348931

theorem tailTrace_7339384 : CollatzResearch.WordTrace tailWord_7339384 prefixEnd_7339384 1256210566639405953348931 := by
  unfold tailWord_7339384
  simp only [CollatzResearch.WordTrace]
  refine ⟨133844663021336354919352603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178459550695115139892470137 133844663021336354919352603)
  ·
    refine ⟨200766994532004532379028905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133844663021336354919352603 200766994532004532379028905)
    ·
      refine ⟨150575245899003399284271679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200766994532004532379028905 150575245899003399284271679)
      ·
        refine ⟨225862868848505098926407519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150575245899003399284271679 225862868848505098926407519)
        ·
          refine ⟨338794303272757648389611279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225862868848505098926407519 338794303272757648389611279)
          ·
            refine ⟨508191454909136472584416919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338794303272757648389611279 508191454909136472584416919)
            ·
              refine ⟨762287182363704708876625379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508191454909136472584416919 762287182363704708876625379)
              ·
                refine ⟨1143430773545557063314938069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 762287182363704708876625379 1143430773545557063314938069)
                ·
                  refine ⟨26799158754973993671443861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1143430773545557063314938069 26799158754973993671443861)
                  ·
                    refine ⟨1256210566639405953348931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26799158754973993671443861 1256210566639405953348931)
                    ·
                      rfl

theorem cell23_7339384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7, 6].length) (baseStart_7339384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339384 prefixEnd_7339384 := by exact prefixLift 7339384
  have htrace : WordTrace (prefixWord ++ tailWord_7339384) baseStart_7339384 baseEnd_7339384 := by
    simpa [prefixWord, tailWord_7339384, baseEnd_7339384] using wordTrace_append hprefix tailTrace_7339384
  have hstable : (prefixWord ++ tailWord_7339384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339384).length < 2 ^ (prefixWord ++ tailWord_7339384).sum := by decide
  have hdescent : baseEnd_7339384 < baseStart_7339384 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339395 : List Nat := [1, 1, 1, 3, 5, 2, 2, 1, 2, 3, 2]
def baseStart_7339395 : Nat := 118140960795 + 7339395 * 2 ^ 59
def prefixEnd_7339395 : Nat := 4983230072969 + 3 ^ 40 * 7339395 * 2
def baseEnd_7339395 : Nat := 3768637348205417317009243

theorem tailTrace_7339395 : CollatzResearch.WordTrace tailWord_7339395 prefixEnd_7339395 3768637348205417317009243 := by
  unfold tailWord_7339395
  simp only [CollatzResearch.WordTrace]
  refine ⟨267689727245632858717355639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178459818163755239144903759 267689727245632858717355639)
  ·
    refine ⟨401534590868449288076033459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267689727245632858717355639 401534590868449288076033459)
    ·
      refine ⟨602301886302673932114050189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401534590868449288076033459 602301886302673932114050189)
      ·
        refine ⟨225863207363502724542768821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 602301886302673932114050189 225863207363502724542768821)
        ·
          refine ⟨21174675690328380425884577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225863207363502724542768821 21174675690328380425884577)
          ·
            refine ⟨15881006767746285319413433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21174675690328380425884577 15881006767746285319413433)
            ·
              refine ⟨11910755075809713989560075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15881006767746285319413433 11910755075809713989560075)
              ·
                refine ⟨17866132613714570984340113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11910755075809713989560075 17866132613714570984340113)
                ·
                  refine ⟨13399599460285928238255085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17866132613714570984340113 13399599460285928238255085)
                  ·
                    refine ⟨5024849797607223089345657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13399599460285928238255085 5024849797607223089345657)
                    ·
                      refine ⟨3768637348205417317009243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024849797607223089345657 3768637348205417317009243)
                      ·
                        rfl

theorem cell23_7339395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 2, 1, 2, 3, 2].length) (baseStart_7339395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339395 prefixEnd_7339395 := by exact prefixLift 7339395
  have htrace : WordTrace (prefixWord ++ tailWord_7339395) baseStart_7339395 baseEnd_7339395 := by
    simpa [prefixWord, tailWord_7339395, baseEnd_7339395] using wordTrace_append hprefix tailTrace_7339395
  have hstable : (prefixWord ++ tailWord_7339395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339395).length < 2 ^ (prefixWord ++ tailWord_7339395).sum := by decide
  have hdescent : baseEnd_7339395 < baseStart_7339395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339502 : List Nat := [4, 1, 2, 1, 2, 1, 4, 2, 1, 3, 2]
def baseStart_7339502 : Nat := 118140960795 + 7339502 * 2 ^ 59
def prefixEnd_7339502 : Nat := 4983230072969 + 3 ^ 40 * 7339502 * 2
def baseEnd_7339502 : Nat := 3768692290635448398371251

theorem tailTrace_7339502 : CollatzResearch.WordTrace tailWord_7339502 prefixEnd_7339502 3768692290635448398371251 := by
  unfold tailWord_7339502
  simp only [CollatzResearch.WordTrace]
  refine ⟨33461703732030651998937595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178462419904163477327667173 33461703732030651998937595)
  ·
    refine ⟨50192555598045977998406393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33461703732030651998937595 50192555598045977998406393)
    ·
      refine ⟨37644416698534483498804795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50192555598045977998406393 37644416698534483498804795)
      ·
        refine ⟨56466625047801725248207193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37644416698534483498804795 56466625047801725248207193)
        ·
          refine ⟨42349968785851293936155395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56466625047801725248207193 42349968785851293936155395)
          ·
            refine ⟨63524953178776940904233093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42349968785851293936155395 63524953178776940904233093)
            ·
              refine ⟨11910928721020676419543705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63524953178776940904233093 11910928721020676419543705)
              ·
                refine ⟨8933196540765507314657779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11910928721020676419543705 8933196540765507314657779)
                ·
                  refine ⟨13399794811148260971986669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8933196540765507314657779 13399794811148260971986669)
                  ·
                    refine ⟨5024923054180597864495001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13399794811148260971986669 5024923054180597864495001)
                    ·
                      refine ⟨3768692290635448398371251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5024923054180597864495001 3768692290635448398371251)
                      ·
                        rfl

theorem cell23_7339502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_7339502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339502 prefixEnd_7339502 := by exact prefixLift 7339502
  have htrace : WordTrace (prefixWord ++ tailWord_7339502) baseStart_7339502 baseEnd_7339502 := by
    simpa [prefixWord, tailWord_7339502, baseEnd_7339502] using wordTrace_append hprefix tailTrace_7339502
  have hstable : (prefixWord ++ tailWord_7339502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339502).length < 2 ^ (prefixWord ++ tailWord_7339502).sum := by decide
  have hdescent : baseEnd_7339502 < baseStart_7339502 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339511 : List Nat := [1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 4]
def baseStart_7339511 : Nat := 118140960795 + 7339511 * 2 ^ 59
def prefixEnd_7339511 : Nat := 4983230072969 + 3 ^ 40 * 7339511 * 2
def baseEnd_7339511 : Nat := 3768696911961338863158709

theorem tailTrace_7339511 : CollatzResearch.WordTrace tailWord_7339511 prefixEnd_7339511 3768696911961338863158709 := by
  unfold tailWord_7339511
  simp only [CollatzResearch.WordTrace]
  refine ⟨267693958113212610528578387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178462638742141740352385591 267693958113212610528578387)
  ·
    refine ⟨401540937169818915792867581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267693958113212610528578387 401540937169818915792867581)
    ·
      refine ⟨150577851438682093422325343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401540937169818915792867581 150577851438682093422325343)
      ·
        refine ⟨225866777158023140133488015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150577851438682093422325343 225866777158023140133488015)
        ·
          refine ⟨338800165737034710200232023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225866777158023140133488015 338800165737034710200232023)
          ·
            refine ⟨508200248605552065300348035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338800165737034710200232023 508200248605552065300348035)
            ·
              refine ⟨762300372908328097950522053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508200248605552065300348035 762300372908328097950522053)
              ·
                refine ⟨142931319920311518365722885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 762300372908328097950522053 142931319920311518365722885)
                ·
                  refine ⟨26799622485058409693573041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142931319920311518365722885 26799622485058409693573041)
                  ·
                    refine ⟨20099716863793807270179781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26799622485058409693573041 20099716863793807270179781)
                    ·
                      refine ⟨3768696911961338863158709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20099716863793807270179781 3768696911961338863158709)
                      ·
                        rfl

theorem cell23_7339511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_7339511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339511 prefixEnd_7339511 := by exact prefixLift 7339511
  have htrace : WordTrace (prefixWord ++ tailWord_7339511) baseStart_7339511 baseEnd_7339511 := by
    simpa [prefixWord, tailWord_7339511, baseEnd_7339511] using wordTrace_append hprefix tailTrace_7339511
  have hstable : (prefixWord ++ tailWord_7339511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339511).length < 2 ^ (prefixWord ++ tailWord_7339511).sum := by decide
  have hdescent : baseEnd_7339511 < baseStart_7339511 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339548 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_7339548 : Nat := 118140960795 + 7339548 * 2 ^ 59
def prefixEnd_7339548 : Nat := 4983230072969 + 3 ^ 40 * 7339548 * 2
def baseEnd_7339548 : Nat := 3768715910745555218396039

theorem tailTrace_7339548 : CollatzResearch.WordTrace tailWord_7339548 prefixEnd_7339548 3768715910745555218396039 := by
  unfold tailWord_7339548
  simp only [CollatzResearch.WordTrace]
  refine ⟨133847653807039282923837649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178463538409385710565116865 133847653807039282923837649)
  ·
    refine ⟨100385740355279462192878237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133847653807039282923837649 100385740355279462192878237)
    ·
      refine ⟨37644652633229798322329339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100385740355279462192878237 37644652633229798322329339)
      ·
        refine ⟨56466978949844697483494009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37644652633229798322329339 56466978949844697483494009)
        ·
          refine ⟨42350234212383523112620507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56466978949844697483494009 42350234212383523112620507)
          ·
            refine ⟨63525351318575284668930761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42350234212383523112620507 63525351318575284668930761)
            ·
              refine ⟨47644013488931463501698071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63525351318575284668930761 47644013488931463501698071)
              ·
                refine ⟨71466020233397195252547107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47644013488931463501698071 71466020233397195252547107)
                ·
                  refine ⟨107199030350095792878820661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71466020233397195252547107 107199030350095792878820661)
                  ·
                    refine ⟨10049909095321480582389437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 107199030350095792878820661 10049909095321480582389437)
                    ·
                      refine ⟨3768715910745555218396039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10049909095321480582389437 3768715910745555218396039)
                      ·
                        rfl

theorem cell23_7339548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_7339548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339548 prefixEnd_7339548 := by exact prefixLift 7339548
  have htrace : WordTrace (prefixWord ++ tailWord_7339548) baseStart_7339548 baseEnd_7339548 := by
    simpa [prefixWord, tailWord_7339548, baseEnd_7339548] using wordTrace_append hprefix tailTrace_7339548
  have hstable : (prefixWord ++ tailWord_7339548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339548).length < 2 ^ (prefixWord ++ tailWord_7339548).sum := by decide
  have hdescent : baseEnd_7339548 < baseStart_7339548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339551 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 3, 7]
def baseStart_7339551 : Nat := 118140960795 + 7339551 * 2 ^ 59
def prefixEnd_7339551 : Nat := 4983230072969 + 3 ^ 40 * 7339551 * 2
def baseEnd_7339551 : Nat := 1256239150395839568886175

theorem tailTrace_7339551 : CollatzResearch.WordTrace tailWord_7339551 prefixEnd_7339551 1256239150395839568886175 := by
  unfold tailWord_7339551
  simp only [CollatzResearch.WordTrace]
  refine ⟨267695417033067697360034507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178463611355378464906689671 267695417033067697360034507)
  ·
    refine ⟨401543125549601546040051761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267695417033067697360034507 401543125549601546040051761)
    ·
      refine ⟨301157344162201159530038821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401543125549601546040051761 301157344162201159530038821)
      ·
        refine ⟨56467002030412717411882279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301157344162201159530038821 56467002030412717411882279)
        ·
          refine ⟨84700503045619076117823419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56467002030412717411882279 84700503045619076117823419)
          ·
            refine ⟨127050754568428614176735129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84700503045619076117823419 127050754568428614176735129)
            ·
              refine ⟨95288065926321460632551347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127050754568428614176735129 95288065926321460632551347)
              ·
                refine ⟨142932098889482190948827021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95288065926321460632551347 142932098889482190948827021)
                ·
                  refine ⟨53599537083555821605810133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142932098889482190948827021 53599537083555821605810133)
                  ·
                    refine ⟨1256239150395839568886175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53599537083555821605810133 1256239150395839568886175)
                    ·
                      rfl

theorem cell23_7339551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 7].length) (baseStart_7339551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339551 prefixEnd_7339551 := by exact prefixLift 7339551
  have htrace : WordTrace (prefixWord ++ tailWord_7339551) baseStart_7339551 baseEnd_7339551 := by
    simpa [prefixWord, tailWord_7339551, baseEnd_7339551] using wordTrace_append hprefix tailTrace_7339551
  have hstable : (prefixWord ++ tailWord_7339551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339551).length < 2 ^ (prefixWord ++ tailWord_7339551).sum := by decide
  have hdescent : baseEnd_7339551 < baseStart_7339551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339608 : List Nat := [2, 1, 2, 2, 1, 2, 1, 4, 1, 4, 3]
def baseStart_7339608 : Nat := 118140960795 + 7339608 * 2 ^ 59
def prefixEnd_7339608 : Nat := 4983230072969 + 3 ^ 40 * 7339608 * 2
def baseEnd_7339608 : Nat := 3768746719584824983645763

theorem tailTrace_7339608 : CollatzResearch.WordTrace tailWord_7339608 prefixEnd_7339608 3768746719584824983645763 := by
  unfold tailWord_7339608
  simp only [CollatzResearch.WordTrace]
  refine ⟨133848747996930598047429739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178464997329240797396572985 133848747996930598047429739)
  ·
    refine ⟨200773121995395897071144609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133848747996930598047429739 200773121995395897071144609)
    ·
      refine ⟨150579841496546922803358457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200773121995395897071144609 150579841496546922803358457)
      ·
        refine ⟨112934881122410192102518843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150579841496546922803358457 112934881122410192102518843)
        ·
          refine ⟨169402321683615288153778265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112934881122410192102518843 169402321683615288153778265)
          ·
            refine ⟨127051741262711466115333699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169402321683615288153778265 127051741262711466115333699)
            ·
              refine ⟨190577611894067199173000549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 127051741262711466115333699 190577611894067199173000549)
              ·
                refine ⟨35733302230137599844937603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190577611894067199173000549 35733302230137599844937603)
                ·
                  refine ⟨53599953345206399767406405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35733302230137599844937603 53599953345206399767406405)
                  ·
                    refine ⟨10049991252226199956388701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53599953345206399767406405 10049991252226199956388701)
                    ·
                      refine ⟨3768746719584824983645763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10049991252226199956388701 3768746719584824983645763)
                      ·
                        rfl

theorem cell23_7339608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 4, 1, 4, 3].length) (baseStart_7339608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339608 prefixEnd_7339608 := by exact prefixLift 7339608
  have htrace : WordTrace (prefixWord ++ tailWord_7339608) baseStart_7339608 baseEnd_7339608 := by
    simpa [prefixWord, tailWord_7339608, baseEnd_7339608] using wordTrace_append hprefix tailTrace_7339608
  have hstable : (prefixWord ++ tailWord_7339608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339608).length < 2 ^ (prefixWord ++ tailWord_7339608).sum := by decide
  have hdescent : baseEnd_7339608 < baseStart_7339608 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339625 : List Nat := [1, 2, 1, 1, 1, 4, 5, 1, 2, 2, 3]
def baseStart_7339625 : Nat := 118140960795 + 7339625 * 2 ^ 59
def prefixEnd_7339625 : Nat := 4983230072969 + 3 ^ 40 * 7339625 * 2
def baseEnd_7339625 : Nat := 3768755448755951417133185

theorem tailTrace_7339625 : CollatzResearch.WordTrace tailWord_7339625 prefixEnd_7339625 3768755448755951417133185 := by
  unfold tailWord_7339625
  simp only [CollatzResearch.WordTrace]
  refine ⟨267698116034799607998228329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178465410689866405332152219 267698116034799607998228329)
  ·
    refine ⟨200773587026099705998671247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267698116034799607998228329 200773587026099705998671247)
    ·
      refine ⟨301160380539149558998006871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200773587026099705998671247 301160380539149558998006871)
      ·
        refine ⟨451740570808724338497010307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301160380539149558998006871 451740570808724338497010307)
        ·
          refine ⟨677610856213086507745515461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451740570808724338497010307 677610856213086507745515461)
          ·
            refine ⟨127052035539953720202284149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 677610856213086507745515461 127052035539953720202284149)
            ·
              refine ⟨11911128331870661268964139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 127052035539953720202284149 11911128331870661268964139)
              ·
                refine ⟨17866692497805991903446209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11911128331870661268964139 17866692497805991903446209)
                ·
                  refine ⟨13400019373354493927584657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17866692497805991903446209 13400019373354493927584657)
                  ·
                    refine ⟨10050014530015870445688493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13400019373354493927584657 10050014530015870445688493)
                    ·
                      refine ⟨3768755448755951417133185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10050014530015870445688493 3768755448755951417133185)
                      ·
                        rfl

theorem cell23_7339625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 1, 2, 2, 3].length) (baseStart_7339625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339625 prefixEnd_7339625 := by exact prefixLift 7339625
  have htrace : WordTrace (prefixWord ++ tailWord_7339625) baseStart_7339625 baseEnd_7339625 := by
    simpa [prefixWord, tailWord_7339625, baseEnd_7339625] using wordTrace_append hprefix tailTrace_7339625
  have hstable : (prefixWord ++ tailWord_7339625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339625).length < 2 ^ (prefixWord ++ tailWord_7339625).sum := by decide
  have hdescent : baseEnd_7339625 < baseStart_7339625 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339632 : List Nat := [2, 1, 1, 1, 6, 1, 1, 5, 1, 4]
def baseStart_7339632 : Nat := 118140960795 + 7339632 * 2 ^ 59
def prefixEnd_7339632 : Nat := 4983230072969 + 3 ^ 40 * 7339632 * 2
def baseEnd_7339632 : Nat := 1256253014373510963248551

theorem tailTrace_7339632 : CollatzResearch.WordTrace tailWord_7339632 prefixEnd_7339632 1256253014373510963248551 := by
  unfold tailWord_7339632
  simp only [CollatzResearch.WordTrace]
  refine ⟨133849185672887124096866575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178465580897182832129155433 133849185672887124096866575)
  ·
    refine ⟨200773778509330686145299863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133849185672887124096866575 200773778509330686145299863)
    ·
      refine ⟨301160667763996029217949795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200773778509330686145299863 301160667763996029217949795)
      ·
        refine ⟨451741001645994043826924693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301160667763996029217949795 451741001645994043826924693)
        ·
          refine ⟨21175359452155970804387095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 451741001645994043826924693 21175359452155970804387095)
          ·
            refine ⟨31763039178233956206580643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21175359452155970804387095 31763039178233956206580643)
            ·
              refine ⟨47644558767350934309870965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31763039178233956206580643 47644558767350934309870965)
              ·
                refine ⟨4466677384439150091550403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47644558767350934309870965 4466677384439150091550403)
                ·
                  refine ⟨6700016076658725137325605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466677384439150091550403 6700016076658725137325605)
                  ·
                    refine ⟨1256253014373510963248551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6700016076658725137325605 1256253014373510963248551)
                    ·
                      rfl

theorem cell23_7339632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 1, 4].length) (baseStart_7339632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339632 prefixEnd_7339632 := by exact prefixLift 7339632
  have htrace : WordTrace (prefixWord ++ tailWord_7339632) baseStart_7339632 baseEnd_7339632 := by
    simpa [prefixWord, tailWord_7339632, baseEnd_7339632] using wordTrace_append hprefix tailTrace_7339632
  have hstable : (prefixWord ++ tailWord_7339632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339632).length < 2 ^ (prefixWord ++ tailWord_7339632).sum := by decide
  have hdescent : baseEnd_7339632 < baseStart_7339632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339645 : List Nat := [1, 4, 1, 1, 4, 1, 3, 2, 6]
def baseStart_7339645 : Nat := 118140960795 + 7339645 * 2 ^ 59
def prefixEnd_7339645 : Nat := 4983230072969 + 3 ^ 40 * 7339645 * 2
def baseEnd_7339645 : Nat := 418751746485449037653677

theorem tailTrace_7339645 : CollatzResearch.WordTrace tailWord_7339645 prefixEnd_7339645 418751746485449037653677 := by
  unfold tailWord_7339645
  simp only [CollatzResearch.WordTrace]
  refine ⟨267698845494727151413956389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178465896996484767609304259 267698845494727151413956389)
  ·
    refine ⟨50193533530261340890116823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267698845494727151413956389 50193533530261340890116823)
    ·
      refine ⟨75290300295392011335175235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50193533530261340890116823 75290300295392011335175235)
      ·
        refine ⟨112935450443088017002762853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75290300295392011335175235 112935450443088017002762853)
        ·
          refine ⟨21175396958079003188018035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112935450443088017002762853 21175396958079003188018035)
          ·
            refine ⟨31763095437118504782027053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21175396958079003188018035 31763095437118504782027053)
            ·
              refine ⟨11911160788919439293260145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31763095437118504782027053 11911160788919439293260145)
              ·
                refine ⟨8933370591689579469945109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11911160788919439293260145 8933370591689579469945109)
                ·
                  refine ⟨418751746485449037653677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8933370591689579469945109 418751746485449037653677)
                  ·
                    rfl

theorem cell23_7339645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_7339645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339645 prefixEnd_7339645 := by exact prefixLift 7339645
  have htrace : WordTrace (prefixWord ++ tailWord_7339645) baseStart_7339645 baseEnd_7339645 := by
    simpa [prefixWord, tailWord_7339645, baseEnd_7339645] using wordTrace_append hprefix tailTrace_7339645
  have hstable : (prefixWord ++ tailWord_7339645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339645).length < 2 ^ (prefixWord ++ tailWord_7339645).sum := by decide
  have hdescent : baseEnd_7339645 < baseStart_7339645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339662 : List Nat := [4, 1, 1, 3, 1, 3, 3, 1, 6]
def baseStart_7339662 : Nat := 118140960795 + 7339662 * 2 ^ 59
def prefixEnd_7339662 : Nat := 4983230072969 + 3 ^ 40 * 7339662 * 2
def baseEnd_7339662 : Nat := 418752716393351974707835

theorem tailTrace_7339662 : CollatzResearch.WordTrace tailWord_7339662 prefixEnd_7339662 418752716393351974707835 := by
  unfold tailWord_7339662
  simp only [CollatzResearch.WordTrace]
  refine ⟨33462433191958195414665655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178466310357110375544883493 33462433191958195414665655)
  ·
    refine ⟨50193649787937293121998483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33462433191958195414665655 50193649787937293121998483)
    ·
      refine ⟨75290474681905939682997725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50193649787937293121998483 75290474681905939682997725)
      ·
        refine ⟨28233928005714727381124147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75290474681905939682997725 28233928005714727381124147)
        ·
          refine ⟨42350892008572091071686221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28233928005714727381124147 42350892008572091071686221)
          ·
            refine ⟨15881584503214534151882333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42350892008572091071686221 15881584503214534151882333)
            ·
              refine ⟨5955594188705450306955875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15881584503214534151882333 5955594188705450306955875)
              ·
                refine ⟨8933391283058175460433813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5955594188705450306955875 8933391283058175460433813)
                ·
                  refine ⟨418752716393351974707835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8933391283058175460433813 418752716393351974707835)
                  ·
                    rfl

theorem cell23_7339662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_7339662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339662 prefixEnd_7339662 := by exact prefixLift 7339662
  have htrace : WordTrace (prefixWord ++ tailWord_7339662) baseStart_7339662 baseEnd_7339662 := by
    simpa [prefixWord, tailWord_7339662, baseEnd_7339662] using wordTrace_append hprefix tailTrace_7339662
  have hstable : (prefixWord ++ tailWord_7339662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339662).length < 2 ^ (prefixWord ++ tailWord_7339662).sum := by decide
  have hdescent : baseEnd_7339662 < baseStart_7339662 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339665 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 6, 3, 2]
def baseStart_7339665 : Nat := 118140960795 + 7339665 * 2 ^ 59
def prefixEnd_7339665 : Nat := 4983230072969 + 3 ^ 40 * 7339665 * 2
def baseEnd_7339665 : Nat := 3768775987982131260633001

theorem tailTrace_7339665 : CollatzResearch.WordTrace tailWord_7339665 prefixEnd_7339665 3768775987982131260633001 := by
  unfold tailWord_7339665
  simp only [CollatzResearch.WordTrace]
  refine ⟨267699574954654694829684449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178466383303103129886456299 267699574954654694829684449)
  ·
    refine ⟨200774681215991021122263337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267699574954654694829684449 200774681215991021122263337)
    ·
      refine ⟨150581010911993265841697503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200774681215991021122263337 150581010911993265841697503)
      ·
        refine ⟨225871516367989898762546255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150581010911993265841697503 225871516367989898762546255)
        ·
          refine ⟨338807274551984848143819383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225871516367989898762546255 338807274551984848143819383)
          ·
            refine ⟨508210911827977272215729075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338807274551984848143819383 508210911827977272215729075)
            ·
              refine ⟨762316367741965908323593613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 508210911827977272215729075 762316367741965908323593613)
              ·
                refine ⟨285868637903237215621347605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 762316367741965908323593613 285868637903237215621347605)
                ·
                  refine ⟨13400092401714244482250669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 285868637903237215621347605 13400092401714244482250669)
                  ·
                    refine ⟨5025034650642841680844001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13400092401714244482250669 5025034650642841680844001)
                    ·
                      refine ⟨3768775987982131260633001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5025034650642841680844001 3768775987982131260633001)
                      ·
                        rfl

theorem cell23_7339665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 3, 2].length) (baseStart_7339665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339665 prefixEnd_7339665 := by exact prefixLift 7339665
  have htrace : WordTrace (prefixWord ++ tailWord_7339665) baseStart_7339665 baseEnd_7339665 := by
    simpa [prefixWord, tailWord_7339665, baseEnd_7339665] using wordTrace_append hprefix tailTrace_7339665
  have hstable : (prefixWord ++ tailWord_7339665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339665).length < 2 ^ (prefixWord ++ tailWord_7339665).sum := by decide
  have hdescent : baseEnd_7339665 < baseStart_7339665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339672 : List Nat := [2, 1, 2, 4, 1, 2, 2, 2, 3, 1, 3]
def baseStart_7339672 : Nat := 118140960795 + 7339672 * 2 ^ 59
def prefixEnd_7339672 : Nat := 4983230072969 + 3 ^ 40 * 7339672 * 2
def baseEnd_7339672 : Nat := 3768779582346712733245469

theorem tailTrace_7339672 : CollatzResearch.WordTrace tailWord_7339672 prefixEnd_7339672 3768779582346712733245469 := by
  unfold tailWord_7339672
  simp only [CollatzResearch.WordTrace]
  refine ⟨133849915132814667512594635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178466553510419556683459513 133849915132814667512594635)
  ·
    refine ⟨200774872699222001268891953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133849915132814667512594635 200774872699222001268891953)
    ·
      refine ⟨150581154524416500951668965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200774872699222001268891953 150581154524416500951668965)
      ·
        refine ⟨28233966473328093928437931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150581154524416500951668965 28233966473328093928437931)
        ·
          refine ⟨42350949709992140892656897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28233966473328093928437931 42350949709992140892656897)
          ·
            refine ⟨31763212282494105669492673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42350949709992140892656897 31763212282494105669492673)
            ·
              refine ⟨23822409211870579252119505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31763212282494105669492673 23822409211870579252119505)
              ·
                refine ⟨17866806908902934439089629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23822409211870579252119505 17866806908902934439089629)
                ·
                  refine ⟨6700052590838600414658611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17866806908902934439089629 6700052590838600414658611)
                  ·
                    refine ⟨10050078886257900621987917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6700052590838600414658611 10050078886257900621987917)
                    ·
                      refine ⟨3768779582346712733245469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10050078886257900621987917 3768779582346712733245469)
                      ·
                        rfl

theorem cell23_7339672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_7339672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339672 prefixEnd_7339672 := by exact prefixLift 7339672
  have htrace : WordTrace (prefixWord ++ tailWord_7339672) baseStart_7339672 baseEnd_7339672 := by
    simpa [prefixWord, tailWord_7339672, baseEnd_7339672] using wordTrace_append hprefix tailTrace_7339672
  have hstable : (prefixWord ++ tailWord_7339672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339672).length < 2 ^ (prefixWord ++ tailWord_7339672).sum := by decide
  have hdescent : baseEnd_7339672 < baseStart_7339672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339695 : List Nat := [1, 1, 2, 1, 2, 4, 1, 5, 1, 1, 4]
def baseStart_7339695 : Nat := 118140960795 + 7339695 * 2 ^ 59
def prefixEnd_7339695 : Nat := 4983230072969 + 3 ^ 40 * 7339695 * 2
def baseEnd_7339695 : Nat := 3768791392401766143257863

theorem tailTrace_7339695 : CollatzResearch.WordTrace tailWord_7339695 prefixEnd_7339695 3768791392401766143257863 := by
  unfold tailWord_7339695
  simp only [CollatzResearch.WordTrace]
  refine ⟨267700669144546009953276539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178467112763030673302184359 267700669144546009953276539)
  ·
    refine ⟨401551003716819014929914809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267700669144546009953276539 401551003716819014929914809)
    ·
      refine ⟨301163252787614261197436107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401551003716819014929914809 301163252787614261197436107)
      ·
        refine ⟨451744879181421391796154161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301163252787614261197436107 451744879181421391796154161)
        ·
          refine ⟨338808659386066043847115621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451744879181421391796154161 338808659386066043847115621)
          ·
            refine ⟨63526623634887383221334179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338808659386066043847115621 63526623634887383221334179)
            ·
              refine ⟨95289935452331074832001269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63526623634887383221334179 95289935452331074832001269)
              ·
                refine ⟨8933431448656038265500119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95289935452331074832001269 8933431448656038265500119)
                ·
                  refine ⟨13400147172984057398250179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8933431448656038265500119 13400147172984057398250179)
                  ·
                    refine ⟨20100220759476086097375269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13400147172984057398250179 20100220759476086097375269)
                    ·
                      refine ⟨3768791392401766143257863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20100220759476086097375269 3768791392401766143257863)
                      ·
                        rfl

theorem cell23_7339695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 1, 4].length) (baseStart_7339695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339695 prefixEnd_7339695 := by exact prefixLift 7339695
  have htrace : WordTrace (prefixWord ++ tailWord_7339695) baseStart_7339695 baseEnd_7339695 := by
    simpa [prefixWord, tailWord_7339695, baseEnd_7339695] using wordTrace_append hprefix tailTrace_7339695
  have hstable : (prefixWord ++ tailWord_7339695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339695).length < 2 ^ (prefixWord ++ tailWord_7339695).sum := by decide
  have hdescent : baseEnd_7339695 < baseStart_7339695 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339705 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 4, 4]
def baseStart_7339705 : Nat := 118140960795 + 7339705 * 2 ^ 59
def prefixEnd_7339705 : Nat := 4983230072969 + 3 ^ 40 * 7339705 * 2
def baseEnd_7339705 : Nat := 1256265509069437034710939

theorem tailTrace_7339705 : CollatzResearch.WordTrace tailWord_7339705 prefixEnd_7339705 1256265509069437034710939 := by
  unfold tailWord_7339705
  simp only [CollatzResearch.WordTrace]
  refine ⟨267701033874509781661140569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178467355916339854440760379 267701033874509781661140569)
  ·
    refine ⟨200775775405882336245855427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267701033874509781661140569 200775775405882336245855427)
    ·
      refine ⟨301163663108823504368783141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200775775405882336245855427 301163663108823504368783141)
      ·
        refine ⟨56468186832904407069146839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 301163663108823504368783141 56468186832904407069146839)
        ·
          refine ⟨84702280249356610603720259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56468186832904407069146839 84702280249356610603720259)
          ·
            refine ⟨127053420374034915905580389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84702280249356610603720259 127053420374034915905580389)
            ·
              refine ⟨23822516320131546732296323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127053420374034915905580389 23822516320131546732296323)
              ·
                refine ⟨35733774480197320098444485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23822516320131546732296323 35733774480197320098444485)
                ·
                  refine ⟨6700082715036997518458341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35733774480197320098444485 6700082715036997518458341)
                  ·
                    refine ⟨1256265509069437034710939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6700082715036997518458341 1256265509069437034710939)
                    ·
                      rfl

theorem cell23_7339705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 4].length) (baseStart_7339705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339705 prefixEnd_7339705 := by exact prefixLift 7339705
  have htrace : WordTrace (prefixWord ++ tailWord_7339705) baseStart_7339705 baseEnd_7339705 := by
    simpa [prefixWord, tailWord_7339705, baseEnd_7339705] using wordTrace_append hprefix tailTrace_7339705
  have hstable : (prefixWord ++ tailWord_7339705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339705).length < 2 ^ (prefixWord ++ tailWord_7339705).sum := by decide
  have hdescent : baseEnd_7339705 < baseStart_7339705 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339706 : List Nat := [3, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3]
def baseStart_7339706 : Nat := 118140960795 + 7339706 * 2 ^ 59
def prefixEnd_7339706 : Nat := 4983230072969 + 3 ^ 40 * 7339706 * 2
def baseEnd_7339706 : Nat := 3768797040688965600220313

theorem tailTrace_7339706 : CollatzResearch.WordTrace tailWord_7339706 prefixEnd_7339706 3768797040688965600220313 := by
  unfold tailWord_7339706
  simp only [CollatzResearch.WordTrace]
  refine ⟨66925267586876539707981743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178467380231670772554617981 66925267586876539707981743)
  ·
    refine ⟨100387901380314809561972615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66925267586876539707981743 100387901380314809561972615)
    ·
      refine ⟨150581852070472214342958923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100387901380314809561972615 150581852070472214342958923)
      ·
        refine ⟨225872778105708321514438385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150581852070472214342958923 225872778105708321514438385)
        ·
          refine ⟨169404583579281241135828789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225872778105708321514438385 169404583579281241135828789)
          ·
            refine ⟨15881679710557616356483949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169404583579281241135828789 15881679710557616356483949)
            ·
              refine ⟨5955629891459106133681481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15881679710557616356483949 5955629891459106133681481)
              ·
                refine ⟨4466722418594329600261111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5955629891459106133681481 4466722418594329600261111)
                ·
                  refine ⟨6700083627891494400391667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4466722418594329600261111 6700083627891494400391667)
                  ·
                    refine ⟨10050125441837241600587501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6700083627891494400391667 10050125441837241600587501)
                    ·
                      refine ⟨3768797040688965600220313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10050125441837241600587501 3768797040688965600220313)
                      ·
                        rfl

theorem cell23_7339706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 3, 2, 1, 1, 3].length) (baseStart_7339706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339706 prefixEnd_7339706 := by exact prefixLift 7339706
  have htrace : WordTrace (prefixWord ++ tailWord_7339706) baseStart_7339706 baseEnd_7339706 := by
    simpa [prefixWord, tailWord_7339706, baseEnd_7339706] using wordTrace_append hprefix tailTrace_7339706
  have hstable : (prefixWord ++ tailWord_7339706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339706).length < 2 ^ (prefixWord ++ tailWord_7339706).sum := by decide
  have hdescent : baseEnd_7339706 < baseStart_7339706 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339749 : List Nat := [1, 3, 1, 4, 1, 1, 5, 1, 1, 2, 3]
def baseStart_7339749 : Nat := 118140960795 + 7339749 * 2 ^ 59
def prefixEnd_7339749 : Nat := 4983230072969 + 3 ^ 40 * 7339749 * 2
def baseEnd_7339749 : Nat := 3768819120357108931982615

theorem tailTrace_7339749 : CollatzResearch.WordTrace tailWord_7339749 prefixEnd_7339749 3768819120357108931982615 := by
  unfold tailWord_7339749
  simp only [CollatzResearch.WordTrace]
  refine ⟨267702638686350377175742301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178468425790900251450494867 267702638686350377175742301)
  ·
    refine ⟨100388489507381391440903363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267702638686350377175742301 100388489507381391440903363)
    ·
      refine ⟨150582734261072087161355045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100388489507381391440903363 150582734261072087161355045)
      ·
        refine ⟨28234262673951016342754071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150582734261072087161355045 28234262673951016342754071)
        ·
          refine ⟨42351394010926524514131107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28234262673951016342754071 42351394010926524514131107)
          ·
            refine ⟨63527091016389786771196661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42351394010926524514131107 63527091016389786771196661)
            ·
              refine ⟨5955664782786542509799687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63527091016389786771196661 5955664782786542509799687)
              ·
                refine ⟨8933497174179813764699531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5955664782786542509799687 8933497174179813764699531)
                ·
                  refine ⟨13400245761269720647049297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8933497174179813764699531 13400245761269720647049297)
                  ·
                    refine ⟨10050184320952290485286973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13400245761269720647049297 10050184320952290485286973)
                    ·
                      refine ⟨3768819120357108931982615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10050184320952290485286973 3768819120357108931982615)
                      ·
                        rfl

theorem cell23_7339749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_7339749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339749 prefixEnd_7339749 := by exact prefixLift 7339749
  have htrace : WordTrace (prefixWord ++ tailWord_7339749) baseStart_7339749 baseEnd_7339749 := by
    simpa [prefixWord, tailWord_7339749, baseEnd_7339749] using wordTrace_append hprefix tailTrace_7339749
  have hstable : (prefixWord ++ tailWord_7339749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339749).length < 2 ^ (prefixWord ++ tailWord_7339749).sum := by decide
  have hdescent : baseEnd_7339749 < baseStart_7339749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339772 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 5, 3, 2]
def baseStart_7339772 : Nat := 118140960795 + 7339772 * 2 ^ 59
def prefixEnd_7339772 : Nat := 4983230072969 + 3 ^ 40 * 7339772 * 2
def baseEnd_7339772 : Nat := 3768830930412162341995009

theorem tailTrace_7339772 : CollatzResearch.WordTrace tailWord_7339772 prefixEnd_7339772 3768830930412162341995009 := by
  unfold tailWord_7339772
  simp only [CollatzResearch.WordTrace]
  refine ⟨133851738782633526051914785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178468985043511368069219713 133851738782633526051914785)
  ·
    refine ⟨100388804086975144538936089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133851738782633526051914785 100388804086975144538936089)
    ·
      refine ⟨75291603065231358404202067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100388804086975144538936089 75291603065231358404202067)
      ·
        refine ⟨112937404597847037606303101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75291603065231358404202067 112937404597847037606303101)
        ·
          refine ⟨42351526724192639102363663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112937404597847037606303101 42351526724192639102363663)
          ·
            refine ⟨63527290086288958653545495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42351526724192639102363663 63527290086288958653545495)
            ·
              refine ⟨95290935129433437980318243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63527290086288958653545495 95290935129433437980318243)
              ·
                refine ⟨142936402694150156970477365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95290935129433437980318243 142936402694150156970477365)
                ·
                  refine ⟨13400287752576577215982253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142936402694150156970477365 13400287752576577215982253)
                  ·
                    refine ⟨5025107907216216455993345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13400287752576577215982253 5025107907216216455993345)
                    ·
                      refine ⟨3768830930412162341995009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5025107907216216455993345 3768830930412162341995009)
                      ·
                        rfl

theorem cell23_7339772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_7339772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339772 prefixEnd_7339772 := by exact prefixLift 7339772
  have htrace : WordTrace (prefixWord ++ tailWord_7339772) baseStart_7339772 baseEnd_7339772 := by
    simpa [prefixWord, tailWord_7339772, baseEnd_7339772] using wordTrace_append hprefix tailTrace_7339772
  have hstable : (prefixWord ++ tailWord_7339772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339772).length < 2 ^ (prefixWord ++ tailWord_7339772).sum := by decide
  have hdescent : baseEnd_7339772 < baseStart_7339772 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339825 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 7]
def baseStart_7339825 : Nat := 118140960795 + 7339825 * 2 ^ 59
def prefixEnd_7339825 : Nat := 4983230072969 + 3 ^ 40 * 7339825 * 2
def baseEnd_7339825 : Nat := 418762016098538959403585

theorem tailTrace_7339825 : CollatzResearch.WordTrace tailWord_7339825 prefixEnd_7339825 418762016098538959403585 := by
  unfold tailWord_7339825
  simp only [CollatzResearch.WordTrace]
  refine ⟨267705410634075042155508929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178470273756050028103672619 267705410634075042155508929)
  ·
    refine ⟨200779057975556281616631697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267705410634075042155508929 200779057975556281616631697)
    ·
      refine ⟨150584293481667211212473773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200779057975556281616631697 150584293481667211212473773)
      ·
        refine ⟨56469110055625204204677665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150584293481667211212473773 56469110055625204204677665)
        ·
          refine ⟨42351832541718903153508249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56469110055625204204677665 42351832541718903153508249)
          ·
            refine ⟨31763874406289177365131187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42351832541718903153508249 31763874406289177365131187)
            ·
              refine ⟨47645811609433766047696781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31763874406289177365131187 47645811609433766047696781)
              ·
                refine ⟨17867179353537662267886293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47645811609433766047696781 17867179353537662267886293)
                ·
                  refine ⟨418762016098538959403585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17867179353537662267886293 418762016098538959403585)
                  ·
                    rfl

theorem cell23_7339825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 7].length) (baseStart_7339825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339825 prefixEnd_7339825 := by exact prefixLift 7339825
  have htrace : WordTrace (prefixWord ++ tailWord_7339825) baseStart_7339825 baseEnd_7339825 := by
    simpa [prefixWord, tailWord_7339825, baseEnd_7339825] using wordTrace_append hprefix tailTrace_7339825
  have hstable : (prefixWord ++ tailWord_7339825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339825).length < 2 ^ (prefixWord ++ tailWord_7339825).sum := by decide
  have hdescent : baseEnd_7339825 < baseStart_7339825 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339865 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 1, 2, 5]
def baseStart_7339865 : Nat := 118140960795 + 7339865 * 2 ^ 59
def prefixEnd_7339865 : Nat := 4983230072969 + 3 ^ 40 * 7339865 * 2
def baseEnd_7339865 : Nat := 3768878684113030478132081

theorem tailTrace_7339865 : CollatzResearch.WordTrace tailWord_7339865 prefixEnd_7339865 3768878684113030478132081 := by
  unfold tailWord_7339865
  simp only [CollatzResearch.WordTrace]
  refine ⟨267706869553930128986965049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178471246369286752657976699 267706869553930128986965049)
  ·
    refine ⟨200780152165447596740223787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267706869553930128986965049 200780152165447596740223787)
    ·
      refine ⟨301170228248171395110335681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200780152165447596740223787 301170228248171395110335681)
      ·
        refine ⟨225877671186128546332751761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 301170228248171395110335681 225877671186128546332751761)
        ·
          refine ⟨169408253389596409749563821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225877671186128546332751761 169408253389596409749563821)
          ·
            refine ⟨63528095021098653656086433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169408253389596409749563821 63528095021098653656086433)
            ·
              refine ⟨47646071265823990242064825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63528095021098653656086433 47646071265823990242064825)
              ·
                refine ⟨35734553449367992681548619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47646071265823990242064825 35734553449367992681548619)
                ·
                  refine ⟨53601830174051989022322929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35734553449367992681548619 53601830174051989022322929)
                  ·
                    refine ⟨40201372630538991766742197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53601830174051989022322929 40201372630538991766742197)
                    ·
                      refine ⟨3768878684113030478132081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40201372630538991766742197 3768878684113030478132081)
                      ·
                        rfl

theorem cell23_7339865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_7339865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339865 prefixEnd_7339865 := by exact prefixLift 7339865
  have htrace : WordTrace (prefixWord ++ tailWord_7339865) baseStart_7339865 baseEnd_7339865 := by
    simpa [prefixWord, tailWord_7339865, baseEnd_7339865] using wordTrace_append hprefix tailTrace_7339865
  have hstable : (prefixWord ++ tailWord_7339865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339865).length < 2 ^ (prefixWord ++ tailWord_7339865).sum := by decide
  have hdescent : baseEnd_7339865 < baseStart_7339865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339872 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 2, 5]
def baseStart_7339872 : Nat := 118140960795 + 7339872 * 2 ^ 59
def prefixEnd_7339872 : Nat := 4983230072969 + 3 ^ 40 * 7339872 * 2
def baseEnd_7339872 : Nat := 1256294092825870650248183

theorem tailTrace_7339872 : CollatzResearch.WordTrace tailWord_7339872 prefixEnd_7339872 1256294092825870650248183 := by
  unfold tailWord_7339872
  simp only [CollatzResearch.WordTrace]
  refine ⟨133853562432452384591234935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178471416576603179454979913 133853562432452384591234935)
  ·
    refine ⟨200780343648678576886852403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133853562432452384591234935 200780343648678576886852403)
    ·
      refine ⟨301170515473017865330278605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200780343648678576886852403 301170515473017865330278605)
      ·
        refine ⟨112938943302381699498854477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 301170515473017865330278605 112938943302381699498854477)
        ·
          refine ⟨42352103738393137312070429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112938943302381699498854477 42352103738393137312070429)
          ·
            refine ⟨15882038901897426492026411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42352103738393137312070429 15882038901897426492026411)
            ·
              refine ⟨23823058352846139738039617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15882038901897426492026411 23823058352846139738039617)
              ·
                refine ⟨17867293764634604803529713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23823058352846139738039617 17867293764634604803529713)
                ·
                  refine ⟨13400470323475953602647285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17867293764634604803529713 13400470323475953602647285)
                  ·
                    refine ⟨1256294092825870650248183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13400470323475953602647285 1256294092825870650248183)
                    ·
                      rfl

theorem cell23_7339872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 2, 5].length) (baseStart_7339872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339872 prefixEnd_7339872 := by exact prefixLift 7339872
  have htrace : WordTrace (prefixWord ++ tailWord_7339872) baseStart_7339872 baseEnd_7339872 := by
    simpa [prefixWord, tailWord_7339872, baseEnd_7339872] using wordTrace_append hprefix tailTrace_7339872
  have hstable : (prefixWord ++ tailWord_7339872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339872).length < 2 ^ (prefixWord ++ tailWord_7339872).sum := by decide
  have hdescent : baseEnd_7339872 < baseStart_7339872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339876 : List Nat := [2, 3, 1, 1, 5, 1, 3, 2, 5]
def baseStart_7339876 : Nat := 118140960795 + 7339876 * 2 ^ 59
def prefixEnd_7339876 : Nat := 4983230072969 + 3 ^ 40 * 7339876 * 2
def baseEnd_7339876 : Nat := 418764925822247770566059

theorem tailTrace_7339876 : CollatzResearch.WordTrace tailWord_7339876 prefixEnd_7339876 418764925822247770566059 := by
  unfold tailWord_7339876
  simp only [CollatzResearch.WordTrace]
  refine ⟨133853635378445138932807741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178471513837926851910410321 133853635378445138932807741)
  ·
    refine ⟨50195113266916927099802903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133853635378445138932807741 50195113266916927099802903)
    ·
      refine ⟨75292669900375390649704355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50195113266916927099802903 75292669900375390649704355)
      ·
        refine ⟨112939004850563085974556533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75292669900375390649704355 112939004850563085974556533)
        ·
          refine ⟨10588031704740289310114675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112939004850563085974556533 10588031704740289310114675)
          ·
            refine ⟨15882047557110433965172013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10588031704740289310114675 15882047557110433965172013)
            ·
              refine ⟨5955767833916412736939505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15882047557110433965172013 5955767833916412736939505)
              ·
                refine ⟨4466825875437309552704629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5955767833916412736939505 4466825875437309552704629)
                ·
                  refine ⟨418764925822247770566059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4466825875437309552704629 418764925822247770566059)
                  ·
                    rfl

theorem cell23_7339876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_7339876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339876 prefixEnd_7339876 := by exact prefixLift 7339876
  have htrace : WordTrace (prefixWord ++ tailWord_7339876) baseStart_7339876 baseEnd_7339876 := by
    simpa [prefixWord, tailWord_7339876, baseEnd_7339876] using wordTrace_append hprefix tailTrace_7339876
  have hstable : (prefixWord ++ tailWord_7339876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339876).length < 2 ^ (prefixWord ++ tailWord_7339876).sum := by decide
  have hdescent : baseEnd_7339876 < baseStart_7339876 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7339955 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 7]
def baseStart_7339955 : Nat := 118140960795 + 7339955 * 2 ^ 59
def prefixEnd_7339955 : Nat := 4983230072969 + 3 ^ 40 * 7339955 * 2
def baseEnd_7339955 : Nat := 3768924897371935126006667

theorem tailTrace_7339955 : CollatzResearch.WordTrace tailWord_7339955 prefixEnd_7339955 3768924897371935126006667 := by
  unfold tailWord_7339955
  simp only [CollatzResearch.WordTrace]
  refine ⟨267710152123604074357741319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178473434749069382905160879 267710152123604074357741319)
  ·
    refine ⟨401565228185406111536611979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267710152123604074357741319 401565228185406111536611979)
    ·
      refine ⟨602347842278109167304917969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401565228185406111536611979 602347842278109167304917969)
      ·
        refine ⟨451760881708581875478688477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 602347842278109167304917969 451760881708581875478688477)
        ·
          refine ⟨169410330640718203304508179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451760881708581875478688477 169410330640718203304508179)
          ·
            refine ⟨254115495961077304956762269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169410330640718203304508179 254115495961077304956762269)
            ·
              refine ⟨95293310985403989358785851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254115495961077304956762269 95293310985403989358785851)
              ·
                refine ⟨142939966478105984038178777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95293310985403989358785851 142939966478105984038178777)
                ·
                  refine ⟨107204974858579488028634083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142939966478105984038178777 107204974858579488028634083)
                  ·
                    refine ⟨160807462287869232042951125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107204974858579488028634083 160807462287869232042951125)
                    ·
                      refine ⟨3768924897371935126006667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160807462287869232042951125 3768924897371935126006667)
                      ·
                        rfl

theorem cell23_7339955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_7339955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7339955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7339955 prefixEnd_7339955 := by exact prefixLift 7339955
  have htrace : WordTrace (prefixWord ++ tailWord_7339955) baseStart_7339955 baseEnd_7339955 := by
    simpa [prefixWord, tailWord_7339955, baseEnd_7339955] using wordTrace_append hprefix tailTrace_7339955
  have hstable : (prefixWord ++ tailWord_7339955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7339955).length < 2 ^ (prefixWord ++ tailWord_7339955).sum := by decide
  have hdescent : baseEnd_7339955 < baseStart_7339955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7339955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340013 : List Nat := [1, 5, 1, 4, 1, 1, 2, 2, 1, 5]
def baseStart_7340013 : Nat := 118140960795 + 7340013 * 2 ^ 59
def prefixEnd_7340013 : Nat := 4983230072969 + 3 ^ 40 * 7340013 * 2
def baseEnd_7340013 : Nat := 1256318226416631966360467

theorem tailTrace_7340013 : CollatzResearch.WordTrace tailWord_7340013 prefixEnd_7340013 1256318226416631966360467 := by
  unfold tailWord_7340013
  simp only [CollatzResearch.WordTrace]
  refine ⟨267712267557393950263352693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178474845038262633508901795 267712267557393950263352693)
  ·
    refine ⟨25098025083505682837189315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267712267557393950263352693 25098025083505682837189315)
    ·
      refine ⟨37647037625258524255783973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25098025083505682837189315 37647037625258524255783973)
      ·
        refine ⟨7058819554735973297959495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37647037625258524255783973 7058819554735973297959495)
        ·
          refine ⟨10588229332103959946939243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7058819554735973297959495 10588229332103959946939243)
          ·
            refine ⟨15882343998155939920408865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10588229332103959946939243 15882343998155939920408865)
            ·
              refine ⟨11911757998616954940306649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15882343998155939920408865 11911757998616954940306649)
              ·
                refine ⟨8933818498962716205229987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11911757998616954940306649 8933818498962716205229987)
                ·
                  refine ⟨13400727748444074307844981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8933818498962716205229987 13400727748444074307844981)
                  ·
                    refine ⟨1256318226416631966360467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13400727748444074307844981 1256318226416631966360467)
                    ·
                      rfl

theorem cell23_7340013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_7340013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340013 prefixEnd_7340013 := by exact prefixLift 7340013
  have htrace : WordTrace (prefixWord ++ tailWord_7340013) baseStart_7340013 baseEnd_7340013 := by
    simpa [prefixWord, tailWord_7340013, baseEnd_7340013] using wordTrace_append hprefix tailTrace_7340013
  have hstable : (prefixWord ++ tailWord_7340013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340013).length < 2 ^ (prefixWord ++ tailWord_7340013).sum := by decide
  have hdescent : baseEnd_7340013 < baseStart_7340013 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340016 : List Nat := [2, 1, 1, 1, 3, 2, 4, 2, 3, 2, 2]
def baseStart_7340016 : Nat := 118140960795 + 7340016 * 2 ^ 59
def prefixEnd_7340016 : Nat := 4983230072969 + 3 ^ 40 * 7340016 * 2
def baseEnd_7340016 : Nat := 3768956219691859387343887

theorem tailTrace_7340016 : CollatzResearch.WordTrace tailWord_7340016 prefixEnd_7340016 3768956219691859387343887 := by
  unfold tailWord_7340016
  simp only [CollatzResearch.WordTrace]
  refine ⟨133856188488191540887855951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178474917984255387850474601 133856188488191540887855951)
  ·
    refine ⟨200784282732287311331783927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133856188488191540887855951 200784282732287311331783927)
    ·
      refine ⟨301176424098430966997675891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200784282732287311331783927 301176424098430966997675891)
      ·
        refine ⟨451764636147646450496513837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 301176424098430966997675891 451764636147646450496513837)
        ·
          refine ⟨169411738555367418936192689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451764636147646450496513837 169411738555367418936192689)
          ·
            refine ⟨127058803916525564202144517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169411738555367418936192689 127058803916525564202144517)
            ·
              refine ⟨23823525734348543287902097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127058803916525564202144517 23823525734348543287902097)
              ·
                refine ⟨17867644300761407465926573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23823525734348543287902097 17867644300761407465926573)
                ·
                  refine ⟨6700366612785527799722465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17867644300761407465926573 6700366612785527799722465)
                  ·
                    refine ⟨5025274959589145849791849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6700366612785527799722465 5025274959589145849791849)
                    ·
                      refine ⟨3768956219691859387343887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5025274959589145849791849 3768956219691859387343887)
                      ·
                        rfl

theorem cell23_7340016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 2, 3, 2, 2].length) (baseStart_7340016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340016 prefixEnd_7340016 := by exact prefixLift 7340016
  have htrace : WordTrace (prefixWord ++ tailWord_7340016) baseStart_7340016 baseEnd_7340016 := by
    simpa [prefixWord, tailWord_7340016, baseEnd_7340016] using wordTrace_append hprefix tailTrace_7340016
  have hstable : (prefixWord ++ tailWord_7340016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340016).length < 2 ^ (prefixWord ++ tailWord_7340016).sum := by decide
  have hdescent : baseEnd_7340016 < baseStart_7340016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340076 : List Nat := [2, 2, 1, 1, 1, 2, 2, 6, 1, 3, 2]
def baseStart_7340076 : Nat := 118140960795 + 7340076 * 2 ^ 59
def prefixEnd_7340076 : Nat := 4983230072969 + 3 ^ 40 * 7340076 * 2
def baseEnd_7340076 : Nat := 3768987028531129152593611

theorem tailTrace_7340076 : CollatzResearch.WordTrace tailWord_7340076 prefixEnd_7340076 3768987028531129152593611 := by
  unfold tailWord_7340076
  simp only [CollatzResearch.WordTrace]
  refine ⟨133857282678082856011448041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178476376904110474681930721 133857282678082856011448041)
  ·
    refine ⟨100392962008562142008586031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133857282678082856011448041 100392962008562142008586031)
    ·
      refine ⟨150589443012843213012879047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100392962008562142008586031 150589443012843213012879047)
      ·
        refine ⟨225884164519264819519318571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150589443012843213012879047 225884164519264819519318571)
        ·
          refine ⟨338826246778897229278977857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225884164519264819519318571 338826246778897229278977857)
          ·
            refine ⟨254119685084172921959233393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338826246778897229278977857 254119685084172921959233393)
            ·
              refine ⟨190589763813129691469425045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 254119685084172921959233393 190589763813129691469425045)
              ·
                refine ⟨8933895178740454287629299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 190589763813129691469425045 8933895178740454287629299)
                ·
                  refine ⟨13400842768110681431443949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8933895178740454287629299 13400842768110681431443949)
                  ·
                    refine ⟨5025316038041505536791481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13400842768110681431443949 5025316038041505536791481)
                    ·
                      refine ⟨3768987028531129152593611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5025316038041505536791481 3768987028531129152593611)
                      ·
                        rfl

theorem cell23_7340076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 3, 2].length) (baseStart_7340076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340076 prefixEnd_7340076 := by exact prefixLift 7340076
  have htrace : WordTrace (prefixWord ++ tailWord_7340076) baseStart_7340076 baseEnd_7340076 := by
    simpa [prefixWord, tailWord_7340076, baseEnd_7340076] using wordTrace_append hprefix tailTrace_7340076
  have hstable : (prefixWord ++ tailWord_7340076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340076).length < 2 ^ (prefixWord ++ tailWord_7340076).sum := by decide
  have hdescent : baseEnd_7340076 < baseStart_7340076 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340146 : List Nat := [3, 2, 1, 2, 2, 2, 1, 5, 5]
def baseStart_7340146 : Nat := 118140960795 + 7340146 * 2 ^ 59
def prefixEnd_7340146 : Nat := 4983230072969 + 3 ^ 40 * 7340146 * 2
def baseEnd_7340146 : Nat := 418780330241882653190921

theorem tailTrace_7340146 : CollatzResearch.WordTrace tailWord_7340146 prefixEnd_7340146 418780330241882653190921 := by
  unfold tailWord_7340146
  simp only [CollatzResearch.WordTrace]
  refine ⟨66929279616478028494486073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178478078977274742651962861 66929279616478028494486073)
  ·
    refine ⟨50196959712358521370864555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66929279616478028494486073 50196959712358521370864555)
    ·
      refine ⟨75295439568537782056296833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50196959712358521370864555 75295439568537782056296833)
      ·
        refine ⟨56471579676403336542222625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75295439568537782056296833 56471579676403336542222625)
        ·
          refine ⟨42353684757302502406666969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56471579676403336542222625 42353684757302502406666969)
          ·
            refine ⟨31765263567976876805000227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42353684757302502406666969 31765263567976876805000227)
            ·
              refine ⟨47647895351965315207500341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31765263567976876805000227 47647895351965315207500341)
              ·
                refine ⟨4466990189246748300703157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47647895351965315207500341 4466990189246748300703157)
                ·
                  refine ⟨418780330241882653190921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4466990189246748300703157 418780330241882653190921)
                  ·
                    rfl

theorem cell23_7340146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 5].length) (baseStart_7340146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340146 prefixEnd_7340146 := by exact prefixLift 7340146
  have htrace : WordTrace (prefixWord ++ tailWord_7340146) baseStart_7340146 baseEnd_7340146 := by
    simpa [prefixWord, tailWord_7340146, baseEnd_7340146] using wordTrace_append hprefix tailTrace_7340146
  have hstable : (prefixWord ++ tailWord_7340146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340146).length < 2 ^ (prefixWord ++ tailWord_7340146).sum := by decide
  have hdescent : baseEnd_7340146 < baseStart_7340146 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340216 : List Nat := [2, 1, 2, 1, 2, 1, 5, 2, 2, 2, 3]
def baseStart_7340216 : Nat := 118140960795 + 7340216 * 2 ^ 59
def prefixEnd_7340216 : Nat := 4983230072969 + 3 ^ 40 * 7340216 * 2
def baseEnd_7340216 : Nat := 3769058915822758604842967

theorem tailTrace_7340216 : CollatzResearch.WordTrace tailWord_7340216 prefixEnd_7340216 3769058915822758604842967 := by
  unfold tailWord_7340216
  simp only [CollatzResearch.WordTrace]
  refine ⟨133859835787829257966496251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178479781050439010621995001 133859835787829257966496251)
  ·
    refine ⟨200789753681743886949744377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133859835787829257966496251 200789753681743886949744377)
    ·
      refine ⟨150592315261307915212308283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200789753681743886949744377 150592315261307915212308283)
      ·
        refine ⟨225888472891961872818462425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150592315261307915212308283 225888472891961872818462425)
        ·
          refine ⟨169416354668971404613846819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225888472891961872818462425 169416354668971404613846819)
          ·
            refine ⟨254124532003457106920770229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169416354668971404613846819 254124532003457106920770229)
            ·
              refine ⟨23824174875324103773822209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 254124532003457106920770229 23824174875324103773822209)
              ·
                refine ⟨17868131156493077830366657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23824174875324103773822209 17868131156493077830366657)
                ·
                  refine ⟨13401098367369808372774993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17868131156493077830366657 13401098367369808372774993)
                  ·
                    refine ⟨10050823775527356279581245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13401098367369808372774993 10050823775527356279581245)
                    ·
                      refine ⟨3769058915822758604842967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10050823775527356279581245 3769058915822758604842967)
                      ·
                        rfl

theorem cell23_7340216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 2, 2, 2, 3].length) (baseStart_7340216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340216 prefixEnd_7340216 := by exact prefixLift 7340216
  have htrace : WordTrace (prefixWord ++ tailWord_7340216) baseStart_7340216 baseEnd_7340216 := by
    simpa [prefixWord, tailWord_7340216, baseEnd_7340216] using wordTrace_append hprefix tailTrace_7340216
  have hstable : (prefixWord ++ tailWord_7340216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340216).length < 2 ^ (prefixWord ++ tailWord_7340216).sum := by decide
  have hdescent : baseEnd_7340216 < baseStart_7340216 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340219 : List Nat := [1, 1, 1, 1, 1, 2, 6, 4, 6]
def baseStart_7340219 : Nat := 118140960795 + 7340219 * 2 ^ 59
def prefixEnd_7340219 : Nat := 4983230072969 + 3 ^ 40 * 7340219 * 2
def baseEnd_7340219 : Nat := 418784495140524677011717

theorem tailTrace_7340219 : CollatzResearch.WordTrace tailWord_7340219 prefixEnd_7340219 418784495140524677011717 := by
  unfold tailWord_7340219
  simp only [CollatzResearch.WordTrace]
  refine ⟨267719780994647647445351711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178479853996431764963567807 267719780994647647445351711)
  ·
    refine ⟨401579671491971471168027567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267719780994647647445351711 401579671491971471168027567)
    ·
      refine ⟨602369507237957206752041351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401579671491971471168027567 602369507237957206752041351)
      ·
        refine ⟨903554260856935810128062027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 602369507237957206752041351 903554260856935810128062027)
        ·
          refine ⟨1355331391285403715192093041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 903554260856935810128062027 1355331391285403715192093041)
          ·
            refine ⟨1016498543464052786394069781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1355331391285403715192093041 1016498543464052786394069781)
            ·
              refine ⟨47648369224877474362222021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1016498543464052786394069781 47648369224877474362222021)
              ·
                refine ⟨8934069229664526442916629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47648369224877474362222021 8934069229664526442916629)
                ·
                  refine ⟨418784495140524677011717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8934069229664526442916629 418784495140524677011717)
                  ·
                    rfl

theorem cell23_7340219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 6].length) (baseStart_7340219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340219 prefixEnd_7340219 := by exact prefixLift 7340219
  have htrace : WordTrace (prefixWord ++ tailWord_7340219) baseStart_7340219 baseEnd_7340219 := by
    simpa [prefixWord, tailWord_7340219, baseEnd_7340219] using wordTrace_append hprefix tailTrace_7340219
  have hstable : (prefixWord ++ tailWord_7340219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340219).length < 2 ^ (prefixWord ++ tailWord_7340219).sum := by decide
  have hdescent : baseEnd_7340219 < baseStart_7340219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340273 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 2, 3, 2]
def baseStart_7340273 : Nat := 118140960795 + 7340273 * 2 ^ 59
def prefixEnd_7340273 : Nat := 4983230072969 + 3 ^ 40 * 7340273 * 2
def baseEnd_7340273 : Nat := 3769088184220064881830205

theorem tailTrace_7340273 : CollatzResearch.WordTrace tailWord_7340273 prefixEnd_7340273 3769088184220064881830205 := by
  unfold tailWord_7340273
  simp only [CollatzResearch.WordTrace]
  refine ⟨267721750536452014667817473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178481167024301343111878315 267721750536452014667817473)
  ·
    refine ⟨200791312902339011000863105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267721750536452014667817473 200791312902339011000863105)
    ·
      refine ⟨150593484676754258250647329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200791312902339011000863105 150593484676754258250647329)
      ·
        refine ⟨112945113507565693687985497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150593484676754258250647329 112945113507565693687985497)
        ·
          refine ⟨84708835130674270265989123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112945113507565693687985497 84708835130674270265989123)
          ·
            refine ⟨127063252696011405398983685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84708835130674270265989123 127063252696011405398983685)
            ·
              refine ⟨23824359880502138512309441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 127063252696011405398983685 23824359880502138512309441)
              ·
                refine ⟨17868269910376603884232081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23824359880502138512309441 17868269910376603884232081)
                ·
                  refine ⟨13401202432782452913174061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17868269910376603884232081 13401202432782452913174061)
                  ·
                    refine ⟨5025450912293419842440273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13401202432782452913174061 5025450912293419842440273)
                    ·
                      refine ⟨3769088184220064881830205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5025450912293419842440273 3769088184220064881830205)
                      ·
                        rfl

theorem cell23_7340273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 2, 3, 2].length) (baseStart_7340273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340273 prefixEnd_7340273 := by exact prefixLift 7340273
  have htrace : WordTrace (prefixWord ++ tailWord_7340273) baseStart_7340273 baseEnd_7340273 := by
    simpa [prefixWord, tailWord_7340273, baseEnd_7340273] using wordTrace_append hprefix tailTrace_7340273
  have hstable : (prefixWord ++ tailWord_7340273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340273).length < 2 ^ (prefixWord ++ tailWord_7340273).sum := by decide
  have hdescent : baseEnd_7340273 < baseStart_7340273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340296 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 1, 6]
def baseStart_7340296 : Nat := 118140960795 + 7340296 * 2 ^ 59
def prefixEnd_7340296 : Nat := 4983230072969 + 3 ^ 40 * 7340296 * 2
def baseEnd_7340296 : Nat := 1256366664758372763947533

theorem tailTrace_7340296 : CollatzResearch.WordTrace tailWord_7340296 prefixEnd_7340296 1256366664758372763947533 := by
  unfold tailWord_7340296
  simp only [CollatzResearch.WordTrace]
  refine ⟨133861294707684344797952371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178481726276912459730603161 133861294707684344797952371)
  ·
    refine ⟨200791942061526517196928557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133861294707684344797952371 200791942061526517196928557)
    ·
      refine ⟨75296978273072443948848209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200791942061526517196928557 75296978273072443948848209)
      ·
        refine ⟨56472733704804332961636157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75296978273072443948848209 56472733704804332961636157)
        ·
          refine ⟨21177275139301624860613559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56472733704804332961636157 21177275139301624860613559)
          ·
            refine ⟨31765912708952437290920339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21177275139301624860613559 31765912708952437290920339)
            ·
              refine ⟨47648869063428655936380509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31765912708952437290920339 47648869063428655936380509)
              ·
                refine ⟨17868325898785745976142691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47648869063428655936380509 17868325898785745976142691)
                ·
                  refine ⟨26802488848178618964214037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17868325898785745976142691 26802488848178618964214037)
                  ·
                    refine ⟨1256366664758372763947533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26802488848178618964214037 1256366664758372763947533)
                    ·
                      rfl

theorem cell23_7340296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_7340296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340296 prefixEnd_7340296 := by exact prefixLift 7340296
  have htrace : WordTrace (prefixWord ++ tailWord_7340296) baseStart_7340296 baseEnd_7340296 := by
    simpa [prefixWord, tailWord_7340296, baseEnd_7340296] using wordTrace_append hprefix tailTrace_7340296
  have hstable : (prefixWord ++ tailWord_7340296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340296).length < 2 ^ (prefixWord ++ tailWord_7340296).sum := by decide
  have hdescent : baseEnd_7340296 < baseStart_7340296 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340309 : List Nat := [1, 3, 2, 1, 2, 1, 2, 11]
def baseStart_7340309 : Nat := 118140960795 + 7340309 * 2 ^ 59
def prefixEnd_7340309 : Nat := 4983230072969 + 3 ^ 40 * 7340309 * 2
def baseEnd_7340309 : Nat := 139596543315689879295557

theorem tailTrace_7340309 : CollatzResearch.WordTrace tailWord_7340309 prefixEnd_7340309 139596543315689879295557 := by
  unfold tailWord_7340309
  simp only [CollatzResearch.WordTrace]
  refine ⟨267723063564321592816127981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178482042376214395210751987 267723063564321592816127981)
  ·
    refine ⟨100396148836620597306047993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267723063564321592816127981 100396148836620597306047993)
    ·
      refine ⟨75297111627465447979535995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100396148836620597306047993 75297111627465447979535995)
      ·
        refine ⟨112945667441198171969303993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75297111627465447979535995 112945667441198171969303993)
        ·
          refine ⟨84709250580898628976977995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112945667441198171969303993 84709250580898628976977995)
          ·
            refine ⟨127063875871347943465466993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84709250580898628976977995 127063875871347943465466993)
            ·
              refine ⟨95297906903510957599100245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 127063875871347943465466993 95297906903510957599100245)
              ·
                refine ⟨139596543315689879295557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 95297906903510957599100245 139596543315689879295557)
                ·
                  rfl

theorem cell23_7340309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 11].length) (baseStart_7340309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340309 prefixEnd_7340309 := by exact prefixLift 7340309
  have htrace : WordTrace (prefixWord ++ tailWord_7340309) baseStart_7340309 baseEnd_7340309 := by
    simpa [prefixWord, tailWord_7340309, baseEnd_7340309] using wordTrace_append hprefix tailTrace_7340309
  have hstable : (prefixWord ++ tailWord_7340309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340309).length < 2 ^ (prefixWord ++ tailWord_7340309).sum := by decide
  have hdescent : baseEnd_7340309 < baseStart_7340309 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340317 : List Nat := [1, 4, 2, 3, 2, 2, 2, 1, 1, 5]
def baseStart_7340317 : Nat := 118140960795 + 7340317 * 2 ^ 59
def prefixEnd_7340317 : Nat := 4983230072969 + 3 ^ 40 * 7340317 * 2
def baseEnd_7340317 : Nat := 1256370259122954236560001

theorem tailTrace_7340317 : CollatzResearch.WordTrace tailWord_7340317 prefixEnd_7340317 1256370259122954236560001 := by
  unfold tailWord_7340317
  simp only [CollatzResearch.WordTrace]
  refine ⟨267723355348292610182419205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178482236898861740121612803 267723355348292610182419205)
  ·
    refine ⟨50198129127804864409203601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267723355348292610182419205 50198129127804864409203601)
    ·
      refine ⟨37648596845853648306902701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50198129127804864409203601 37648596845853648306902701)
      ·
        refine ⟨14118223817195118115088513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37648596845853648306902701 14118223817195118115088513)
        ·
          refine ⟨10588667862896338586316385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14118223817195118115088513 10588667862896338586316385)
          ·
            refine ⟨7941500897172253939737289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10588667862896338586316385 7941500897172253939737289)
            ·
              refine ⟨5956125672879190454802967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7941500897172253939737289 5956125672879190454802967)
              ·
                refine ⟨8934188509318785682204451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5956125672879190454802967 8934188509318785682204451)
                ·
                  refine ⟨13401282763978178523306677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8934188509318785682204451 13401282763978178523306677)
                  ·
                    refine ⟨1256370259122954236560001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13401282763978178523306677 1256370259122954236560001)
                    ·
                      rfl

theorem cell23_7340317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 1, 5].length) (baseStart_7340317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340317 prefixEnd_7340317 := by exact prefixLift 7340317
  have htrace : WordTrace (prefixWord ++ tailWord_7340317) baseStart_7340317 baseEnd_7340317 := by
    simpa [prefixWord, tailWord_7340317, baseEnd_7340317] using wordTrace_append hprefix tailTrace_7340317
  have hstable : (prefixWord ++ tailWord_7340317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340317).length < 2 ^ (prefixWord ++ tailWord_7340317).sum := by decide
  have hdescent : baseEnd_7340317 < baseStart_7340317 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340320 : List Nat := [2, 1, 1, 5, 2, 1, 4, 1, 1, 1, 4]
def baseStart_7340320 : Nat := 118140960795 + 7340320 * 2 ^ 59
def prefixEnd_7340320 : Nat := 4983230072969 + 3 ^ 40 * 7340320 * 2
def baseEnd_7340320 : Nat := 3769112317810826197942489

theorem tailTrace_7340320 : CollatzResearch.WordTrace tailWord_7340320 prefixEnd_7340320 3769112317810826197942489 := by
  unfold tailWord_7340320
  simp only [CollatzResearch.WordTrace]
  refine ⟨133861732383640870847389207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178482309844854494463185609 133861732383640870847389207)
  ·
    refine ⟨200792598575461306271083811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133861732383640870847389207 200792598575461306271083811)
    ·
      refine ⟨301188897863191959406625717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200792598575461306271083811 301188897863191959406625717)
      ·
        refine ⟨28236459174674246194371161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 301188897863191959406625717 28236459174674246194371161)
        ·
          refine ⟨21177344381005684645778371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28236459174674246194371161 21177344381005684645778371)
          ·
            refine ⟨31766016571508526968667557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21177344381005684645778371 31766016571508526968667557)
            ·
              refine ⟨5956128107157848806625167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31766016571508526968667557 5956128107157848806625167)
              ·
                refine ⟨8934192160736773209937751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5956128107157848806625167 8934192160736773209937751)
                ·
                  refine ⟨13401288241105159814906627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8934192160736773209937751 13401288241105159814906627)
                  ·
                    refine ⟨20101932361657739722359941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13401288241105159814906627 20101932361657739722359941)
                    ·
                      refine ⟨3769112317810826197942489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20101932361657739722359941 3769112317810826197942489)
                      ·
                        rfl

theorem cell23_7340320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_7340320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340320 prefixEnd_7340320 := by exact prefixLift 7340320
  have htrace : WordTrace (prefixWord ++ tailWord_7340320) baseStart_7340320 baseEnd_7340320 := by
    simpa [prefixWord, tailWord_7340320, baseEnd_7340320] using wordTrace_append hprefix tailTrace_7340320
  have hstable : (prefixWord ++ tailWord_7340320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340320).length < 2 ^ (prefixWord ++ tailWord_7340320).sum := by decide
  have hdescent : baseEnd_7340320 < baseStart_7340320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340323 : List Nat := [1, 1, 1, 4, 2, 2, 3, 3, 1, 2, 3]
def baseStart_7340323 : Nat := 118140960795 + 7340323 * 2 ^ 59
def prefixEnd_7340323 : Nat := 4983230072969 + 3 ^ 40 * 7340323 * 2
def baseEnd_7340323 : Nat := 3769113858252789686204975

theorem tailTrace_7340323 : CollatzResearch.WordTrace tailWord_7340323 prefixEnd_7340323 3769113858252789686204975 := by
  unfold tailWord_7340323
  simp only [CollatzResearch.WordTrace]
  refine ⟨267723574186270873207137623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178482382790847248804758415 267723574186270873207137623)
  ·
    refine ⟨401585361279406309810706435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267723574186270873207137623 401585361279406309810706435)
    ·
      refine ⟨602378041919109464716059653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401585361279406309810706435 602378041919109464716059653)
      ·
        refine ⟨112945882859833024634261185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 602378041919109464716059653 112945882859833024634261185)
        ·
          refine ⟨84709412144874768475695889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112945882859833024634261185 84709412144874768475695889)
          ·
            refine ⟨63532059108656076356771917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84709412144874768475695889 63532059108656076356771917)
            ·
              refine ⟨23824522165746028633789469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63532059108656076356771917 23824522165746028633789469)
              ·
                refine ⟨8934195812154760737671051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23824522165746028633789469 8934195812154760737671051)
                ·
                  refine ⟨13401293718232141106506577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8934195812154760737671051 13401293718232141106506577)
                  ·
                    refine ⟨10050970288674105829879933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13401293718232141106506577 10050970288674105829879933)
                    ·
                      refine ⟨3769113858252789686204975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10050970288674105829879933 3769113858252789686204975)
                      ·
                        rfl

theorem cell23_7340323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_7340323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340323 prefixEnd_7340323 := by exact prefixLift 7340323
  have htrace : WordTrace (prefixWord ++ tailWord_7340323) baseStart_7340323 baseEnd_7340323 := by
    simpa [prefixWord, tailWord_7340323, baseEnd_7340323] using wordTrace_append hprefix tailTrace_7340323
  have hstable : (prefixWord ++ tailWord_7340323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340323).length < 2 ^ (prefixWord ++ tailWord_7340323).sum := by decide
  have hdescent : baseEnd_7340323 < baseStart_7340323 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340330 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 4, 4]
def baseStart_7340330 : Nat := 118140960795 + 7340330 * 2 ^ 59
def prefixEnd_7340330 : Nat := 4983230072969 + 3 ^ 40 * 7340330 * 2
def baseEnd_7340330 : Nat := 1256372484205790386272481

theorem tailTrace_7340330 : CollatzResearch.WordTrace tailWord_7340330 prefixEnd_7340330 1256372484205790386272481 := by
  unfold tailWord_7340330
  simp only [CollatzResearch.WordTrace]
  refine ⟨66930957374311378350660611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178482552998163675601761629 66930957374311378350660611)
  ·
    refine ⟨100396436061467067525990917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66930957374311378350660611 100396436061467067525990917)
    ·
      refine ⟨18824331761525075161123297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100396436061467067525990917 18824331761525075161123297)
      ·
        refine ⟨14118248821143806370842473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18824331761525075161123297 14118248821143806370842473)
        ·
          refine ⟨10588686615857854778131855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14118248821143806370842473 10588686615857854778131855)
          ·
            refine ⟨15883029923786782167197783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10588686615857854778131855 15883029923786782167197783)
            ·
              refine ⟨23824544885680173250796675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15883029923786782167197783 23824544885680173250796675)
              ·
                refine ⟨35736817328520259876195013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23824544885680173250796675 35736817328520259876195013)
                ·
                  refine ⟨6700653249097548726786565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35736817328520259876195013 6700653249097548726786565)
                  ·
                    refine ⟨1256372484205790386272481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6700653249097548726786565 1256372484205790386272481)
                    ·
                      rfl

theorem cell23_7340330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_7340330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340330 prefixEnd_7340330 := by exact prefixLift 7340330
  have htrace : WordTrace (prefixWord ++ tailWord_7340330) baseStart_7340330 baseEnd_7340330 := by
    simpa [prefixWord, tailWord_7340330, baseEnd_7340330] using wordTrace_append hprefix tailTrace_7340330
  have hstable : (prefixWord ++ tailWord_7340330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340330).length < 2 ^ (prefixWord ++ tailWord_7340330).sum := by decide
  have hdescent : baseEnd_7340330 < baseStart_7340330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340337 : List Nat := [1, 2, 2, 3, 4, 1, 2, 1, 3, 2, 2]
def baseStart_7340337 : Nat := 118140960795 + 7340337 * 2 ^ 59
def prefixEnd_7340337 : Nat := 4983230072969 + 3 ^ 40 * 7340337 * 2
def baseEnd_7340337 : Nat := 3769121046981952631429911

theorem tailTrace_7340337 : CollatzResearch.WordTrace tailWord_7340337 prefixEnd_7340337 3769121046981952631429911 := by
  unfold tailWord_7340337
  simp only [CollatzResearch.WordTrace]
  refine ⟨267724084808220153598147265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178482723205480102398764843 267724084808220153598147265)
  ·
    refine ⟨200793063606165115198610449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267724084808220153598147265 200793063606165115198610449)
    ·
      refine ⟨150594797704623836398957837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200793063606165115198610449 150594797704623836398957837)
      ·
        refine ⟨56473049139233938649609189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150594797704623836398957837 56473049139233938649609189)
        ·
          refine ⟨10588696713606363496801723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56473049139233938649609189 10588696713606363496801723)
          ·
            refine ⟨15883045070409545245202585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10588696713606363496801723 15883045070409545245202585)
            ·
              refine ⟨11912283802807158933901939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15883045070409545245202585 11912283802807158933901939)
              ·
                refine ⟨17868425704210738400852909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11912283802807158933901939 17868425704210738400852909)
                ·
                  refine ⟨6700659639079026900319841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17868425704210738400852909 6700659639079026900319841)
                  ·
                    refine ⟨5025494729309270175239881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6700659639079026900319841 5025494729309270175239881)
                    ·
                      refine ⟨3769121046981952631429911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5025494729309270175239881 3769121046981952631429911)
                      ·
                        rfl

theorem cell23_7340337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 2, 1, 3, 2, 2].length) (baseStart_7340337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340337 prefixEnd_7340337 := by exact prefixLift 7340337
  have htrace : WordTrace (prefixWord ++ tailWord_7340337) baseStart_7340337 baseEnd_7340337 := by
    simpa [prefixWord, tailWord_7340337, baseEnd_7340337] using wordTrace_append hprefix tailTrace_7340337
  have hstable : (prefixWord ++ tailWord_7340337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340337).length < 2 ^ (prefixWord ++ tailWord_7340337).sum := by decide
  have hdescent : baseEnd_7340337 < baseStart_7340337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340350 : List Nat := [4, 2, 1, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_7340350 : Nat := 118140960795 + 7340350 * 2 ^ 59
def prefixEnd_7340350 : Nat := 4983230072969 + 3 ^ 40 * 7340350 * 2
def baseEnd_7340350 : Nat := 3769127722230461080567351

theorem tailTrace_7340350 : CollatzResearch.WordTrace tailWord_7340350 prefixEnd_7340350 3769127722230461080567351 := by
  unfold tailWord_7340350
  simp only [CollatzResearch.WordTrace]
  refine ⟨33465569869646632102296313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178483039304782037878913669 33465569869646632102296313)
  ·
    refine ⟨25099177402234974076722235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33465569869646632102296313 25099177402234974076722235)
    ·
      refine ⟨37648766103352461115083353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25099177402234974076722235 37648766103352461115083353)
      ·
        refine ⟨28236574577514345836312515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37648766103352461115083353 28236574577514345836312515)
        ·
          refine ⟨42354861866271518754468773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28236574577514345836312515 42354861866271518754468773)
          ·
            refine ⟨7941536599925909766462895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42354861866271518754468773 7941536599925909766462895)
            ·
              refine ⟨11912304899888864649694343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7941536599925909766462895 11912304899888864649694343)
              ·
                refine ⟨17868457349833296974541515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11912304899888864649694343 17868457349833296974541515)
                ·
                  refine ⟨26802686024749945461812273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17868457349833296974541515 26802686024749945461812273)
                  ·
                    refine ⟨20102014518562459096359205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26802686024749945461812273 20102014518562459096359205)
                    ·
                      refine ⟨3769127722230461080567351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20102014518562459096359205 3769127722230461080567351)
                      ·
                        rfl

theorem cell23_7340350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_7340350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340350 prefixEnd_7340350 := by exact prefixLift 7340350
  have htrace : WordTrace (prefixWord ++ tailWord_7340350) baseStart_7340350 baseEnd_7340350 := by
    simpa [prefixWord, tailWord_7340350, baseEnd_7340350] using wordTrace_append hprefix tailTrace_7340350
  have hstable : (prefixWord ++ tailWord_7340350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340350).length < 2 ^ (prefixWord ++ tailWord_7340350).sum := by decide
  have hdescent : baseEnd_7340350 < baseStart_7340350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340438 : List Nat := [5, 3, 1, 2, 1, 1, 2, 2, 2, 1, 3]
def baseStart_7340438 : Nat := 118140960795 + 7340438 * 2 ^ 59
def prefixEnd_7340438 : Nat := 4983230072969 + 3 ^ 40 * 7340438 * 2
def baseEnd_7340438 : Nat := 3769172908528056736266947

theorem tailTrace_7340438 : CollatzResearch.WordTrace tailWord_7340438 prefixEnd_7340438 3769172908528056736266947 := by
  unfold tailWord_7340438
  simp only [CollatzResearch.WordTrace]
  refine ⟨16732985536303390490473373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178485179053902831898382645 16732985536303390490473373)
  ·
    refine ⟨6274869576113771433927515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16732985536303390490473373 6274869576113771433927515)
    ·
      refine ⟨9412304364170657150891273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6274869576113771433927515 9412304364170657150891273)
      ·
        refine ⟨7059228273127992863168455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9412304364170657150891273 7059228273127992863168455)
        ·
          refine ⟨10588842409691989294752683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7059228273127992863168455 10588842409691989294752683)
          ·
            refine ⟨15883263614537983942129025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10588842409691989294752683 15883263614537983942129025)
            ·
              refine ⟨11912447710903487956596769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15883263614537983942129025 11912447710903487956596769)
              ·
                refine ⟨8934335783177615967447577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11912447710903487956596769 8934335783177615967447577)
                ·
                  refine ⟨6700751837383211975585683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8934335783177615967447577 6700751837383211975585683)
                  ·
                    refine ⟨10051127756074817963378525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6700751837383211975585683 10051127756074817963378525)
                    ·
                      refine ⟨3769172908528056736266947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10051127756074817963378525 3769172908528056736266947)
                      ·
                        rfl

theorem cell23_7340438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_7340438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340438 prefixEnd_7340438 := by exact prefixLift 7340438
  have htrace : WordTrace (prefixWord ++ tailWord_7340438) baseStart_7340438 baseEnd_7340438 := by
    simpa [prefixWord, tailWord_7340438, baseEnd_7340438] using wordTrace_append hprefix tailTrace_7340438
  have hstable : (prefixWord ++ tailWord_7340438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340438).length < 2 ^ (prefixWord ++ tailWord_7340438).sum := by decide
  have hdescent : baseEnd_7340438 < baseStart_7340438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340450 : List Nat := [3, 3, 1, 2, 1, 1, 3, 4, 5]
def baseStart_7340450 : Nat := 118140960795 + 7340450 * 2 ^ 59
def prefixEnd_7340450 : Nat := 4983230072969 + 3 ^ 40 * 7340450 * 2
def baseEnd_7340450 : Nat := 418797674477323409924099

theorem tailTrace_7340450 : CollatzResearch.WordTrace tailWord_7340450 prefixEnd_7340450 418797674477323409924099 := by
  unfold tailWord_7340450
  simp only [CollatzResearch.WordTrace]
  refine ⟨66932051564202693474252701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178485470837873849264673869 66932051564202693474252701)
  ·
    refine ⟨25099519336576010052844763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66932051564202693474252701 25099519336576010052844763)
    ·
      refine ⟨37649279004864015079267145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25099519336576010052844763 37649279004864015079267145)
      ·
        refine ⟨28236959253648011309450359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37649279004864015079267145 28236959253648011309450359)
        ·
          refine ⟨42355438880472016964175539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28236959253648011309450359 42355438880472016964175539)
          ·
            refine ⟨63533158320708025446263309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42355438880472016964175539 63533158320708025446263309)
            ·
              refine ⟨23824934370265509542348741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63533158320708025446263309 23824934370265509542348741)
              ·
                refine ⟨4467175194424783039190389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23824934370265509542348741 4467175194424783039190389)
                ·
                  refine ⟨418797674477323409924099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4467175194424783039190389 418797674477323409924099)
                  ·
                    rfl

theorem cell23_7340450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 5].length) (baseStart_7340450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340450 prefixEnd_7340450 := by exact prefixLift 7340450
  have htrace : WordTrace (prefixWord ++ tailWord_7340450) baseStart_7340450 baseEnd_7340450 := by
    simpa [prefixWord, tailWord_7340450, baseEnd_7340450] using wordTrace_append hprefix tailTrace_7340450
  have hstable : (prefixWord ++ tailWord_7340450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340450).length < 2 ^ (prefixWord ++ tailWord_7340450).sum := by decide
  have hdescent : baseEnd_7340450 < baseStart_7340450 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7340453 : List Nat := [1, 3, 1, 2, 1, 1, 3, 1, 1, 7, 2]
def baseStart_7340453 : Nat := 118140960795 + 7340453 * 2 ^ 59
def prefixEnd_7340453 : Nat := 4983230072969 + 3 ^ 40 * 7340453 * 2
def baseEnd_7340453 : Nat := 3769180610737874177579377

theorem tailTrace_7340453 : CollatzResearch.WordTrace tailWord_7340453 prefixEnd_7340453 3769180610737874177579377 := by
  unfold tailWord_7340453
  simp only [CollatzResearch.WordTrace]
  refine ⟨267728315675799905409370013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178485543783866603606246675 267728315675799905409370013)
  ·
    refine ⟨100398118378424964528513755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267728315675799905409370013 100398118378424964528513755)
    ·
      refine ⟨150597177567637446792770633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100398118378424964528513755 150597177567637446792770633)
      ·
        refine ⟨112947883175728085094577975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150597177567637446792770633 112947883175728085094577975)
        ·
          refine ⟨169421824763592127641866963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112947883175728085094577975 169421824763592127641866963)
          ·
            refine ⟨254132737145388191462800445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169421824763592127641866963 254132737145388191462800445)
            ·
              refine ⟨95299776429520571798550167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 254132737145388191462800445 95299776429520571798550167)
              ·
                refine ⟨142949664644280857697825251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95299776429520571798550167 142949664644280857697825251)
                ·
                  refine ⟨214424496966421286546737877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142949664644280857697825251 214424496966421286546737877)
                  ·
                    refine ⟨5025574147650498903439169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 214424496966421286546737877 5025574147650498903439169)
                    ·
                      refine ⟨3769180610737874177579377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5025574147650498903439169 3769180610737874177579377)
                      ·
                        rfl

theorem cell23_7340453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 1, 1, 7, 2].length) (baseStart_7340453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7340453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7340453 prefixEnd_7340453 := by exact prefixLift 7340453
  have htrace : WordTrace (prefixWord ++ tailWord_7340453) baseStart_7340453 baseEnd_7340453 := by
    simpa [prefixWord, tailWord_7340453, baseEnd_7340453] using wordTrace_append hprefix tailTrace_7340453
  have hstable : (prefixWord ++ tailWord_7340453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7340453).length < 2 ^ (prefixWord ++ tailWord_7340453).sum := by decide
  have hdescent : baseEnd_7340453 < baseStart_7340453 := by decide
  rcases family_descends (prefixWord ++ tailWord_7340453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
